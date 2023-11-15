use egg::{rewrite, Applier, EGraph, Id, Language, Pattern, Rewrite, Searcher, Subst, Var};

use crate::language::{
    self,
    ir::{ArithAluOps, Constant, Mio, MioAnalysis, MioAnalysisData},
    utils::{get_dependency, Dependency},
};

type RW = Rewrite<language::ir::Mio, language::ir::MioAnalysis>;
type EG = EGraph<Mio, MioAnalysis>;

fn constains_leaf(v: Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let eclass = subst[v];
        for node in egraph[eclass].nodes.iter() {
            if node.is_leaf() {
                return true;
            }
        }
        return false;
    }
}

fn none_global(v: Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let eclass = subst[v];
        match &egraph[eclass].data {
            MioAnalysisData::Action(u) => {
                for elaborated in u.elaborations.iter() {
                    if elaborated.contains("global.") {
                        return false;
                    }
                }
            }
            _ => (),
        }
        return true;
    }
}

fn same_elaboration(v1: Var, v2: Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let eclass1 = subst[v1];
        let eclass2 = subst[v2];
        let elaborations1 = MioAnalysis::elaborations(egraph, eclass1);
        let elaborations2 = MioAnalysis::elaborations(egraph, eclass2);
        return elaborations1 == elaborations2;
    }
}

fn independent_actions(a1s: Var, a2s: Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let c1 = subst[a1s];
        let c2 = subst[a2s];
        return get_dependency(
            &MioAnalysis::read_set(egraph, c1),
            &MioAnalysis::write_set(egraph, c1),
            &MioAnalysis::read_set(egraph, c2),
            &MioAnalysis::write_set(egraph, c2),
        ) == Dependency::INDEPENDENT;
    }
}

fn is_greater_eq(v1: Var, val: i32) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let c1 = subst[v1];
        return match &MioAnalysis::get_constant(egraph, c1) {
            Some(Constant::Int(c1)) => *c1 >= val,
            _ => false,
        };
    }
}

pub fn seq_elim() -> Vec<RW> {
    // work together with table splitting
    return vec![rewrite!("seq-normalization";
            "(seq (seq ?t1 ?t2) ?t3)" => "(seq ?t1 (seq ?t2 ?t3))")];
}

pub fn parallelize_independent_tables() -> Vec<RW> {
    return vec![
        rewrite!(
            "parallelize-table-adj";
            "(seq (gite ?k1s ?a1s) (gite ?k2s ?a2s))" =>
            "(join (gite ?k1s ?a1s) (gite ?k2s ?a2s))"
            if independent_actions("?a1s".parse().unwrap(), "?a2s".parse().unwrap())
        ),
        rewrite!(
            "parallelize-table-left";
            "(seq (gite ?k1s ?a1s) (seq (gite ?k2s ?a2s) ?t3))" =>
            "(seq (join (gite ?k1s ?a1s) (gite ?k2s ?a2s)) ?t3)"
            if independent_actions("?a1s".parse().unwrap(), "?a2s".parse().unwrap())
        ),
    ];
}

pub fn comm_independent_tables() -> Vec<RW> {
    return vec![
        rewrite!("comm-tables-adj";
            "(seq (gite ?k1s ?a1s) (gite ?k2s ?a2s))" =>
            "(seq (gite ?k2s ?a2s) (gite ?k1s ?a1s))"
            if independent_actions("?a1s".parse().unwrap(), "?a2s".parse().unwrap())
        ),
        rewrite!("comm-tables-left";
            "(seq (gite ?k1s ?a1s) (seq (gite ?k2s ?a2s) ?t3))" =>
            "(seq (gite ?k2s ?a2s) (seq (gite ?k1s ?a1s) ?t3))"
            if independent_actions("?a1s".parse().unwrap(), "?a2s".parse().unwrap())
        ),
    ];
}

/// Split actions to two tables (if applicable)
/// T -> T1; T2
/// Guarantees that T1 actions do not modify the keys
pub fn split_table(n: usize) -> Vec<RW> {
    struct SplitApplier(Var, Var, usize);
    impl Applier<Mio, MioAnalysis> for SplitApplier {
        fn apply_one(
            &self,
            egraph: &mut EGraph<Mio, MioAnalysis>,
            eclass: Id,
            subst: &Subst,
            _searcher_ast: Option<&egg::PatternAst<Mio>>,
            _rule_name: egg::Symbol,
        ) -> Vec<Id> {
            let k1s = subst[self.0];
            let a1s = subst[self.1];
            let key_reads = MioAnalysis::read_set(egraph, k1s);
            // the remaining actions must not modify the keys
            // split out at most n actions a time
            let mut remained = vec![];
            let mut split = vec![];
            let split_bound = self.2;
            let mut index = 0;
            for a in egraph[a1s].nodes[0].children() {
                if MioAnalysis::write_set(egraph, *a).is_disjoint(&key_reads) {
                    if remained.len() == split_bound {
                        split.push(index);
                    } else {
                        remained.push(index);
                    }
                } else {
                    split.push(index);
                }
                index += 1;
            }
            if split.len() == 0 || remained.len() == 0 {
                return vec![];
            }
            debug_assert!(split.len() + remained.len() == index);
            debug_assert!(split.len() <= split_bound);

            let actions = egraph[a1s].nodes[0].children().to_vec();
            let remaining_actions = remained.iter().map(|i| actions[*i]).collect::<Vec<_>>();
            let split_actions = split.iter().map(|i| actions[*i]).collect::<Vec<_>>();
            let lhs_action_id = egraph.add(Mio::Actions(remaining_actions));
            let rhs_action_id = egraph.add(Mio::Actions(split_actions));
            let lhs_table = egraph.add(Mio::GIte([k1s, lhs_action_id]));
            let rhs_table = egraph.add(Mio::GIte([k1s, rhs_action_id]));
            // (seq (gite ?k1s ?remaining) (gite ?k1s ?split))
            let seq_id: Id = egraph.add(Mio::Seq([lhs_table, rhs_table]));
            egraph.union(eclass, seq_id);
            // TODO: propagate elaboration?
            vec![eclass, seq_id]
        }
    }
    return vec![rewrite!("separate-action";
            "(gite ?k1s ?a1s)" => { SplitApplier("?k1s".parse().unwrap(), "?a1s".parse().unwrap(), n) })];
}

/// Span actions across stages
/// `update_limit` is the maxium number of global updates allowed in a stage for an action
/// Also need to guarantee that actions kept in the table do not modify the keys
pub fn multi_stage_action(update_limit: usize) -> Vec<RW> {
    struct MultiStagedApplier(Var, Var, usize);
    impl Applier<Mio, MioAnalysis> for MultiStagedApplier {
        fn apply_one(
            &self,
            egraph: &mut EGraph<Mio, MioAnalysis>,
            eclass: Id,
            subst: &Subst,
            _searcher_ast: Option<&egg::PatternAst<Mio>>,
            _rule_name: egg::Symbol,
        ) -> Vec<Id> {
            let kid = subst[self.0];
            let aid = subst[self.1];
            let limit = self.2;
            let keys_read = MioAnalysis::read_set(egraph, kid);
            // stores a vector of elaborations (Vec<Id>)
            let mut remained_updates = vec![];
            let mut splitted_updates = vec![];
            for elabs in egraph[aid].nodes[0].children() {
                let mut remained = vec![];
                let mut split = vec![];
                let mut num_global_writes = 0;
                for elaboration in egraph[*elabs].nodes[0].children() {
                    // each elaboration
                    if MioAnalysis::write_set(egraph, *elaboration).is_disjoint(keys_read) {
                        match &egraph[*elaboration].data {
                            MioAnalysisData::Action(u) => {
                                if u.elaborations.iter().any(|x| x.contains("global.")) {
                                    if num_global_writes == limit {
                                        split.push(*elaboration);
                                    } else {
                                        num_global_writes += 1;
                                        remained.push(*elaboration);
                                    }
                                }
                            }
                            _ => remained.push(*elaboration),
                        }
                    } else {
                        split.push(*elaboration);
                    }
                }
                if remained.len() == 0 || split.len() == 0 {
                    continue;
                }
                remained_updates.push(remained);
                splitted_updates.push(split);
            }
            if remained_updates.len() == 0 || splitted_updates.len() == 0 {
                return vec![];
            }
            let lhs_table_elaborations = remained_updates
                .into_iter()
                .map(|v| egraph.add(Mio::Elaborations(v)))
                .collect::<Vec<_>>();
            let rhs_table_elaborations = splitted_updates
                .into_iter()
                .map(|v| egraph.add(Mio::Elaborations(v)))
                .collect::<Vec<_>>();
            let lhs_table_actions = egraph.add(Mio::Actions(lhs_table_elaborations));
            let rhs_table_actions = egraph.add(Mio::Actions(rhs_table_elaborations));
            let lhs_table = egraph.add(Mio::GIte([kid, lhs_table_actions]));
            let rhs_table = egraph.add(Mio::GIte([kid, rhs_table_actions]));
            let seq_id = egraph.add(Mio::Seq([lhs_table, rhs_table]));
            egraph.union(eclass, seq_id);
            vec![eclass, seq_id]
        }
    }
    return vec![rewrite!(
            "multi-staged-action";
            "(gite ?k ?a)" => 
            { MultiStagedApplier("?k".parse().unwrap(), "?a".parse().unwrap(), update_limit) })];
}

pub fn ite_to_gite() -> Vec<RW> {
    vec![rewrite!("ite-to-gite"; "(ite ?c ?t1 ?t2)" => "(gite (keys ?c1) (actions ?t1 ?t2))")]
}

pub fn alg_simpl() -> Vec<RW> {
    vec![
        rewrite!("add-sub-convert"; "(+ ?x (neg ?y))" => "(- ?x ?y)"),
        rewrite!("sub-neg-convert"; "(- 0 ?x)" => "(neg ?x)"),
        rewrite!("add-sub-elim"; "(- (+ ?x ?y) ?y)" => "?x"),
        rewrite!("sub-conv"; "(- ?x (- ?y ?z))" => "(+ (- ?x ?y) ?z)"),
        rewrite!("add-conv"; "(+ ?x (- ?y ?z))" => "(- (+ ?x ?y) ?z)"),
        rewrite!("add-zero"; "(+ ?x 0)" => "?x"),
        rewrite!("sub-zero"; "(- ?x 0)" => "?x"),
        rewrite!("double-to-shift"; "(+ ?x ?x)" => "(bitshl ?x 1)"),
        rewrite!("shl-shr-elim"; "(bitshr (bitshl ?x ?y) ?y)" => "?x"),
        rewrite!("shl-sum"; "(bitshl ?x (+ ?y ?z)" => "(bitshl (bitshl ?x ?y) ?z)"),
        rewrite!("shr-to-zero"; "(bitshr ?x ?y)" => "0" if is_greater_eq("?y".parse().unwrap(), 32)),
        rewrite!("sub-elim"; "(- ?x ?x)" => "0"),
        rewrite!("add-comm"; "(+ ?x ?y)" => "(+ ?y ?x)"),
        rewrite!("add-assoc"; "(+ ?x (+ ?y ?z))" => "(+ (+ ?x ?y) ?z)"),
    ]
}

pub fn predicate_rewrites() -> Vec<RW> {
    vec![
        rewrite!("and-elim-left"; "(land ?x false)" => "false"),
        rewrite!("and-elim-right"; "(land ?x true)" => "?x"),
        rewrite!("and-comm"; "(land ?x ?y)" => "(land ?y ?x)"),
        rewrite!("and-assoc"; "(land ?x (land ?y ?z))" => "(land (land ?x ?y) ?z)"),
        rewrite!("ite-collapse"; "(ite ?c1 ?t3 (ite ?c2 ?t1 ?t2))" => "(ite ?c1 ?t3 ?t1)"), // iff c1 <=> not c2
        rewrite!("ite-true"; "(ite true ?t1 ?t2)" => "?t1"),
        rewrite!("ite-false"; "(ite false ?t1 ?t2)" => "?t2"),
        rewrite!("ite-same"; "(ite ?c ?t ?t)" => "?t"),
    ]
}

/// Check whether a matched e-class has been mapped to an ALU
fn is_mapped(v: Var, stateful: Option<bool>) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let eclass = subst[v];
        for node in egraph[eclass].nodes.iter() {
            if let Some(stateful) = stateful {
                if stateful {
                    match node {
                        Mio::SAlu(_) | Mio::Symbol(_) | Mio::Constant(_) => return true,
                        _ => (),
                    }
                } else {
                    match node {
                        Mio::RelAlu(_) | Mio::ArithAlu(_) | Mio::Symbol(_) | Mio::Constant(_) => {
                            return true
                        }
                        _ => (),
                    }
                }
            } else {
                match node {
                    Mio::RelAlu(_)
                    | Mio::ArithAlu(_)
                    | Mio::SAlu(_)
                    | Mio::Symbol(_)
                    | Mio::Constant(_) => return true,
                    _ => (),
                }
            }
        }
        return false;
    }
}

/// Check whether a matched e-class has been mapped to an ALU
/// and the computation is of at most depth n
fn is_n_depth_mapped(
    v: Var,
    n: usize,
    stateful: Option<bool>,
) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    fn check_level(egraph: &EG, id: Id, level: usize, stateful: Option<bool>) -> bool {
        for node in egraph[id].nodes.iter() {
            if let Some(stateful) = stateful {
                if stateful {
                    if match node {
                        Mio::SAlu(children) => children
                            .iter()
                            .all(|c| egraph[*c].nodes.iter().any(|n| n.is_leaf())),
                        Mio::Symbol(_) => true,
                        _ => false,
                    } {
                        return true;
                    }
                } else {
                    if match node {
                        Mio::RelAlu(children) | Mio::ArithAlu(children) => children
                            .iter()
                            .all(|c| egraph[*c].nodes.iter().any(|n| n.is_leaf())),
                        Mio::Symbol(_) => true,
                        _ => false,
                    } {
                        return true;
                    }
                }
            } else {
                if match node {
                    Mio::RelAlu(children) | Mio::SAlu(children) | Mio::ArithAlu(children) => {
                        children
                            .iter()
                            .all(|c| egraph[*c].nodes.iter().any(|n| n.is_leaf()))
                    }
                    Mio::Symbol(_) => true,
                    _ => false,
                } {
                    return true;
                }
            }
        }
        if level == 0 {
            return false;
        }
        for node in egraph[id].nodes.iter() {
            if let Some(stateful_b) = stateful {
                if stateful_b {
                    if match node {
                        Mio::SAlu(children) => children
                            .iter()
                            .any(|c| check_level(egraph, *c, level - 1, stateful)),
                        _ => false,
                    } {
                        return true;
                    }
                } else {
                    if match node {
                        Mio::RelAlu(children) | Mio::ArithAlu(children) => children
                            .iter()
                            .any(|c| check_level(egraph, *c, level - 1, stateful)),
                        _ => false,
                    } {
                        return true;
                    }
                }
            } else {
                if match node {
                    Mio::RelAlu(children) | Mio::SAlu(children) | Mio::ArithAlu(children) => {
                        children
                            .iter()
                            .any(|c| check_level(egraph, *c, level - 1, stateful))
                    }
                    _ => false,
                } {
                    return true;
                }
            }
        }
        return false;
    }
    move |egraph, _id, subst| {
        let eclass = subst[v];
        return check_level(egraph, eclass, n, stateful);
    }
}

struct AluApplier {
    alu_type: &'static str,
    alu_op: &'static str,
    operands: Vec<Var>,
}

impl AluApplier {
    fn new(alu_type: &'static str, alu_op: &'static str, operands: Vec<&'static str>) -> Self {
        Self {
            alu_type,
            alu_op,
            operands: operands.into_iter().map(|s| s.parse().unwrap()).collect(),
        }
    }
}

impl Applier<Mio, MioAnalysis> for AluApplier {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<Mio, MioAnalysis>,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&egg::PatternAst<Mio>>,
        rule_name: egg::Symbol,
    ) -> Vec<Id> {
        let (elaborations, reads) = match &egraph[eclass].data {
            MioAnalysisData::Action(u) => (u.elaborations.clone(), u.reads.clone()),
            _ => panic!("not an action"),
        };
        if elaborations
            .iter()
            .chain(reads.iter())
            .any(|x| x.contains("global."))
        {
            let ops_id = egraph.add(if self.alu_type == "arith-alu" {
                Mio::ArithAluOps(self.alu_op.parse().unwrap())
            } else {
                Mio::RelAluOps(self.alu_op.parse().unwrap())
            });
            let operands = self.operands.iter().map(|v| subst[*v]).collect::<Vec<_>>();
            let global_update_action = egraph.add(Mio::ArithAlu(
                vec![ops_id]
                    .into_iter()
                    .chain(operands.into_iter())
                    .collect(),
            ));
            match &mut egraph[global_update_action].data {
                MioAnalysisData::Action(u) => u.elaborations = elaborations,
                _ => panic!("not an action when converting to a statefu alu"),
            }
            let stateful_alu = egraph.add(Mio::SAlu(vec![global_update_action]));
            egraph.union(eclass, stateful_alu);
            vec![eclass, global_update_action, stateful_alu]
        } else {
            let pattern = format!(
                "({} {} {})",
                self.alu_type,
                self.alu_op,
                self.operands
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            );
            let pattern = pattern.parse::<Pattern<Mio>>().unwrap();
            pattern.apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        }
    }
}

pub mod tofino_alus {

    use egg::{Id, Subst};

    use crate::language::ir::Mio;

    use super::{constains_leaf, is_mapped, rewrite, Var, EG, RW};

    pub mod stateless {
        use egg::{Applier, Pattern};

        use crate::{
            language::ir::{MioAnalysis, MioAnalysisData},
            rewrites::{none_global, AluApplier},
        };

        use super::*;

        pub fn arith_to_alu() -> Vec<RW> {
            vec![
                rewrite!("add-to-alu"; "(+ ?x ?y)" => { AluApplier::new("arith-alu", "alu-add", vec!["?x", "?y"]) }
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("minus-to-alu"; "(- ?x ?y)" => { AluApplier::new("arith-alu", "alu-sub", vec!["?x", "?y"]) }
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("ite-to-max"; "(ite (> ?x ?y) ?x ?y)" => { AluApplier::new("arith-alu", "alu-max", vec!["?x", "?y"]) }
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("ite-to-min"; "(ite (< ?x ?y) ?x ?y)" => { AluApplier::new("arith-min", "alu-add", vec!["?x", "?y"]) }
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
            ]
        }

        pub fn cmp_to_rel() -> Vec<RW> {
            vec![
                rewrite!("gt-to-rel"; "(> ?x ?y)" => "(rel-alu alu-gt ?x ?y)"
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("lt-to-rel"; "(< ?x ?y)" => "(rel-alu alu-lt ?x ?y)"
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("eq-to-rel"; "(= ?x ?y)" => "(rel-alu alu-eq ?x ?y)"
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("neq-to-rel"; "(!= ?x ?y)" => "(rel-alu alu-neq ?x ?y)"
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("ge-to-rel"; "(>= ?x ?y)" => "(rel-alu alu-not (rel-alu alu-lt ?x ?y))"
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("le-to-rel"; "(<= ?x ?y)" => "(rel-alu alu-not (rel-alu alu-gt ?x ?y))"
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
            ]
        }
    }

    pub mod stateful {
        use std::collections::{HashMap, HashSet};

        use egg::{Applier, Pattern};

        use crate::{
            language::ir::{ArithAluOps, MioAnalysis},
            rewrites::{is_n_depth_mapped, same_elaboration},
        };

        use super::*;
        pub fn conditional_assignments() -> Vec<RW> {
            vec![rewrite!("cond-assign-to-salu";
                    "(ite ?rel ?lhs ?rhs)" =>
                    "(stateful-alu (ite ?rel ?lhs ?rhs))"
                if is_n_depth_mapped("?rel".parse().unwrap(), 2, None)
                if is_n_depth_mapped("?lhs".parse().unwrap(), 1, None)
                if is_n_depth_mapped("?rhs".parse().unwrap(), 1, None))]
        }
    }
}

pub mod banzai_alu {
    pub mod stateless {
        use egg::rewrite;

        use crate::rewrites::{is_mapped, AluApplier, RW};

        pub fn arith_to_alu() -> Vec<RW> {
            // https://github.com/CaT-mindepth/minDepthCompiler/blob/weighted-grammar-parallel-final/src/grammars/stateless_domino/stateless_new.sk
            vec![
                rewrite!("domino-add";
                    "(+ ?x ?y)" => { AluApplier::new("arith-alu", "alu-add", vec!["?x", "?y"]) }
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("domino-sub";
                    "(- ?x ?y)" => { AluApplier::new("arith-alu", "alu-sub", vec!["?x", "?y"]) }
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("domino-neq";
                    "(!= ?x ?y)" => { AluApplier::new("rel-alu", "alu-neq", vec!["?x", "?y"]) }
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("domino-neq";
                    "(= ?x ?y)" => { AluApplier::new("rel-alu", "alu-eq", vec!["?x", "?y"]) }
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("domino-geq";
                    "(>= ?x ?y)" => { AluApplier::new("rel-alu", "alu-ge", vec!["?x", "?y"]) }
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
                rewrite!("domino-lt";
                    "(< ?x ?y)" => { AluApplier::new("rel-alu", "alu-lt", vec!["?x", "?y"]) }
                    if is_mapped("?x".parse().unwrap(), None)
                    if is_mapped("?y".parse().unwrap(), None)),
            ]
        }
    }
}

mod test {
    use std::time::Duration;

    use egg::Runner;

    use crate::{
        language::transforms::tables_to_egraph,
        p4::{example_progs, p4ir::Table},
    };

    use super::{
        multi_stage_action, seq_elim, split_table,
        tofino_alus::{
            stateful::conditional_assignments,
            stateless::{arith_to_alu, cmp_to_rel},
        },
    };

    fn test_tofino_mapping(prog: Vec<Table>, filename: &'static str) {
        let egraph = tables_to_egraph(prog);
        let rewrites = seq_elim()
            .into_iter()
            // .chain(split_table(1).into_iter())
            .chain(arith_to_alu().into_iter())
            .chain(multi_stage_action(2).into_iter())
            .chain(conditional_assignments().into_iter())
            .chain(cmp_to_rel().into_iter())
            .collect::<Vec<_>>();
        let runner = Runner::default()
            .with_egraph(egraph)
            .with_node_limit(5_000)
            .with_time_limit(Duration::from_secs(10));
        let runner = runner.run(rewrites.iter());
        runner.egraph.dot().to_pdf(filename).unwrap();
    }

    #[test]
    fn test_tofino_rcp() {
        test_tofino_mapping(example_progs::rcp(), "rcp.pdf");
    }

    #[test]
    fn test_tofino_sampling() {
        test_tofino_mapping(example_progs::sampling(), "sampling.pdf");
    }

    #[test]
    fn test_tofino_blue_increase() {
        test_tofino_mapping(example_progs::blue_increase(), "blue_increase.pdf");
    }
}
