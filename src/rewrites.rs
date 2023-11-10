use egg::{rewrite, Applier, EGraph, Id, Language, Pattern, Rewrite, Subst, Var};

use crate::language::{
    self,
    ir::{Constant, Mio, MioAnalysis, MioAnalysisData},
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
/// `update_limit` is the maxium number of updates allowed in a stage for an action
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
                for elaboration in egraph[*elabs].nodes[0].children() {
                    // each elaboration
                    if MioAnalysis::write_set(egraph, *elaboration).is_disjoint(keys_read) {
                        if remained.len() == limit {
                            split.push(*elaboration);
                        } else {
                            // push to limit; maximize stage utilization
                            remained.push(*elaboration);
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
fn is_mapped(v: Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let eclass = subst[v];
        for node in egraph[eclass].nodes.iter() {
            match node {
                Mio::RelAlu(_) | Mio::ArithAlu(_) | Mio::SAlu(_) => return true,
                _ => (),
            }
        }
        return false;
    }
}

/// Check whether a matched e-class has been mapped to an ALU
/// and the computation is of depth 1
fn is_1_depth_mapped(v: Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let eclass = subst[v];
        for node in egraph[eclass].nodes.iter() {
            if match node {
                Mio::RelAlu(children) | Mio::SAlu(children) | Mio::ArithAlu(children) => {
                    children.iter().all(|c| {
                        for node in egraph[*c].nodes.iter() {
                            if node.is_leaf() {
                                return true;
                            }
                        }
                        return false;
                    })
                }
                _ => false,
            } {
                return true;
            }
        }
        return false;
    }
}

pub mod tofino_alus {

    use egg::{Id, Subst};

    use crate::language::ir::Mio;

    use super::{constains_leaf, is_mapped, rewrite, Var, EG, RW};

    pub mod stateless {
        use super::*;

        pub fn arith_to_alu() -> Vec<RW> {
            vec![
                rewrite!("add-to-alu-leaf"; "(+ ?x ?y)" => "(arith-alu alu-add ?x ?y)"
                    if constains_leaf("?x".parse().unwrap())
                    if constains_leaf("?y".parse().unwrap())),
                rewrite!("alu-add-tree";
                    "(+ (arith-alu ?op1 ?x1 ?y1) (arith-alu ?op2 ?x2 ?y2))" =>
                    "(arith-alu alu-add (arith-alu ?op1 ?x1 ?x2) (arith-alu ?op2 ?y1 ?y2))"),
                rewrite!("minus-to-alu-leaf"; "(- ?x ?y)" => "(arith-alu alu-sub ?x ?y)"
                    if constains_leaf("?x".parse().unwrap())
                    if constains_leaf("?y".parse().unwrap())),
                rewrite!("minus-to-alu-tree";
                    "(- (arith-alu ?op1 ?x1 ?y1) (arith-alu ?op2 ?x2 ?y2))" =>
                    "(arith-alu alu-sub (arith-alu ?op1 ?x1 ?x2) (arith-alu ?op2 ?y1 ?y2))"),
                rewrite!("ite-to-max"; "(ite (> ?x ?y) ?x ?y)" => "(arith-alu alu-max ?x ?y)"
                    if is_mapped("?x".parse().unwrap())
                    if is_mapped("?y".parse().unwrap())),
                rewrite!("ite-to-min"; "(ite (< ?x ?y) ?x ?y)" => "(arith-alu alu-min ?x ?y)"
                    if is_mapped("?x".parse().unwrap())
                    if is_mapped("?y".parse().unwrap())),
            ]
        }
    }

    pub mod stateful {
        use egg::Applier;

        use crate::{language::ir::MioAnalysis, rewrites::is_1_depth_mapped};

        use super::*;
        pub fn conditional_assignments() -> Vec<RW> {
            vec![
                rewrite!("cond-to-salu-lt";
                    "(ite (< ?lhs ?rhs) ?ib ?eb)" =>
                        "(stateful-alu (rel-alu alu-lt ?lhs ?rhs) ?ib ?eb)"
                        if is_1_depth_mapped("?lhs".parse().unwrap())
                        if is_1_depth_mapped("?rhs".parse().unwrap())
                        if is_mapped("?ib".parse().unwrap())
                        if is_mapped("?eb".parse().unwrap())),
                rewrite!("cond-to-salu-gt";
                    "(ite (> ?lhs ?rhs) ?ib ?eb)" =>
                        "(stateful-alu (rel-alu alu-gt ?lhs ?rhs) ?ib ?eb)"
                        if is_1_depth_mapped("?lhs".parse().unwrap())
                        if is_1_depth_mapped("?rhs".parse().unwrap())
                        if is_mapped("?ib".parse().unwrap())
                        if is_mapped("?eb".parse().unwrap())),
                rewrite!("cond-to-salu-le";
                    "(ite (<= ?lhs ?rhs) ?ib ?eb)" =>
                        "(stateful-alu (arith-alu alu-not (rel-alu alu-gt ?lhs ?rhs)) ?ib ?eb)"
                        if is_1_depth_mapped("?lhs".parse().unwrap())
                        if is_1_depth_mapped("?rhs".parse().unwrap())
                        if is_mapped("?ib".parse().unwrap())
                        if is_mapped("?eb".parse().unwrap())),
                rewrite!("cond-to-salu-ge";
                    "(ite (>= ?lhs ?rhs) ?ib ?eb)" =>
                        "(stateful-alu (arith-alu alu-not (rel-alu alu-lt ?lhs ?rhs)) ?ib ?eb)"
                        if is_1_depth_mapped("?lhs".parse().unwrap())
                        if is_1_depth_mapped("?rhs".parse().unwrap())
                        if is_mapped("?ib".parse().unwrap())
                        if is_mapped("?eb".parse().unwrap())),
            ]
        }
    }
}

mod test {
    use std::time::Duration;

    use egg::Runner;

    use crate::{language::transforms::tables_to_egraph, p4::example_progs};

    use super::{
        multi_stage_action, seq_elim, split_table,
        tofino_alus::{stateful::conditional_assignments, stateless::arith_to_alu},
    };

    #[test]
    fn test_tofino_rcp() {
        let prog = example_progs::rcp();
        let egraph = tables_to_egraph(vec![prog]);
        let rewrites = seq_elim()
            .into_iter()
            .chain(split_table(1).into_iter())
            .chain(arith_to_alu().into_iter())
            .chain(multi_stage_action(2).into_iter())
            .chain(conditional_assignments().into_iter())
            .collect::<Vec<_>>();
        let runner = Runner::default()
            .with_egraph(egraph)
            .with_node_limit(5_000)
            .with_time_limit(Duration::from_secs(10));
        let runner = runner.run(rewrites.iter());
        runner.egraph.dot().to_pdf("rcp.pdf").unwrap();
    }
}
