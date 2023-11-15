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
            let evar = if elaborations.len() > 0 {
                elaborations
                    .iter()
                    .filter(|x| x.contains("global."))
                    .next()
                    .unwrap()
                    .clone()
            } else {
                "tmp".to_string()
            };
            let var_id = egraph.add(Mio::Symbol(evar));
            let operands = self.operands.iter().map(|v| subst[*v]).collect::<Vec<_>>();
            // TODO: Notice that we are not enforcing depth limit to the operands.
            // We will need to limit it because it cannot have unbounded depth
            // e.g. Intel Tofino can only do depth 2
            let stateful_alu = egraph.add(Mio::SAlu(
                vec![ops_id, var_id]
                    .into_iter()
                    .chain(operands.into_iter())
                    .collect(),
            ));
            egraph.union(eclass, stateful_alu);
            vec![eclass, stateful_alu]
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
        use egg::{Applier, Language, Pattern, Searcher};

        use crate::{
            language::ir::{MioAnalysis, MioAnalysisData},
            rewrites::{is_n_depth_mapped, none_global, AluApplier},
        };

        use super::*;

        pub fn lift_stateless() -> Vec<RW> {
            // If the elaboration of some computation is a global variable,
            // and the computation requires reading that global variable, e.g. global.x = global.x + (meta.y + meta.z)
            // then we could lift (meta.y + meta.z) to a previous stage
            // When such computation has a depth >= 2, we must lift it to a previous stage, otherwise we cannot compile it.
            struct StatelessLiftApplier(Var, Var);
            impl Applier<Mio, MioAnalysis> for StatelessLiftApplier {
                fn apply_one(
                    &self,
                    egraph: &mut egg::EGraph<Mio, MioAnalysis>,
                    eclass: Id,
                    subst: &Subst,
                    searcher_ast: Option<&egg::PatternAst<Mio>>,
                    rule_name: egg::Symbol,
                ) -> Vec<Id> {
                    // First check whether in each action there is an elaboration that involves
                    // both reading and writing to a global variable
                    let keys = subst[self.0];
                    let action_wrapper_id = subst[self.1];
                    let mut lhs_action_elabs = vec![];
                    let mut rhs_action_elabs = vec![];
                    let mut changed: Vec<Id> = vec![];
                    // copy to avoid holding mut and immut references
                    for action_wrapper in egraph[action_wrapper_id]
                        .nodes
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                    {
                        for &elab_wrapper_id in action_wrapper.children() {
                            for elab_node in egraph[elab_wrapper_id]
                                .nodes
                                .iter()
                                .cloned()
                                .collect::<Vec<_>>()
                            {
                                let mut remain = vec![];
                                let mut lifted = vec![];
                                for &action_elaborations in elab_node.children() {
                                    let elaborations =
                                        MioAnalysis::elaborations(egraph, action_elaborations);
                                    let read_set =
                                        MioAnalysis::read_set(egraph, action_elaborations);
                                    if elaborations.intersection(read_set).next().is_none() {
                                        // no read-write global variable
                                        continue;
                                    }
                                    // we will need to check whether this elaboration has a match in the form of
                                    // (?op ?x ?y) where ?x or ?y is a global variable
                                    for op in ["+", "-"] {
                                        let pattern_l =
                                            format!("({} (arith-alu alu-global ?x) ?y)", op)
                                                .parse::<Pattern<Mio>>()
                                                .unwrap();
                                        let pattern_r =
                                            format!("({} ?y (arith-alu alu-global ?x))", op)
                                                .parse::<Pattern<Mio>>()
                                                .unwrap();
                                        egraph.rebuild();
                                        let search_left =
                                            pattern_l.search_eclass(egraph, action_elaborations);
                                        let search_right =
                                            pattern_r.search_eclass(egraph, action_elaborations);
                                        let hit_left = search_left.is_some();
                                        if let Some(matches) = search_left.or(search_right) {
                                            // split ?y to some previous stage and replace with a new PHV field
                                            let new_subst = &matches.substs[0];
                                            let pattern_var = "?y".parse().unwrap();
                                            if is_n_depth_mapped(pattern_var, 1, Some(false))(
                                                egraph,
                                                new_subst[pattern_var],
                                                new_subst,
                                            ) {
                                                // if it is at most depth 1 computation on stateless alu, we don't need to lift it
                                                remain.push(action_elaborations);
                                                continue;
                                            }
                                            if !is_mapped(pattern_var, Some(false))(
                                                egraph,
                                                action_elaborations,
                                                new_subst,
                                            ) {
                                                // if it is not mapped to stateless alus, we can't lift it
                                                remain.push(action_elaborations);
                                                continue;
                                            }
                                            let to_lift = new_subst[pattern_var];
                                            let binding = egraph
                                                .analysis
                                                .new_var(MioAnalysis::get_type(egraph, to_lift));
                                            let _binding_id =
                                                egraph.add(Mio::Symbol(binding.clone()));
                                            // remaining computation should be (op ?x ?binding) / (op ?binding ?x)
                                            let pattern_str = if hit_left {
                                                format!(
                                                    "({} (arith-alu alu-global ?x) ?binding)",
                                                    op
                                                )
                                            } else {
                                                format!(
                                                    "({} ?binding (arith-alu alu-global ?x))",
                                                    op
                                                )
                                            };
                                            let new_pattern =
                                                pattern_str.parse::<Pattern<Mio>>().unwrap();
                                            let new_action_elaborations = new_pattern.apply_one(
                                                egraph,
                                                action_elaborations,
                                                new_subst,
                                                searcher_ast,
                                                rule_name,
                                            );
                                            changed.extend(new_action_elaborations.iter());
                                            remain.push(new_action_elaborations[0]);
                                            lifted.push((to_lift, binding));
                                        } else {
                                            remain.push(action_elaborations);
                                        }
                                    }
                                }
                                if lifted.len() > 0 {
                                    lhs_action_elabs.push(lifted);
                                }
                                if remain.len() > 0 {
                                    rhs_action_elabs.push(remain);
                                }
                            }
                            break;
                        }
                    }
                    if lhs_action_elabs.len() == 0 {
                        vec![]
                    } else {
                        // construct new table
                        for lhs_action_elab in lhs_action_elabs.iter() {
                            for (to_lift, binding) in lhs_action_elab {
                                match &mut egraph[*to_lift].data {
                                    MioAnalysisData::Action(u) => {
                                        u.elaborations.insert(binding.clone())
                                    }
                                    _ => panic!("not an action"),
                                };
                            }
                        }
                        let elab_ids = lhs_action_elabs
                            .iter()
                            .map(|v| {
                                egraph.add(Mio::Elaborations(v.iter().map(|(id, _)| *id).collect()))
                            })
                            .collect();
                        let action_id = egraph.add(Mio::Actions(elab_ids));
                        let lhs_table_id = egraph.add(Mio::GIte([keys, action_id]));
                        let elab_ids = rhs_action_elabs
                            .iter()
                            .map(|v| {
                                egraph.add(Mio::Elaborations(v.iter().map(|id| *id).collect()))
                            })
                            .collect();
                        let action_id = egraph.add(Mio::Actions(elab_ids));
                        let rhs_table_id = egraph.add(Mio::GIte([keys, action_id]));
                        let seq_id = egraph.add(Mio::Seq([lhs_table_id, rhs_table_id]));
                        vec![seq_id]
                            .into_iter()
                            .chain(changed.into_iter())
                            .collect()
                    }
                }
            }
            vec![rewrite!("lift-comp";
                    "(gite ?keys ?actions)" =>
                    {  StatelessLiftApplier("?keys".parse().unwrap(), "?actions".parse().unwrap()) })]
        }

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
            language::ir::{ArithAluOps, MioAnalysis, MioAnalysisData},
            rewrites::{is_n_depth_mapped, same_elaboration},
        };

        use super::*;
        pub fn conditional_assignments() -> Vec<RW> {
            struct TofinoStatefulAluApplier {
                alu_type: &'static str,
                alu_op: &'static str,
                operands: Vec<Var>,
            }
            impl TofinoStatefulAluApplier {
                fn new(
                    alu_type: &'static str,
                    alu_op: &'static str,
                    operands: Vec<&'static str>,
                ) -> Self {
                    Self {
                        alu_type,
                        alu_op,
                        operands: operands.into_iter().map(|s| s.parse().unwrap()).collect(),
                    }
                }
            }
            impl Applier<Mio, MioAnalysis> for TofinoStatefulAluApplier {
                fn apply_one(
                    &self,
                    egraph: &mut egg::EGraph<Mio, MioAnalysis>,
                    eclass: Id,
                    subst: &Subst,
                    searcher_ast: Option<&egg::PatternAst<Mio>>,
                    rule_name: egg::Symbol,
                ) -> Vec<Id> {
                    let elaborations = match &egraph[eclass].data {
                        MioAnalysisData::Action(u) => u.elaborations.clone(),
                        _ => panic!("not an action"),
                    };
                    assert!(
                        elaborations.len() <= 1,
                        "conditional assignments should have at most one elaboration"
                    );
                    let elab_var = if elaborations.len() == 0 {
                        "tmp".to_string()
                    } else {
                        elaborations.iter().cloned().next().unwrap()
                    };
                    let read_set = MioAnalysis::read_set(egraph, eclass).clone();
                    let write_set = MioAnalysis::write_set(egraph, eclass).clone();
                    let elaborations = MioAnalysis::elaborations(egraph, eclass).clone();
                    let alu_op_id = egraph.add(if self.alu_type == "arith-alu" {
                        Mio::ArithAluOps(self.alu_op.parse().unwrap())
                    } else {
                        Mio::RelAluOps(self.alu_op.parse().unwrap())
                    });
                    let operands = self.operands.iter().map(|v| subst[*v]).collect::<Vec<_>>();
                    let elab_id = egraph.add(Mio::Symbol(elab_var.clone()));
                    let salu_id = egraph.add(Mio::SAlu(
                        vec![alu_op_id, elab_id]
                            .into_iter()
                            .chain(operands.iter().cloned())
                            .collect(),
                    ));
                    match &mut egraph[salu_id].data {
                        MioAnalysisData::Action(u) => {
                            u.reads = read_set;
                            u.writes = write_set;
                            u.elaborations = elaborations;
                        }
                        _ => (),
                    }
                    let f = egraph.union(salu_id, eclass);
                    if f {
                        vec![eclass, salu_id]
                    } else {
                        vec![]
                    }
                }
            }
            vec![rewrite!("cond-assign-to-salu";
                    "(ite ?rel ?lhs ?rhs)" =>
                    { TofinoStatefulAluApplier::new("arith-alu", "alu-ite", vec!["?rel", "?lhs", "?rhs"]) }
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

    use egg::{Extractor, Runner};

    use crate::{
        extractors::GreedyExtractor,
        language::transforms::tables_to_egraph,
        p4::{example_progs, p4ir::Table},
    };

    use super::{
        multi_stage_action, seq_elim, split_table,
        tofino_alus::{
            stateful::conditional_assignments,
            stateless::{arith_to_alu, cmp_to_rel, lift_stateless},
        },
    };

    fn test_tofino_mapping(prog: Vec<Table>, filename: &'static str) {
        let (egraph, root) = tables_to_egraph(prog);
        let rewrites = seq_elim()
            .into_iter()
            // .chain(split_table(1).into_iter())
            .chain(arith_to_alu().into_iter())
            .chain(multi_stage_action(2).into_iter())
            .chain(conditional_assignments().into_iter())
            .chain(cmp_to_rel().into_iter())
            .chain(lift_stateless())
            .collect::<Vec<_>>();
        let runner = Runner::default()
            .with_egraph(egraph)
            .with_node_limit(5_000)
            .with_time_limit(Duration::from_secs(10));
        let runner = runner.run(rewrites.iter());
        runner.egraph.dot().to_pdf(filename).unwrap();
        let greedy_ext = GreedyExtractor {};
        let extractor = Extractor::new(&runner.egraph, greedy_ext);
        let (best_cost, best) = extractor.find_best(root);
        println!("best cost: {}", best_cost);
        println!("best: {}", best.pretty(80));
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
