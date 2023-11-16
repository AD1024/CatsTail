use egg::{Id, Subst};

use crate::language::ir::Mio;

use super::{is_mapped, RW};

pub mod stateless {
    use egg::{rewrite, Applier, Language, Pattern, Searcher, Var};

    use crate::{
        language::ir::{MioAnalysis, MioAnalysisData},
        rewrites::{is_n_depth_mapped, AluApplier},
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
                                let read_set = MioAnalysis::read_set(egraph, action_elaborations);
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
                                        // remaining computation should be (op ?x ?binding) / (op ?binding ?x)
                                        let pattern_str = if hit_left {
                                            format!(
                                                "({} (arith-alu alu-global ?x) {})",
                                                op, binding
                                            )
                                        } else {
                                            format!(
                                                "({} {} (arith-alu alu-global ?x))",
                                                op, binding
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
                        .map(|v| egraph.add(Mio::Elaborations(v.iter().map(|id| *id).collect())))
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

    use egg::{rewrite, Applier, Pattern, Var};

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
