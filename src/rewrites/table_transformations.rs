use std::collections::{HashMap, HashSet};

use egg::{rewrite, Applier};

use super::*;

pub fn seq_elim() -> Vec<RW> {
    // work together with table splitting
    return vec![rewrite!("seq-normalization";
            "(seq (seq ?t1 ?t2) ?t3)" => "(seq ?t1 (seq ?t2 ?t3))")];
}

pub fn waw_elim() -> Vec<RW> {
    struct WAWElimApplier {
        k1: Var,
        k2: Var,
        a1: Var,
        a2: Var,
    }
    impl Applier<Mio, MioAnalysis> for WAWElimApplier {
        fn apply_one(
            &self,
            egraph: &mut EGraph<Mio, MioAnalysis>,
            eclass: Id,
            subst: &Subst,
            searcher_ast: Option<&egg::PatternAst<Mio>>,
            rule_name: egg::Symbol,
        ) -> Vec<Id> {
            let k1s = subst[self.k1];
            let k2s = subst[self.k2];
            let a1s = subst[self.a1];
            let a2s = subst[self.a2];
            let k1_reads = MioAnalysis::read_set(egraph, k1s);
            let t1_elaborations = MioAnalysis::elaborations(egraph, a1s);
            if t1_elaborations.intersection(&k1_reads).count() > 0 {
                return vec![];
            }
            let new_keys = egraph[k1s].nodes[0]
                .children()
                .iter()
                .chain(egraph[k2s].nodes[0].children().iter())
                .cloned()
                .collect::<HashSet<_>>();
            let mut new_actions = vec![];
            for actions_a1 in egraph[a1s].nodes[0].children() {
                for actions_a2 in egraph[a2s].nodes[0].children() {
                    if MioAnalysis::elaborations(egraph, *actions_a1)
                        .is_disjoint(MioAnalysis::elaborations(egraph, *actions_a2))
                    {
                        new_actions.push(
                            egraph[*actions_a1].nodes[0]
                                .children()
                                .iter()
                                .chain(egraph[*actions_a2].nodes[0].children().iter())
                                .cloned()
                                .collect::<Vec<_>>(),
                        );
                    } else {
                        let mut elabs = egraph[*actions_a2].nodes[0].children().to_vec().clone();
                        for e1 in egraph[*actions_a1].nodes[0].children() {
                            if MioAnalysis::elaborations(egraph, *actions_a2)
                                .is_disjoint(MioAnalysis::elaborations(egraph, *e1))
                            {
                                elabs.push(*e1);
                            }
                        }
                        new_actions.push(elabs);
                    }
                }
            }
            let new_keys_id = egraph.add(Mio::Keys(new_keys.into_iter().collect()));
            let elaboration_ids = new_actions
                .into_iter()
                .map(|v| egraph.add(Mio::Elaborations(v)))
                .collect::<Vec<_>>();
            let new_actions_id = egraph.add(Mio::Actions(elaboration_ids));
            let new_table_id = egraph.add(Mio::GIte([new_keys_id, new_actions_id]));
            egraph.union(eclass, new_table_id);
            vec![eclass, new_table_id]
        }
    }
    vec![
        rewrite!(
            "waw-elim"; "(seq (gite ?k1s ?a1s) (seq (gite ?k2s ?a2s) ?t3))" => {
                WAWElimApplier {
                    k1: "?k1s".parse().unwrap(),
                    k2: "?k2s".parse().unwrap(),
                    a1: "?a1s".parse().unwrap(),
                    a2: "?a2s".parse().unwrap(),
                }
             }
        ),
        rewrite!("waw-elim-right"; "(seq (gite ?k1s ?a1s) (gite ?k2s ?a2s))" => {
            WAWElimApplier {
                k1: "?k1s".parse().unwrap(),
                k2: "?k2s".parse().unwrap(),
                a1: "?a1s".parse().unwrap(),
                a2: "?a2s".parse().unwrap(),
            }
        }),
    ]
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
            // remain at most n actions a time
            let mut remained = vec![];
            let mut split = vec![];
            let split_bound = self.2;
            let mut index = 0;
            for a in egraph[a1s].nodes[0].children() {
                // if *a elaborates to some global register r
                // and r is read by some other elaboration(s),
                // then it must stay in the same state
                if MioAnalysis::has_stateful_elaboration(egraph, *a) {
                    remained.push(index);
                } else if MioAnalysis::elaborations(egraph, *a).is_disjoint(&key_reads) {
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
pub fn multi_stage_action(global_update_limit: usize, phv_update_limit: usize) -> Vec<RW> {
    struct MultiStagedApplier(Var, Var, usize, usize);
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
            let global_update_limit = self.2;
            let local_update_limit = self.3;
            let keys_read = MioAnalysis::read_set(egraph, kid);
            // stores a vector of elaborations (Vec<Id>)
            let mut remained_updates = vec![];
            let mut splitted_updates = vec![];
            for elabs in egraph[aid].nodes[0].children() {
                let mut remained = vec![];
                let mut split = vec![];
                let mut num_global_writes = HashSet::new();
                let mut num_phv_writes = HashSet::new();
                let mut fixed = HashSet::new();
                for elaboration in egraph[*elabs].nodes[0].children() {
                    // each elaboration
                    if fixed.contains(elaboration) {
                        continue;
                    }
                    if MioAnalysis::elaborations(egraph, *elaboration).is_disjoint(keys_read) {
                        match &egraph[*elaboration].data {
                            MioAnalysisData::Action(u) => {
                                println!("elaborations: {:?}", u.elaborations);
                                if u.elaborations.iter().any(|x| x.contains("global.")) {
                                    if num_global_writes.len() == global_update_limit {
                                        split.push(*elaboration);
                                        for others in egraph[*elabs].nodes[0].children() {
                                            if others != elaboration
                                                && !split.contains(others)
                                                && MioAnalysis::read_set(egraph, *others)
                                                    .intersection(&u.elaborations)
                                                    .count()
                                                    > 0
                                            {
                                                if fixed.contains(others) {
                                                    remained.retain(|x| x != others);
                                                    num_global_writes.retain(|x| {
                                                        !MioAnalysis::elaborations(egraph, *others)
                                                            .contains(*x)
                                                    });
                                                    num_phv_writes.retain(|x| {
                                                        !MioAnalysis::elaborations(egraph, *others)
                                                            .contains(*x)
                                                    });
                                                }
                                                fixed.insert(others);
                                                split.push(*others);
                                            }
                                        }
                                    } else {
                                        num_global_writes.extend(u.elaborations.iter());
                                        remained.push(*elaboration);
                                    }
                                } else {
                                    if num_phv_writes.len() == local_update_limit {
                                        split.push(*elaboration);
                                        for others in egraph[*elabs].nodes[0].children() {
                                            if others != elaboration
                                                && !split.contains(others)
                                                && MioAnalysis::read_set(egraph, *others)
                                                    .intersection(&u.elaborations)
                                                    .count()
                                                    > 0
                                                && MioAnalysis::has_stateful_elaboration(
                                                    egraph, *others,
                                                )
                                            {
                                                if fixed.contains(others) {
                                                    remained.retain(|x| x != others);
                                                    num_global_writes.retain(|x| {
                                                        !MioAnalysis::elaborations(egraph, *others)
                                                            .contains(*x)
                                                    });
                                                    num_phv_writes.retain(|x| {
                                                        !MioAnalysis::elaborations(egraph, *others)
                                                            .contains(*x)
                                                    });
                                                }
                                                fixed.insert(others);
                                                split.push(*others);
                                            }
                                        }
                                    } else {
                                        num_phv_writes.extend(u.elaborations.iter());
                                        remained.push(*elaboration);
                                    }
                                }
                            }
                            _ => panic!("not an action"),
                        }
                    } else {
                        fixed.insert(elaboration);
                        split.push(*elaboration);
                    }
                }
                println!("remained: {:?}", remained);
                println!("split: {:?}", split);
                println!("num_global_writes: {:?}", num_global_writes);
                if remained.len() == 0 || split.len() == 0 {
                    continue;
                }
                assert!(remained.len() + split.len() == egraph[*elabs].nodes[0].children().len());
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
            { MultiStagedApplier("?k".parse().unwrap(), "?a".parse().unwrap(), global_update_limit, phv_update_limit) })];
}

pub fn ite_to_gite() -> Vec<RW> {
    vec![rewrite!("ite-to-gite"; "(ite ?c ?t1 ?t2)" => "(gite (keys ?c1) (actions ?t1 ?t2))")]
}
