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
        t3: Option<Var>,
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
            let mut new_table_id = egraph.add(Mio::GIte([new_keys_id, new_actions_id]));
            if let Some(t3) = self.t3 {
                new_table_id = egraph.add(Mio::Seq([new_table_id, subst[t3]]));
            }
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
                    t3: Some("?t3".parse().unwrap()),
                }
             }
        ),
        rewrite!("waw-elim-right"; "(seq (gite ?k1s ?a1s) (gite ?k2s ?a2s))" => {
            WAWElimApplier {
                k1: "?k1s".parse().unwrap(),
                k2: "?k2s".parse().unwrap(),
                a1: "?a1s".parse().unwrap(),
                a2: "?a2s".parse().unwrap(),
                t3: None,
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

pub fn lift_ite_cond() -> Vec<RW> {
    struct IteToGIteApplier {
        keys: &'static str,
        actions: &'static str,
    }
    impl Applier<Mio, MioAnalysis> for IteToGIteApplier {
        fn apply_one(
            &self,
            egraph: &mut EGraph<Mio, MioAnalysis>,
            eclass: Id,
            subst: &Subst,
            searcher_ast: Option<&egg::PatternAst<Mio>>,
            rule_name: egg::Symbol,
        ) -> Vec<Id> {
            let kid = subst[self.keys.parse().unwrap()];
            let aid = subst[self.actions.parse().unwrap()];
            let elaborations = MioAnalysis::aggregate_elaborators(egraph, aid);
            let mut remain = vec![];
            let mut split = vec![];
            let mut fixed = HashSet::new();
            let mut expr_map = HashMap::new();
            let prev_table = egraph
                .analysis
                .new_table_name(MioAnalysis::get_table_name(egraph, eclass));
            let next_table = egraph
                .analysis
                .new_table_name(MioAnalysis::get_table_name(egraph, eclass));
            for elaborators in elaborations.iter() {
                // check statueful updates:
                // only allow ?c to read from one global register
                let mut subremain = vec![];
                let mut subsplit = vec![];
                let mut split_reads = HashSet::new();
                for elab in elaborators.iter() {
                    assert_eq!(MioAnalysis::elaborations(egraph, *elab).len(), 1);
                    let comp_id = MioAnalysis::unwrap_elaborator(egraph, *elab);
                    let evar = MioAnalysis::get_single_elaboration(egraph, *elab);
                    if !MioAnalysis::has_stateful_elaboration(egraph, *elab) {
                        continue;
                    }
                    if MioAnalysis::elaborations(egraph, *elab)
                        .union(&MioAnalysis::stateful_reads(egraph, *elab))
                        .count()
                        <= 1
                    {
                        continue;
                    }
                    for node in egraph[comp_id].nodes.clone() {
                        match node {
                            Mio::Ite([c, ib, rb]) => {
                                if MioAnalysis::stateful_read_count(egraph, c) > 1 {
                                    continue;
                                }
                                let c_stateful_rd = MioAnalysis::stateful_reads(egraph, c);
                                let ib_stateful_rd = MioAnalysis::stateful_reads(egraph, ib);
                                let rb_stateful_rd = MioAnalysis::stateful_reads(egraph, rb);
                                if c_stateful_rd
                                    .intersection(
                                        &ib_stateful_rd.union(&rb_stateful_rd).cloned().collect(),
                                    )
                                    .count()
                                    > 0
                                {
                                    break;
                                }
                                for compare_node in egraph[c].nodes.clone() {
                                    match compare_node {
                                        Mio::Lt([lhs, rhs]) => {
                                            if MioAnalysis::has_stateful_reads(egraph, lhs)
                                                && MioAnalysis::has_stateful_reads(egraph, rhs)
                                            {
                                                continue;
                                            }
                                            let (var_name, new_comp, compute_phv) =
                                                if MioAnalysis::has_stateful_reads(egraph, lhs) {
                                                    let new_phv_field = egraph.analysis.new_var(
                                                        MioAnalysis::get_type(egraph, lhs),
                                                        lhs.to_string(),
                                                    );
                                                    let phv_id = egraph
                                                        .add(Mio::Symbol(new_phv_field.clone()));
                                                    (
                                                        new_phv_field,
                                                        egraph.add(Mio::Lt([phv_id, rhs])),
                                                        lhs,
                                                    )
                                                } else {
                                                    let new_phv_field = egraph.analysis.new_var(
                                                        MioAnalysis::get_type(egraph, rhs),
                                                        rhs.to_string(),
                                                    );
                                                    let phv_id = egraph
                                                        .add(Mio::Symbol(new_phv_field.clone()));
                                                    (
                                                        new_phv_field,
                                                        egraph.add(Mio::Lt([lhs, phv_id])),
                                                        rhs,
                                                    )
                                                };
                                            let new_ite = egraph.add(Mio::Ite([new_comp, ib, rb]));
                                            subsplit.push((var_name, compute_phv));
                                            split_reads.extend(MioAnalysis::stateful_reads(
                                                egraph,
                                                compute_phv,
                                            ));
                                            subremain.push((evar.clone(), new_ite));
                                            fixed.insert(*elab);
                                            expr_map.insert(c, new_comp);
                                            break;
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                for elab in elaborators.iter() {
                    if !fixed.contains(elab) {
                        let comp_id = MioAnalysis::unwrap_elaborator(egraph, *elab);
                        let evar = MioAnalysis::get_single_elaboration(egraph, *elab);
                        if split_reads.contains(&evar) {
                            subsplit.push((evar, comp_id));
                            continue;
                        }
                        for node in egraph[comp_id].nodes.clone() {
                            match node {
                                Mio::Ite([c, ib, rb]) => {
                                    fixed.insert(*elab);
                                    if expr_map.contains_key(&c) {
                                        let new_ite = egraph.add(Mio::Ite([
                                            *expr_map.get(&c).unwrap(),
                                            ib,
                                            rb,
                                        ]));
                                        subremain.push((evar.clone(), new_ite));
                                    } else {
                                        subremain.push((evar.clone(), comp_id));
                                    }
                                }
                                _ => (),
                            }
                        }
                        if !fixed.contains(elab) {
                            subremain.push((evar.clone(), comp_id));
                        }
                    }
                }
                if subremain.len() > 0 {
                    remain.push(subremain)
                }
                if subsplit.len() > 0 {
                    split.push(subsplit);
                }
            }
            if remain.len() == 0 || split.len() == 0 {
                return vec![];
            }
            let (remain_elabs, remain_comps) = remain
                .into_iter()
                .map(|v| {
                    v.into_iter()
                        .map(|(v, id)| (HashSet::from([v]), id))
                        .unzip::<_, _, Vec<_>, Vec<_>>()
                })
                .unzip::<_, _, Vec<_>, Vec<_>>();
            let (split_elabs, split_comps) = split
                .into_iter()
                .map(|v| {
                    v.into_iter()
                        .map(|(v, id)| (HashSet::from([v]), id))
                        .unzip::<_, _, Vec<_>, Vec<_>>()
                })
                .unzip::<_, _, Vec<_>, Vec<_>>();
            let prev_table_id =
                MioAnalysis::build_table(egraph, prev_table, kid, split_comps, split_elabs);
            let next_table_id =
                MioAnalysis::build_table(egraph, next_table, kid, remain_comps, remain_elabs);
            let seq_id = egraph.add(Mio::Seq([prev_table_id, next_table_id]));
            egraph.union(eclass, seq_id);
            vec![seq_id, eclass]
        }
    }
    vec![rewrite!("lift_ite_cond"; "(gite ?k ?a)" => {
        IteToGIteApplier {
            keys: "?k",
            actions: "?a",
        }
    })]
}
