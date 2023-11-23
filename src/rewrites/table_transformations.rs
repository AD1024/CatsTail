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

pub fn ite_to_gite() -> Vec<RW> {
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
            let pattern = "(ite ?c ?b1 ?b2)".parse::<Pattern<Mio>>().unwrap();
            // let mut remain = vec![];
            // let mut split = vec![];
            for elaborators in elaborations {
                // check statueful updates:
                // only allow
            }
            vec![]
        }
    }
    vec![rewrite!("ite-to-gite"; "(gite ?k ?a)" => {
        IteToGIteApplier {
            keys: "?k",
            actions: "?a",
        }
    })]
}
