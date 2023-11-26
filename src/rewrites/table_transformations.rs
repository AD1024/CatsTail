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

fn compute_lift_cond(
    egraph: &mut EGraph<Mio, MioAnalysis>,
    c: Id,
    ib: Id,
    rb: Id,
) -> Option<(String, Id, Id)> {
    let ib_stateful_rd = MioAnalysis::stateful_reads(egraph, ib);
    let rb_stateful_rd = MioAnalysis::stateful_reads(egraph, rb);
    let compute_rd = ib_stateful_rd
        .union(&rb_stateful_rd)
        .cloned()
        .collect::<HashSet<_>>();
    for compare_node in egraph[c].nodes.clone() {
        match compare_node {
            Mio::Lt([lhs, rhs])
            | Mio::Gt([lhs, rhs])
            | Mio::Le([lhs, rhs])
            | Mio::Ge([lhs, rhs])
            | Mio::Eq([lhs, rhs])
            | Mio::Neq([lhs, rhs])
            | Mio::LAnd([lhs, rhs])
            | Mio::LOr([lhs, rhs]) => {
                let (var_name, new_comp, compute_phv) =
                    // comsider ?c to be (?op lhs rhs)
                    // we can lift lhs or rhs to some new phv field
                    // if it only involves with 1 stateful read
                    if MioAnalysis::stateful_read_count(egraph, lhs)
                        == 1
                    {
                        // if the computation depends on some global variables
                        // that is also required by lhs or rhs, then we cannot
                        // lift it (read then write to the same global variable has to be atomic)
                        if MioAnalysis::stateful_reads(egraph, lhs)
                            .intersection(&compute_rd)
                            .count()
                            > 0
                        {
                            continue;
                        }
                        let new_phv_field = egraph.analysis.new_var(
                            MioAnalysis::get_type(egraph, lhs),
                            lhs.to_string(),
                        );
                        let phv_id = egraph
                            .add(Mio::Symbol(new_phv_field.clone()));
                        (
                            new_phv_field,
                            MioAnalysis::add_expr(egraph, &MioAnalysis::get_operator_repr(&compare_node), vec![phv_id, rhs]),
                            lhs,
                        )
                    } else if MioAnalysis::stateful_read_count(
                        egraph, rhs,
                    ) == 1
                    {
                        if MioAnalysis::stateful_reads(egraph, rhs)
                            .intersection(&compute_rd)
                            .count()
                            > 0
                        {
                            continue;
                        }
                        let new_phv_field = egraph.analysis.new_var(
                            MioAnalysis::get_type(egraph, rhs),
                            rhs.to_string(),
                        );
                        let phv_id = egraph
                            .add(Mio::Symbol(new_phv_field.clone()));
                        (
                            new_phv_field,
                            MioAnalysis::add_expr(egraph, &MioAnalysis::get_operator_repr(&compare_node), vec![lhs, phv_id]),
                            rhs,
                        )
                    } else {
                        continue;
                    };
                return Some((var_name, new_comp, compute_phv));
            }
            _ => {}
        }
    }
    return None;
}

/// If a stateful elaboration is a conditional
/// assignment, and the condition is in the form of
///         ?x = ?y, ?x != ?y, ?x < ?y, etc
/// then we consider lifting ?x or ?y to the previous stage if it contains some
/// stateful reads to another stateful variable; otherwise the computations
/// cannot be mapped onto a single stateful alu.
pub fn lift_ite_compare() -> Vec<RW> {
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
                // check statueful updates
                let mut subremain = vec![];
                let mut subsplit = vec![];
                let mut split_reads = HashSet::new();
                for elab in elaborators.iter() {
                    assert_eq!(MioAnalysis::elaborations(egraph, *elab).len(), 1);
                    let comp_id = MioAnalysis::unwrap_elaborator(egraph, *elab);
                    let evar = MioAnalysis::get_single_elaboration(egraph, *elab);
                    if !MioAnalysis::has_stateful_elaboration(egraph, *elab)
                        && MioAnalysis::stateful_read_count(egraph, *elab) <= 1
                    {
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
                                if let Some((var_name, new_comp, compute_phv)) =
                                    compute_lift_cond(egraph, c, ib, rb)
                                {
                                    let new_ite = egraph.add(Mio::Ite([new_comp, ib, rb]));
                                    subsplit.push((var_name, compute_phv));
                                    split_reads
                                        .extend(MioAnalysis::stateful_reads(egraph, compute_phv));
                                    subremain.push((evar.clone(), new_ite));
                                    fixed.insert(*elab);
                                    expr_map.insert(c, new_comp);
                                    break;
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

pub fn lift_nested_ite_cond() -> Vec<RW> {
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
                // check statueful updates
                let mut subremain = vec![];
                let mut subsplit = vec![];
                let mut split_reads = HashSet::new();
                for elab in elaborators.iter() {
                    assert_eq!(MioAnalysis::elaborations(egraph, *elab).len(), 1);
                    let comp_id = MioAnalysis::unwrap_elaborator(egraph, *elab);
                    let evar = MioAnalysis::get_single_elaboration(egraph, *elab);
                    if !MioAnalysis::has_stateful_elaboration(egraph, *elab)
                        && MioAnalysis::stateful_read_count(egraph, *elab) <= 1
                    {
                        continue;
                    }
                    if MioAnalysis::elaborations(egraph, *elab)
                        .union(&MioAnalysis::stateful_reads(egraph, *elab))
                        .count()
                        <= 1
                    {
                        continue;
                    }
                    'outter_loop: for node in egraph[comp_id].nodes.clone() {
                        match node {
                            Mio::Ite([c, ib, rb]) => {
                                for ib_node in egraph[ib].nodes.clone() {
                                    match ib_node {
                                        Mio::Ite([ib_c, ib_ib, ib_rb]) => {
                                            if let Some((var_name, new_comp, compute_phv)) =
                                                compute_lift_cond(egraph, ib_c, ib_ib, ib_rb)
                                            {
                                                let inner_ite =
                                                    egraph.add(Mio::Ite([new_comp, ib_ib, ib_rb]));
                                                let new_ite =
                                                    egraph.add(Mio::Ite([c, inner_ite, rb]));
                                                subsplit.push((var_name, compute_phv));
                                                split_reads.extend(MioAnalysis::stateful_reads(
                                                    egraph,
                                                    compute_phv,
                                                ));
                                                subremain.push((evar.clone(), new_ite));
                                                fixed.insert(*elab);
                                                expr_map.insert(ib_c, new_comp);
                                                break 'outter_loop;
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                                for rb_node in egraph[rb].nodes.clone() {
                                    match rb_node {
                                        Mio::Ite([rb_c, rb_ib, rb_rb]) => {
                                            if let Some((var_name, new_comp, compute_phv)) =
                                                compute_lift_cond(egraph, rb_c, rb_ib, rb_rb)
                                            {
                                                let inner_ite =
                                                    egraph.add(Mio::Ite([new_comp, rb_ib, rb_rb]));
                                                let new_ite =
                                                    egraph.add(Mio::Ite([c, ib, inner_ite]));
                                                subsplit.push((var_name, compute_phv));
                                                split_reads.extend(MioAnalysis::stateful_reads(
                                                    egraph,
                                                    compute_phv,
                                                ));
                                                subremain.push((evar.clone(), new_ite));
                                                fixed.insert(*elab);
                                                expr_map.insert(rb_c, new_comp);
                                                break 'outter_loop;
                                            }
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
                            fixed.insert(*elab);
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
                            fixed.insert(*elab);
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
    vec![rewrite!("lift_nested_cond"; "(gite ?k ?a)" => {
        IteToGIteApplier {
            keys: "?k",
            actions: "?a",
        }
    })]
}

/// Similar to the above rewrite
/// except it considers the condition to ba
///   ?x && ?y, ?x || ?y and !?x
/// and we remove the assumption of the elaboration
/// to be stateful
pub fn lift_ite_cond() -> Vec<RW> {
    struct LiftIteCondApplier {
        keys: &'static str,
        actions: &'static str,
    }
    impl Applier<Mio, MioAnalysis> for LiftIteCondApplier {
        fn apply_one(
            &self,
            egraph: &mut EGraph<Mio, MioAnalysis>,
            eclass: Id,
            subst: &Subst,
            searcher_ast: Option<&egg::PatternAst<Mio>>,
            rule_name: egg::Symbol,
        ) -> Vec<Id> {
            let k_id = subst[self.keys.parse().unwrap()];
            let a_id = subst[self.actions.parse().unwrap()];
            let elaborations = MioAnalysis::aggregate_elaborators(egraph, a_id);
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
                let mut subremain = vec![];
                let mut subsplit = vec![];
                let mut split_reads = HashSet::new();
                for elaborator in elaborators {
                    assert_eq!(MioAnalysis::elaborations(egraph, *elaborator).len(), 1);
                    let comp_id = MioAnalysis::unwrap_elaborator(egraph, *elaborator);
                    let evar = MioAnalysis::get_single_elaboration(egraph, *elaborator);
                    for comp_node in egraph[comp_id].nodes.clone() {
                        if fixed.contains(&evar) {
                            break;
                        }
                        match comp_node {
                            Mio::Ite([c, ib, rb]) => {
                                if MioAnalysis::read_set(egraph, c).len() == 0 {
                                    continue;
                                }
                                for cond_node in egraph[c].nodes.clone() {
                                    match cond_node {
                                        Mio::LAnd([x, y])
                                        | Mio::LOr([x, y])
                                        | Mio::LXor([x, y]) => {
                                            // 1. x and y are fully stateless
                                            //    -> Lift both to the previous stage
                                            // 2. x and y are fully stateful
                                            // 3. one of x and y is stateful, the other is stateless
                                            //    -> Only lift if it only requires 1 stateful read
                                            if MioAnalysis::stateful_read_count(egraph, x)
                                                + MioAnalysis::stateful_read_count(egraph, y)
                                                <= 1
                                            {
                                                let new_phv_field = egraph.analysis.new_var(
                                                    MioAnalysis::get_type(egraph, c),
                                                    c.to_string(),
                                                );
                                                let phv_id =
                                                    egraph.add(Mio::Symbol(new_phv_field.clone()));
                                                let const_1 =
                                                    egraph.add(Mio::Constant(Constant::Bool(true)));
                                                let new_cond =
                                                    egraph.add(Mio::Eq([phv_id, const_1]));
                                                let new_ite =
                                                    egraph.add(Mio::Ite([new_cond, ib, rb]));
                                                let compute_phv = MioAnalysis::add_expr(
                                                    egraph,
                                                    &MioAnalysis::get_operator_repr(&cond_node),
                                                    vec![x, y],
                                                );
                                                subsplit.push((new_phv_field, compute_phv));
                                                split_reads.extend(MioAnalysis::stateful_reads(
                                                    egraph,
                                                    compute_phv,
                                                ));
                                                assert!(!fixed.contains(&evar));
                                                subremain.push((evar.clone(), new_ite));
                                                fixed.insert(evar.clone());
                                                expr_map.insert(c, new_cond);
                                                break;
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                for elaborator in elaborators {
                    let evar = MioAnalysis::get_single_elaboration(egraph, *elaborator);
                    if !fixed.contains(&evar) {
                        let comp_id = MioAnalysis::unwrap_elaborator(egraph, *elaborator);
                        if split_reads.contains(&evar) {
                            subsplit.push((evar.clone(), comp_id));
                            fixed.insert(evar);
                            continue;
                        }
                        for comp_node in egraph[comp_id].nodes.clone() {
                            if fixed.contains(&evar) {
                                break;
                            }
                            match comp_node {
                                Mio::Ite([c, ib, rb]) => {
                                    fixed.insert(evar.clone());
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
                                    break;
                                }
                                _ => (),
                            }
                        }
                        if !fixed.contains(&evar) {
                            fixed.insert(evar.clone());
                            subremain.push((evar, comp_id));
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
                MioAnalysis::build_table(egraph, prev_table, k_id, split_comps, split_elabs);
            let next_table_id =
                MioAnalysis::build_table(egraph, next_table, k_id, remain_comps, remain_elabs);
            let seq_id = egraph.add(Mio::Seq([prev_table_id, next_table_id]));
            egraph.union(eclass, seq_id);
            vec![seq_id, eclass]
        }
    }
    vec![rewrite!("lift-ite-cond";
    "(gite ?k ?a)" =>
        {
            LiftIteCondApplier {
                keys: "?k",
                actions: "?a",
            }
        })]
}
