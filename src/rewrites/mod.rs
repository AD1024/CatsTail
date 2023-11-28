use egg::{rewrite, Applier, EGraph, Id, Language, Pattern, Rewrite, Searcher, Subst, Var};

use crate::language::{
    ir::{Constant, Mio, MioAnalysis, MioAnalysisData},
    utils::{get_dependency, Dependency},
};

pub mod alg_simp;
pub mod domino;
pub mod table_transformations;
pub mod tofino;

type RW = Rewrite<Mio, MioAnalysis>;
type EG = EGraph<Mio, MioAnalysis>;

fn constains_leaf(v: Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let eclass = subst[v];
        return MioAnalysis::has_leaf(egraph, eclass);
    }
}

#[allow(dead_code)]
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

#[allow(dead_code)]
fn same_elaboration(v1: Var, v2: Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let eclass1 = subst[v1];
        let eclass2 = subst[v2];
        let elaborations1 = MioAnalysis::elaborations(egraph, eclass1);
        let elaborations2 = MioAnalysis::elaborations(egraph, eclass2);
        return elaborations1 == elaborations2;
    }
}

#[allow(dead_code)]
fn same_read(v1: Var, v2: Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let eclass1 = subst[v1];
        let eclass2 = subst[v2];
        let read_set1 = MioAnalysis::read_set(egraph, eclass1);
        let read_set2 = MioAnalysis::read_set(egraph, eclass2);
        return read_set1 == read_set2;
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
    move |egraph, _id, subst| {
        let eclass = subst[v];
        // return check_level(egraph, eclass, n, stateful);
        if MioAnalysis::min_depth(egraph, eclass) == 0 {
            return true;
        }
        let check_depth = |children: &Vec<Id>| {
            children
                .iter()
                .map(|c| MioAnalysis::min_depth(egraph, *c))
                .max()
                .unwrap_or(0)
                + 1
                <= n
        };
        if let Some(stateful) = stateful {
            if stateful {
                for node in egraph[eclass].nodes.iter() {
                    match node {
                        Mio::SAlu(children) => {
                            return check_depth(children);
                        }
                        _ => continue,
                    }
                }
                return false;
            } else {
                for node in egraph[eclass].nodes.iter() {
                    match node {
                        Mio::RelAlu(children) | Mio::ArithAlu(children) => {
                            return check_depth(children);
                        }
                        _ => continue,
                    }
                }
                return false;
            }
        } else {
            for node in egraph[eclass].nodes.iter() {
                match node {
                    Mio::RelAlu(children) | Mio::SAlu(children) | Mio::ArithAlu(children) => {
                        return check_depth(children);
                    }
                    _ => continue,
                }
            }
            return false;
        }
    }
}

/// Map (E ?t ?expr) to Alu operators (for ?expr)
/// will decide whether to map to stateful or stay stateless
#[allow(dead_code)]
struct ElaboratorConversion {
    table_id: Var,
    expr: Var,
}

impl ElaboratorConversion {
    fn new(table_id: &'static str, expr: &'static str) -> Self {
        Self {
            table_id: table_id.parse().unwrap(),
            expr: expr.parse().unwrap(),
        }
    }
}

impl Applier<Mio, MioAnalysis> for ElaboratorConversion {
    fn apply_one(
        &self,
        egraph: &mut EGraph<Mio, MioAnalysis>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&egg::PatternAst<Mio>>,
        _rule_name: egg::Symbol,
    ) -> Vec<Id> {
        // let table_id = subst[self.table_id];
        let expr_id = subst[self.expr];
        let elaborations = MioAnalysis::elaborations(egraph, eclass).clone();
        let (op, args) = MioAnalysis::decompose_alu_ops(egraph, expr_id).unwrap();
        if MioAnalysis::has_stateful_elaboration(egraph, eclass)
            || MioAnalysis::has_stateful_reads(egraph, eclass)
        {
            // map to stateful alu
            let output_var_id =
                egraph.add(Mio::Symbol(elaborations.iter().next().unwrap().clone()));
            let op_id = if let Some(arith_op) = MioAnalysis::to_arith_alu_op(&op) {
                egraph.add(Mio::ArithAluOps(arith_op))
            } else {
                egraph.add(Mio::RelAluOps(op.parse().unwrap()))
            };
            let alu_id = egraph.add(Mio::SAlu(
                vec![op_id, output_var_id]
                    .into_iter()
                    .chain(args.into_iter())
                    .collect(),
            ));
            // let elaborator_id = egraph.add(Mio::Elaborate([table_id, output_var_id, alu_id]));
            // MioAnalysis::set_elaboration(egraph, elaborator_id, elaborations);
            egraph.union(expr_id, alu_id);
            return vec![];
        }
        return vec![];
    }
}

pub fn elaborator_conversion() -> Vec<RW> {
    vec![rewrite!("elaborator-conversion";
            "(E ?t ?v ?expr)" => {
                ElaboratorConversion::new("?t", "?expr")
            }
            if is_mapped("?expr".parse().unwrap(), Some(false)))]
}

struct AluApplier {
    alu_type: &'static str,
    alu_op: &'static str,
    operands: Vec<&'static str>,
}

impl AluApplier {
    fn new(alu_type: &'static str, alu_op: &'static str, operands: Vec<&'static str>) -> Self {
        Self {
            alu_type,
            alu_op,
            operands,
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

#[allow(dead_code)]
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
            _searcher_ast: Option<&egg::PatternAst<Mio>>,
            _rule_name: egg::Symbol,
        ) -> Vec<Id> {
            // First check whether in each action there is an elaboration that involves
            // both reading and writing to a global variable
            let keys = subst[self.0];
            let action_wrapper_id = subst[self.1];
            let mut lhs_action_elabs = vec![];
            let mut rhs_action_elabs = vec![];
            // copy to avoid holding mut and immut references
            // (actions (elaborations (E e) ...))
            for action_wrapper in egraph[action_wrapper_id]
                .nodes
                .iter()
                .cloned()
                .collect::<Vec<_>>()
            {
                // (elaborations (E e) ...)
                for &elab_wrapper_id in action_wrapper.children() {
                    for elab_node in egraph[elab_wrapper_id]
                        .nodes
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                    {
                        let mut remain = vec![];
                        let mut lifted = vec![];
                        // (E e)
                        for &action_elaborations in elab_node.children() {
                            let elaborations =
                                MioAnalysis::elaborations(egraph, action_elaborations).clone();
                            let read_set = MioAnalysis::read_set(egraph, action_elaborations);
                            if elaborations.intersection(read_set).next().is_none() {
                                // no read-write global variable
                                continue;
                            }
                            // we will need to check whether this elaboration has a match in the form of
                            // (?op ?x ?y) where ?x or ?y is a global variable
                            for op in ["+", "-"] {
                                let pattern_l =
                                    format!("(E ?t ?v ({} (arith-alu alu-global ?x) ?y))", op)
                                        .parse::<Pattern<Mio>>()
                                        .unwrap();
                                let pattern_r =
                                    format!("(E ?t ?v ({} ?y (arith-alu alu-global ?x)))", op)
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
                                        remain.push((action_elaborations, elaborations.clone()));
                                        continue;
                                    }
                                    if !is_mapped(pattern_var, Some(false))(
                                        egraph,
                                        action_elaborations,
                                        new_subst,
                                    ) {
                                        // if it is not mapped to stateless alus, we can't lift it
                                        remain.push((action_elaborations, elaborations.clone()));
                                        continue;
                                    }
                                    let to_lift = new_subst[pattern_var];
                                    let binding = egraph.analysis.new_var(
                                        MioAnalysis::get_type(egraph, to_lift),
                                        to_lift.to_string(),
                                    );
                                    // remaining computation should be (op ?x ?binding) / (op ?binding ?x)
                                    let alu_global_id =
                                        egraph.add(Mio::ArithAluOps("alu-global".parse().unwrap()));
                                    // Id of (arith-alu alu-global ?x)
                                    let global_var_id = egraph.add(Mio::ArithAlu(vec![
                                        alu_global_id,
                                        new_subst["?x".parse().unwrap()],
                                    ]));
                                    let binding_id = egraph.add(Mio::Symbol(binding.clone()));
                                    let remain_id = if hit_left {
                                        // Wrap to be (op (arith-alu alu-global ?x) ?binding)
                                        MioAnalysis::add_expr(
                                            egraph,
                                            op,
                                            vec![global_var_id, binding_id],
                                        )
                                    } else {
                                        // Wrap to be (op ?binding (arith-alu alu-global ?x))
                                        MioAnalysis::add_expr(
                                            egraph,
                                            op,
                                            vec![binding_id, global_var_id],
                                        )
                                    };
                                    remain.push((remain_id, elaborations.clone()));
                                    lifted.push((to_lift, binding));
                                } else {
                                    remain.push((action_elaborations, elaborations.clone()));
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
                let origin_table_name = MioAnalysis::get_table_name(egraph, eclass);
                let new_table_name = egraph.analysis.new_table_name(origin_table_name.clone());
                let table_name_id = egraph.add(Mio::Symbol(new_table_name));
                let elaborate_ids = lhs_action_elabs
                    .iter()
                    .map(|v| {
                        v.iter()
                            .map(|(expr_id, binding)| {
                                let evar_id = egraph.add(Mio::Symbol(binding.clone()));
                                let elaborate_id =
                                    egraph.add(Mio::Elaborate([table_name_id, evar_id, *expr_id]));
                                MioAnalysis::add_to_elaboration(
                                    egraph,
                                    elaborate_id,
                                    binding.clone(),
                                );
                                return elaborate_id;
                            })
                            .collect()
                    })
                    .collect::<Vec<Vec<_>>>();
                let elab_ids = elaborate_ids
                    .into_iter()
                    .map(|v| egraph.add(Mio::Elaborations(v)))
                    .collect::<Vec<_>>();
                let action_id = egraph.add(Mio::Actions(elab_ids));
                let lhs_table_id = egraph.add(Mio::GIte([keys, action_id]));
                // Construct RHS table
                let new_table_name = egraph.analysis.new_table_name(origin_table_name);
                let table_name_id = egraph.add(Mio::Symbol(new_table_name));
                // Construct Vec of (E expr)
                let elaborate_ids = rhs_action_elabs
                    .into_iter()
                    .map(|v| {
                        v.into_iter()
                            .map(|(id, elaboration)| {
                                let evar_id = egraph
                                    .add(Mio::Symbol(elaboration.iter().next().unwrap().clone()));
                                let elaborate_id =
                                    egraph.add(Mio::Elaborate([table_name_id, evar_id, id]));
                                MioAnalysis::set_elaboration(egraph, elaborate_id, elaboration);
                                return elaborate_id;
                            })
                            .collect()
                    })
                    .collect::<Vec<Vec<_>>>();
                // Construct each action: (Elaboration (E e1) (E e2) ...)
                let elab_ids = elaborate_ids
                    .into_iter()
                    .map(|v| egraph.add(Mio::Elaborations(v)))
                    .collect::<Vec<_>>();
                // Construct Action node
                let action_id = egraph.add(Mio::Actions(elab_ids));
                // Finally, the table
                let rhs_table_id = egraph.add(Mio::GIte([keys, action_id]));
                // LHS before RHS, set value to the binding
                let seq_id = egraph.add(Mio::Seq([lhs_table_id, rhs_table_id]));
                vec![seq_id].into_iter().collect()
            }
        }
    }
    // TODO: add 2 more rewrits:
    // 1. lift stateless updates to previous stage or next stage
    // 2. Make stateless computation to elaborate to some PHV fields in the same stage
    struct LiftStatelessUpdate {
        keys: Var,
        actions: Var,
        is_prepend: bool,
    }

    impl Applier<Mio, MioAnalysis> for LiftStatelessUpdate {
        fn apply_one(
            &self,
            egraph: &mut EGraph<Mio, MioAnalysis>,
            eclass: Id,
            subst: &Subst,
            _searcher_ast: Option<&egg::PatternAst<Mio>>,
            _rule_name: egg::Symbol,
        ) -> Vec<Id> {
            let kid = subst[self.keys];
            let action_id = subst[self.actions];
            // first aggregate global updates; these must be pinned
            let mut remain = vec![];
            let mut split = vec![];
            let mut remain_elaborations = vec![];
            let mut split_elaborations = vec![];
            let reads = MioAnalysis::read_set(egraph, kid);
            for elaborations in MioAnalysis::aggregate_elaborators(egraph, action_id) {
                let mut current_remain = elaborations
                    .iter()
                    .cloned()
                    .filter(|x| MioAnalysis::has_stateful_elaboration(egraph, *x))
                    .collect::<Vec<_>>();
                let mut current_remain_elaborations = current_remain
                    .iter()
                    .map(|x| MioAnalysis::elaborations(egraph, *x).clone())
                    .collect::<Vec<_>>();
                if current_remain.len() == 0 {
                    remain_elaborations.push(
                        elaborations
                            .iter()
                            .map(|x| MioAnalysis::elaborations(egraph, *x).clone())
                            .collect::<Vec<_>>(),
                    );
                    remain.push(elaborations);
                    continue;
                }
                let mut current_split_elaborations = vec![];
                let mut current_split = vec![];
                let mut remain_reads = current_remain
                    .iter()
                    .map(|x| MioAnalysis::read_set(egraph, *x).clone())
                    .reduce(|a, b| a.union(&b).cloned().collect())
                    .unwrap();
                let mut remain_writes = current_remain
                    .iter()
                    .map(|x| MioAnalysis::elaborations(egraph, *x).clone())
                    .reduce(|a, b| a.union(&b).cloned().collect())
                    .unwrap();
                for elaborator in elaborations.iter() {
                    if MioAnalysis::has_stateful_elaboration(egraph, *elaborator) {
                        continue;
                    }
                    let stateless_reads = MioAnalysis::read_set(egraph, *elaborator);
                    let stateless_writes = MioAnalysis::elaborations(egraph, *elaborator);
                    if self.is_prepend {
                        // a stateless update can be lifted to the previous stage if
                        // 1. it does not read global registers in the current stage
                        // 2. it does not write variables in `remain_reads`
                        if MioAnalysis::has_stateful_reads(egraph, *elaborator)
                            || !stateless_writes.is_disjoint(&reads)
                            || !stateless_writes.is_disjoint(&remain_reads)
                        {
                            current_remain.push(*elaborator);
                            current_remain_elaborations
                                .push(MioAnalysis::elaborations(egraph, *elaborator).clone());
                            remain_reads = remain_reads.union(&stateless_reads).cloned().collect();
                            remain_writes =
                                remain_writes.union(&stateless_writes).cloned().collect();
                        } else {
                            current_split.push(*elaborator);
                            current_split_elaborations
                                .push(MioAnalysis::elaborations(egraph, *elaborator).clone());
                        }
                    } else {
                        // a stateless update can be lifted to the next stage if
                        // 1. remain_writes does not modify keys
                        // 2. remain_writes does not modify stateless_reads
                        if !remain_writes.is_disjoint(&reads)
                            || !remain_writes.is_disjoint(&stateless_reads)
                        {
                            current_remain.push(*elaborator);
                            remain_reads = remain_reads.union(&stateless_reads).cloned().collect();
                            remain_writes =
                                remain_writes.union(&stateless_writes).cloned().collect();
                        } else {
                            current_split.push(*elaborator);
                        }
                    }
                }
                if current_remain.len() == 0 || current_split.len() == 0 {
                    continue;
                }
                debug_assert!(current_remain.len() + current_split.len() == elaborations.len());
                remain.push(current_remain);
                split.push(current_split);
                remain_elaborations.push(current_remain_elaborations);
                split_elaborations.push(current_split_elaborations);
            }
            let table_name = MioAnalysis::get_table_name(egraph, eclass)
                .unwrap_or(format!("lifted-{}", egraph.analysis.new_table_name(None)));
            let lhs_table = MioAnalysis::build_table(
                egraph,
                table_name.clone(),
                kid,
                split,
                split_elaborations,
            );
            let rhs_table =
                MioAnalysis::build_table(egraph, table_name, kid, remain, remain_elaborations);
            let seq_id = egraph.add(Mio::Seq(if self.is_prepend {
                [lhs_table, rhs_table]
            } else {
                [rhs_table, lhs_table]
            }));
            vec![seq_id]
        }
    }
    vec![
        // If a computation is the form of (op ?x ?y) where one of ?x ?y is a global update
        // lift the computation of the stateless one to the previous stage and elaborate to
        // some PHV field
        rewrite!("lift-comp";
                "(gite ?keys ?actions)" =>
                {  StatelessLiftApplier("?keys".parse().unwrap(), "?actions".parse().unwrap()) }),
        // If an update to PHV field is fully stateless (i.e. no read to global variables)
        // then we can lift it to the previous stage if the elaborated field is not in the read set of keys;
        // if all other updates does not modify the read set of the stateless update, we can also lift it to the next stage.
        // This rule lift as many updates as possible (as long as it does not break the above constraints)
        // rewrite!("lift-stateless-update-prev";
        // "(gite ?keys ?actions)" =>
        // {
        //     LiftStatelessUpdate {
        //         keys: "?keys".parse().unwrap(),
        //         actions: "?actions".parse().unwrap(),
        //         is_prepend: true,
        //     }
        // }),
    ]
}
