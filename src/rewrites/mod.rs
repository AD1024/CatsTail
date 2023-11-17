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
            && self.alu_type == "arith-alu"
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
                                    format!("(E ?t ({} (arith-alu alu-global ?x) ?y))", op)
                                        .parse::<Pattern<Mio>>()
                                        .unwrap();
                                let pattern_r =
                                    format!("(E ?t ({} ?y (arith-alu alu-global ?x)))", op)
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
                                    let binding = egraph
                                        .analysis
                                        .new_var(MioAnalysis::get_type(egraph, to_lift));
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
                                let elaborate_id =
                                    egraph.add(Mio::Elaborate([table_name_id, *expr_id]));
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
                                let elaborate_id = egraph.add(Mio::Elaborate([table_name_id, id]));
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
