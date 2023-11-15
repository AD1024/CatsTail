use egg::{Applier, EGraph, Id, Language, Pattern, Rewrite, Subst, Var};

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

mod test {
    use std::time::Duration;

    use egg::{Extractor, Runner};

    use crate::{
        extractors::GreedyExtractor,
        language::transforms::tables_to_egraph,
        p4::{example_progs, p4ir::Table},
        rewrites::{
            domino::stateless::arith_to_alu,
            tofino::{
                stateful::conditional_assignments,
                stateless::{cmp_to_rel, lift_stateless},
            },
        },
    };

    use super::table_transformations::{multi_stage_action, seq_elim, split_table};

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
