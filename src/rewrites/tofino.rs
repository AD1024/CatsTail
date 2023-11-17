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

mod test {
    use std::time::Duration;

    use egg::{Extractor, Runner};

    use crate::{
        extractors::GreedyExtractor,
        language::transforms::tables_to_egraph,
        p4::{example_progs, p4ir::Table},
        rewrites::{
            domino::stateless::arith_to_alu,
            lift_stateless,
            table_transformations::{multi_stage_action, seq_elim, split_table},
            tofino::{stateful::conditional_assignments, stateless::cmp_to_rel},
        },
    };

    fn test_tofino_mapping(prog: Vec<Table>, filename: &'static str) {
        let (egraph, root) = tables_to_egraph(prog);
        let rewrites = seq_elim()
            .into_iter()
            .chain(split_table(1).into_iter())
            .chain(arith_to_alu().into_iter())
            .chain(multi_stage_action(2).into_iter())
            .chain(conditional_assignments().into_iter())
            .chain(cmp_to_rel().into_iter())
            .chain(lift_stateless())
            .collect::<Vec<_>>();
        let runner = Runner::default()
            .with_egraph(egraph)
            // .with_node_limit(5_000)
            .with_time_limit(Duration::from_secs(10));
        let runner = runner.run(rewrites.iter());
        runner.egraph.dot().to_pdf(filename).unwrap();
        let greedy_ext = GreedyExtractor {
            egraph: &runner.egraph,
            stateful_update_limit: 2,
            stateless_update_limit: 1,
            effect_disjoint: false,
        };
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

    #[test]
    fn test_tofino_flowlet() {
        test_tofino_mapping(example_progs::flowlet(), "flowlet.pdf");
    }

    #[test]
    fn test_tofino_marple_nmo() {
        test_tofino_mapping(example_progs::marple_nmo(), "marple_nmo.pdf");
    }

    #[test]
    fn test_tofino_marple_new() {
        test_tofino_mapping(example_progs::marple_new_flow(), "marple_nmo.pdf");
    }
}
