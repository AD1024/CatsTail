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
            table_id: Var,
        }
        impl TofinoStatefulAluApplier {
            fn new(
                alu_type: &'static str,
                alu_op: &'static str,
                table_id: &'static str,
                operands: Vec<&'static str>,
            ) -> Self {
                Self {
                    alu_type,
                    alu_op,
                    table_id: table_id.parse().unwrap(),
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
                let elaborations = MioAnalysis::elaborations(egraph, eclass).clone();
                assert!(
                    elaborations.len() <= 1,
                    "conditional assignments should have at most one elaboration"
                );
                let elab_var = if elaborations.len() == 0 {
                    "tmp".to_string()
                } else {
                    elaborations.iter().cloned().next().unwrap()
                };
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
                let elaborator_id =
                    egraph.add(Mio::Elaborate([subst[self.table_id], elab_id, salu_id]));
                let f = egraph.union(elaborator_id, eclass);
                if f {
                    vec![eclass, elaborator_id]
                } else {
                    vec![]
                }
            }
        }
        vec![rewrite!("cond-assign-to-salu";
                    "(E ?t ?v (ite ?rel ?lhs ?rhs))" =>
                    { TofinoStatefulAluApplier::new("arith-alu", "alu-ite", "?t", vec!["?rel", "?lhs", "?rhs"]) }
                if is_n_depth_mapped("?rel".parse().unwrap(), 2, Some(false))
                if is_n_depth_mapped("?lhs".parse().unwrap(), 1, Some(false))
                if is_n_depth_mapped("?rhs".parse().unwrap(), 1, Some(false)))]
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
            elaborator_conversion, lift_stateless,
            table_transformations::{lift_ite_cond, seq_elim, waw_elim},
            tofino::{stateful::conditional_assignments, stateless::cmp_to_rel},
        },
    };

    fn test_tofino_mapping(prog: Vec<Table>, filename: &'static str) -> Duration {
        let start_time = std::time::Instant::now();
        let (egraph, root) = tables_to_egraph(prog);
        let rewrites = seq_elim()
            .into_iter()
            .chain(arith_to_alu())
            .chain(conditional_assignments())
            .chain(elaborator_conversion())
            .chain(cmp_to_rel())
            // .chain(lift_stateless())
            .chain(lift_ite_cond())
            // .chain(waw_elim())
            .collect::<Vec<_>>();
        let runner = Runner::default()
            .with_egraph(egraph)
            // .with_node_limit(5_000)
            .with_time_limit(Duration::from_secs(5));
        let runner = runner.run(rewrites.iter());
        // runner.egraph.dot().to_pdf(filename).unwrap();
        let greedy_ext = GreedyExtractor::new(&runner.egraph, 1);
        let extractor = Extractor::new(&runner.egraph, greedy_ext);
        let (best_cost, best) = extractor.find_best(root);
        let end_time = std::time::Instant::now();
        println!("best cost: {}", best_cost);
        println!("best: {}", best.pretty(80));
        println!("time: {:?}", end_time - start_time);
        end_time - start_time
    }

    fn run_n_times(n: usize, f: impl Fn() -> Duration) -> Duration {
        let mut total = Duration::new(0, 0);
        for _ in 0..n {
            total += f();
        }
        total / n as u32
    }

    #[test]
    fn test_tofino_rcp() {
        let test_fn = || test_tofino_mapping(example_progs::rcp(), "rcp.pdf");
        let avg_time = run_n_times(1, test_fn);
        println!("RCP avg time: {:?}", avg_time);
    }

    #[test]
    fn test_tofino_sampling() {
        let test_fn = || test_tofino_mapping(example_progs::sampling(), "sampling.pdf");
        let avg_time = run_n_times(1, test_fn);
        println!("sampling avg time: {:?}", avg_time);
    }

    #[test]
    fn test_tofino_blue_increase() {
        let test_fn = || test_tofino_mapping(example_progs::blue_increase(), "blue_increase.pdf");
        let avg_time = run_n_times(1, test_fn);
        println!("blue increase avg time: {:?}", avg_time);
    }

    #[test]
    fn test_tofino_flowlet() {
        let test_fn = || test_tofino_mapping(example_progs::flowlet(), "flowlet.pdf");
        let avg_time = run_n_times(1, test_fn);
        println!("flowlet avg time: {:?}", avg_time);
    }

    #[test]
    fn test_tofino_marple_nmo() {
        let test_fn = || test_tofino_mapping(example_progs::marple_nmo(), "marple_nmo.pdf");
        let avg_time = run_n_times(1, test_fn);
        println!("marple nmo avg time: {:?}", avg_time);
    }

    #[test]
    fn test_tofino_marple_new() {
        let test_fn = || test_tofino_mapping(example_progs::marple_new_flow(), "marple_new.pdf");
        let avg_time = run_n_times(1, test_fn);
        println!("marple new avg time: {:?}", avg_time);
    }

    #[test]
    fn test_tofino_waw_elim() {
        test_tofino_mapping(example_progs::cetus_waw(), "waw_elim.pdf");
    }
}
