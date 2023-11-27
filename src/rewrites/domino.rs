pub mod stateless {

    use egg::{rewrite, EGraph, Id, Pattern, Searcher, Subst, Var};

    use crate::{
        language::ir::{Mio, MioAnalysis},
        rewrites::{is_mapped, AluApplier, RW},
    };

    pub fn arith_to_alu() -> Vec<RW> {
        // https://github.com/CaT-mindepth/minDepthCompiler/blob/weighted-grammar-parallel-final/src/grammars/stateless_domino/stateless_new.sk
        fn neq_0_check_match(x: Var) -> impl Fn(&mut EGraph<Mio, MioAnalysis>, Id, &Subst) -> bool {
            move |egraph, _, subst| {
                let pattern = "(!= ?x 0)";
                let pattern = pattern.parse::<Pattern<Mio>>().unwrap();
                egraph.rebuild();
                pattern.search_eclass(egraph, subst[x]).is_some()
            }
        }
        vec![
            rewrite!("domino-add";
                "(+ ?x ?y)" => { AluApplier::new("arith-alu", "alu-add", vec!["?x", "?y"]) }
                if is_mapped("?x".parse().unwrap(), Some(false))
                if is_mapped("?y".parse().unwrap(), Some(false))),
            rewrite!("domino-sub";
                "(- ?x ?y)" => { AluApplier::new("arith-alu", "alu-sub", vec!["?x", "?y"]) }
                if is_mapped("?x".parse().unwrap(), Some(false))
                if is_mapped("?y".parse().unwrap(), Some(false))),
            rewrite!("domino-neq";
                "(!= ?x ?y)" => { AluApplier::new("rel-alu", "alu-neq", vec!["?x", "?y"]) }
                if is_mapped("?x".parse().unwrap(), None)
                if is_mapped("?y".parse().unwrap(), None)),
            rewrite!("domino-eq";
                "(= ?x ?y)" => { AluApplier::new("rel-alu", "alu-eq", vec!["?x", "?y"]) }
                if is_mapped("?x".parse().unwrap(), None)
                if is_mapped("?y".parse().unwrap(), None)),
            rewrite!("domino-geq";
                "(>= ?x ?y)" => { AluApplier::new("rel-alu", "alu-ge", vec!["?x", "?y"]) }
                if is_mapped("?x".parse().unwrap(), None)
                if is_mapped("?y".parse().unwrap(), None)),
            rewrite!("domino-lt";
                "(< ?x ?y)" => { AluApplier::new("rel-alu", "alu-lt", vec!["?x", "?y"]) }
                if is_mapped("?x".parse().unwrap(), None)
                if is_mapped("?y".parse().unwrap(), None)),
            // rewrite!("domino-ite-0";
            //     "(ite ?c ?x ?y)" => { AluApplier::new("arith-alu", "alu-ite", vec!["?c", "?x", "?y"]) }
            //     if neq_0_check_match("?c".parse().unwrap())),
            rewrite!("domino-neq-0-or";
                "(lor ?x ?y)" => { AluApplier::new("rel-alu", "alu-or", vec!["?x", "?y"]) }
                if neq_0_check_match("?x".parse().unwrap())
                if neq_0_check_match("?y".parse().unwrap())),
            rewrite!("domino-neq-0-and";
                "(land ?x ?y)" => { AluApplier::new("rel-alu", "alu-or", vec!["?x", "?y"]) }
                if neq_0_check_match("?x".parse().unwrap())
                if neq_0_check_match("?y".parse().unwrap())),
        ]
    }
}

pub mod stateful {
    use std::collections::HashSet;

    use egg::{rewrite, Applier, EGraph, Id, Pattern, Searcher, Subst, Var};

    use crate::{
        language::ir::{Constant, Mio, MioAnalysis, MioType},
        rewrites::{constains_leaf, is_mapped, is_n_depth_mapped, same_read, RW},
    };

    fn check_relops(
        v: Var,
        operators: Vec<&'static str>,
    ) -> impl Fn(&mut EGraph<Mio, MioAnalysis>, Id, &Subst) -> bool {
        move |egraph, _, subst| {
            let vid = subst[v];
            let operators = operators
                .iter()
                .map(|op| Mio::RelAluOps(op.parse().unwrap()))
                .collect::<Vec<Mio>>();
            return operators.iter().any(|x| x.eq(&egraph[vid].nodes[0]));
        }
    }

    fn check_arith_alu(v: Var) -> impl Fn(&mut EGraph<Mio, MioAnalysis>, Id, &Subst) -> bool {
        move |egraph, _, subst| {
            let add_pattern = "(arith-alu alu-add ?x ?y)".parse::<Pattern<Mio>>().unwrap();
            let sub_pattern = "(arith-alu alu-sub ?x ?y)".parse::<Pattern<Mio>>().unwrap();
            let vid = subst[v];
            if MioAnalysis::has_leaf(egraph, vid) {
                // constant / variable is ok
                return true;
            }
            egraph.rebuild();
            if let Some(matches) = add_pattern
                .search_eclass(egraph, vid)
                .or(sub_pattern.search_eclass(egraph, vid))
            {
                // Check whether ?x and ?y are leaves
                let var_x = "?x".parse().unwrap();
                let var_y = "?y".parse().unwrap();
                return matches.substs.iter().any(|subst| {
                    MioAnalysis::has_leaf(egraph, subst[var_x])
                        && MioAnalysis::has_leaf(egraph, subst[var_y])
                });
            } else {
                return false;
            }
        }
    }

    pub fn bool_alu_rewrites() -> Vec<RW> {
        vec![
            rewrite!("domino-stateful-bool-alu-1";
                "(lnot (lor ?x ?y))" => "(rel-alu alu-not (rel-alu alu-or ?x ?y))"
                if constains_leaf("?x".parse().unwrap())
                if constains_leaf("?y".parse().unwrap())),
            rewrite!("domino-stateful-bool-alu-2";
                "(land (lnot ?x) ?y)" => "(rel-alu alu-and (rel-alu alu-not ?x) ?y)"
                if constains_leaf("?x".parse().unwrap())
                if constains_leaf("?y".parse().unwrap())),
            rewrite!("domino-stateful-bool-alu-3";
                "(lnot ?x)" => "(rel-alu alu-not ?x)"
                if constains_leaf("?x".parse().unwrap())),
            rewrite!("domino-stateful-bool-alu-and";
                "(land ?x ?y)" => "(rel-alu alu-and ?x ?y)"
                if constains_leaf("?x".parse().unwrap())
                if constains_leaf("?y".parse().unwrap())),
            rewrite!("domino-stateful-bool-alu-or";
                "(lor ?x ?y)" => "(rel-alu alu-or ?x ?y)"
                if constains_leaf("?x".parse().unwrap())
                if constains_leaf("?y".parse().unwrap())),
            rewrite!("domino-stateful-bool-alu-4";
                "(lnot (land ?x ?y))" => "(rel-alu alu-not (rel-alu alu-and ?x ?y))"
                if constains_leaf("?x".parse().unwrap())
                if constains_leaf("?y".parse().unwrap())),
            rewrite!("domino-stateful-bool-alu-5";
                "(lor (lnot ?x) ?y)" => "(rel-alu alu-or (rel-alu alu-not ?x) ?y)"
                if constains_leaf("?x".parse().unwrap())
                if constains_leaf("?y".parse().unwrap())),
        ]
    }

    pub fn global_or_0(v: Var) -> impl Fn(&mut EGraph<Mio, MioAnalysis>, Id, &Subst) -> bool {
        move |egraph, _, subst| {
            let vid = subst[v];
            if MioAnalysis::get_constant(egraph, vid).is_some() {
                return true;
            }
            let pattern = "(arith-alu alu-global ?x)".parse::<Pattern<Mio>>().unwrap();
            egraph.rebuild();
            return pattern.search_eclass(egraph, vid).is_some();
        }
    }

    pub fn same_if_is_var(
        v1: Var,
        v2: Var,
    ) -> impl Fn(&mut EGraph<Mio, MioAnalysis>, Id, &Subst) -> bool {
        move |egraph, _, subst| {
            let vid1 = subst[v1];
            let vid2 = subst[v2];
            let pattern = "(arith-alu alu-global ?x)".parse::<Pattern<Mio>>().unwrap();
            egraph.rebuild();
            if let Some(m1) = pattern.search_eclass(egraph, vid1) {
                if let Some(m2) = pattern.search_eclass(egraph, vid2) {
                    let var_x = "?x".parse().unwrap();
                    return m1.substs[0][var_x] == m2.substs[0][var_x];
                }
            }
            // either v1 or v2 is not a global variable
            return true;
        }
    }

    pub fn check_read_limit(
        vars: Vec<&'static str>,
        phv_field_limit: usize,
        global_reg_limit: usize,
    ) -> impl Fn(&mut EGraph<Mio, MioAnalysis>, Id, &Subst) -> bool {
        move |egraph, _, subst| {
            let mut local_read = HashSet::new();
            let mut global_read = HashSet::new();
            for v in vars.iter() {
                let vid = subst[v.parse().unwrap()];
                let read_set = MioAnalysis::read_set(egraph, vid);
                global_read.extend(read_set.iter().filter(|x| x.starts_with("global.")));
                local_read.extend(read_set.iter().filter(|x| !x.starts_with("global.")));
            }
            return local_read.len() <= phv_field_limit && global_read.len() <= global_reg_limit;
        }
    }

    pub fn if_else_raw() -> Vec<RW> {
        // https://github.com/CaT-mindepth/minDepthCompiler/blob/weighted-grammar-parallel-final/src/grammars/stateful_domino/if_else_raw.sk
        struct IfElseApplier {
            op: Var,
            r: Var,
            rhs: Var,
            x: Var,
            y: Var,
            z: Var,
            w: Var,
        }
        impl Applier<Mio, MioAnalysis> for IfElseApplier {
            fn apply_one(
                &self,
                egraph: &mut EGraph<Mio, MioAnalysis>,
                eclass: Id,
                subst: &Subst,
                searcher_ast: Option<&egg::PatternAst<Mio>>,
                rule_name: egg::Symbol,
            ) -> Vec<Id> {
                let elaborations = MioAnalysis::elaborations(egraph, eclass);
                let evar = if elaborations.len() == 0 {
                    "tmp".to_string()
                } else {
                    format!(
                        "(arith-alu alu-global {})",
                        elaborations.iter().next().unwrap().clone()
                    )
                };
                let pattern = format!(
                    "(E ?t ?v (stateful-alu alu-ite {}
                    (rel-alu {} {} {})
                    (arith-alu alu-add {} {})
                    (arith-alu alu-add {} {})))",
                    evar, self.op, self.r, self.rhs, self.z, self.x, self.w, self.y
                );
                return pattern.parse::<Pattern<Mio>>().unwrap().apply_one(
                    egraph,
                    eclass,
                    subst,
                    searcher_ast,
                    rule_name,
                );
            }
        }
        vec![rewrite!("domino-if-else-raw";
                "(E ?t ?v (ite
                    (rel-alu ?op ?r ?rhs)
                    (+ ?z ?x)
                    (+ ?w ?y)
                ))" => { IfElseApplier {
                    op: "?op".parse().unwrap(),
                    r: "?r".parse().unwrap(),
                    rhs: "?rhs".parse().unwrap(),
                    x: "?x".parse().unwrap(),
                    y: "?y".parse().unwrap(),
                    z: "?z".parse().unwrap(),
                    w: "?w".parse().unwrap(),
                } }
                if check_relops("?op".parse().unwrap(), vec!["alu-eq", "alu-neq", "alu-gt", "alu-lt"])
                // if global_or_0("?r".parse().unwrap())
                // if global_or_0("?z".parse().unwrap())
                // if global_or_0("?w".parse().unwrap())
                // if same_if_is_var("?r".parse().unwrap(), "?z".parse().unwrap())
                // if same_if_is_var("?r".parse().unwrap(), "?w".parse().unwrap())
                if constains_leaf("?rhs".parse().unwrap())
                if constains_leaf("?x".parse().unwrap())
                if constains_leaf("?y".parse().unwrap()))]
    }

    pub fn nested_ifs() -> Vec<RW> {
        // https://github.com/CaT-mindepth/minDepthCompiler/blob/weighted-grammar-parallel-final/src/grammars/stateful_domino/nested_ifs.sk
        struct NestedIfsApplier;
        impl Applier<Mio, MioAnalysis> for NestedIfsApplier {
            fn apply_one(
                &self,
                egraph: &mut EGraph<Mio, MioAnalysis>,
                eclass: Id,
                subst: &Subst,
                searcher_ast: Option<&egg::PatternAst<Mio>>,
                rule_name: egg::Symbol,
            ) -> Vec<Id> {
                // check conditions
                let stateless_read_violation =
                    |v: Id| MioAnalysis::stateless_read_count(egraph, v) > 1;
                let c1 = subst["?c1".parse().unwrap()];
                let c2 = subst["?c2".parse().unwrap()];
                let c3 = subst["?c3".parse().unwrap()];
                if MioAnalysis::stateful_read_count(egraph, c1)
                    + MioAnalysis::stateful_read_count(egraph, c2)
                    + MioAnalysis::stateful_read_count(egraph, c3)
                    > 1
                {
                    return vec![];
                }
                let b1 = subst["?b1".parse().unwrap()];
                let b2 = subst["?b2".parse().unwrap()];
                let b3 = subst["?b3".parse().unwrap()];
                let b4 = subst["?b4".parse().unwrap()];
                if MioAnalysis::stateful_read_count(egraph, b1)
                    + MioAnalysis::stateful_read_count(egraph, b2)
                    + MioAnalysis::stateful_read_count(egraph, b3)
                    + MioAnalysis::stateful_read_count(egraph, b4)
                    > 1
                {
                    return vec![];
                }
                if [b1, b2, b3, b4, c1, c2, c3]
                    .into_iter()
                    .any(stateless_read_violation)
                {
                    return vec![];
                }
                let elaborations = MioAnalysis::elaborations(egraph, eclass);
                let evar = if elaborations.len() == 0 {
                    "tmp".to_string()
                } else {
                    if MioAnalysis::has_stateful_elaboration(egraph, eclass) {
                        format!(
                            "(arith-alu alu-global {})",
                            elaborations.iter().next().unwrap().clone()
                        )
                    } else {
                        format!("{}", elaborations.iter().next().unwrap().clone())
                    }
                };
                let pattern = format!(
                    "(E ?t ?v (stateful-alu alu-ite {}
                        ?c1
                        (stateful-alu alu-ite tmp
                            ?c2
                            ?b1
                            ?b2
                        )
                        (stateful-alu alu-ite tmp
                            ?c3
                            ?b3
                            ?b4
                        )
                ))",
                    evar,
                );
                return pattern.parse::<Pattern<Mio>>().unwrap().apply_one(
                    egraph,
                    eclass,
                    subst,
                    searcher_ast,
                    rule_name,
                );
            }
        }
        vec![rewrite!("domino-stateful-nested-ifs";
                "(E ?t ?v (ite
                    ?c1
                    (ite
                        ?c2
                        ?b1
                        ?b2
                    )
                    (ite
                        ?c3
                        ?b3
                        ?b4
                    )
                ))" => { NestedIfsApplier {} }
            if is_n_depth_mapped("?b1".parse().unwrap(), 1, None)
            if is_n_depth_mapped("?b2".parse().unwrap(), 1, None)
            if is_n_depth_mapped("?b3".parse().unwrap(), 1, None)
            if is_n_depth_mapped("?b4".parse().unwrap(), 1, None)
            if is_n_depth_mapped("?c1".parse().unwrap(), 1, None)
            if is_n_depth_mapped("?c2".parse().unwrap(), 1, None)
            if is_n_depth_mapped("?c3".parse().unwrap(), 1, None)
        )]
    }

    pub fn pred_raw() -> Vec<RW> {
        struct PredRawApplier {
            op: Var,
            r: Var,
            rhs: Var,
            r1: Var,
            x: Var,
            g: Var,
        }
        impl Applier<Mio, MioAnalysis> for PredRawApplier {
            fn apply_one(
                &self,
                egraph: &mut EGraph<Mio, MioAnalysis>,
                eclass: Id,
                subst: &Subst,
                searcher_ast: Option<&egg::PatternAst<Mio>>,
                rule_name: egg::Symbol,
            ) -> Vec<Id> {
                let elaborations = MioAnalysis::elaborations(egraph, eclass);
                let evar = if elaborations.len() == 0 {
                    "tmp".to_string()
                } else {
                    elaborations.iter().next().unwrap().clone()
                };
                let pattern = format!(
                    "(E ?t ?v (stateful-alu alu-ite (arith-alu alu-global {})
                        (rel-alu {} {} {})
                        (arith-alu alu-add {} {})
                        (arith-alu alu-global {})
                    ))",
                    evar, self.op, self.r, self.rhs, self.r1, self.x, self.g
                );
                return pattern.parse::<Pattern<Mio>>().unwrap().apply_one(
                    egraph,
                    eclass,
                    subst,
                    searcher_ast,
                    rule_name,
                );
            }
        }
        vec![
            rewrite!("domino-stateful-pred-raw";
            "(E ?t ?v (ite
                    (rel-alu ?op ?r ?rhs)
                    (+ ?r1 ?x)
                    (arith-alu alu-global ?g)
                ))" => { PredRawApplier {
                op: "?op".parse().unwrap(),
                r: "?r".parse().unwrap(),
                rhs: "?rhs".parse().unwrap(),
                r1: "?r1".parse().unwrap(),
                x: "?x".parse().unwrap(),
                g: "?g".parse().unwrap(),
            } }
            if check_relops("?op".parse().unwrap(), vec!["alu-eq", "alu-neq", "alu-gt", "alu-lt"])
            if global_or_0("?r".parse().unwrap())
            if global_or_0("?r1".parse().unwrap())
            if same_if_is_var("?r".parse().unwrap(), "?r1".parse().unwrap())
            if constains_leaf("?x".parse().unwrap())),
            rewrite!("domino-stateful-pred-raw-stateful";
            "(ite
                    (rel-alu ?op ?r ?rhs)
                    (stateful-alu alu-add ?dst ?r1 ?x)
                    (arith-alu alu-global ?g)
                )" => { PredRawApplier {
                op: "?op".parse().unwrap(),
                r: "?r".parse().unwrap(),
                rhs: "?rhs".parse().unwrap(),
                r1: "?r1".parse().unwrap(),
                x: "?x".parse().unwrap(),
                g: "?g".parse().unwrap(),
            } }
            if check_relops("?op".parse().unwrap(), vec!["alu-eq", "alu-neq", "alu-gt", "alu-lt"])
            if global_or_0("?r".parse().unwrap())
            if global_or_0("?r1".parse().unwrap())
            // if same_if_is_var("?r".parse().unwrap(), "?r1".parse().unwrap())
            if constains_leaf("?x".parse().unwrap())),
        ]
    }

    pub fn stateful_ite_simpl() -> Vec<RW> {
        struct SAluIteSimplApplier {
            comp: Var,
        }
        impl Applier<Mio, MioAnalysis> for SAluIteSimplApplier {
            fn apply_one(
                &self,
                egraph: &mut EGraph<Mio, MioAnalysis>,
                eclass: Id,
                subst: &Subst,
                searcher_ast: Option<&egg::PatternAst<Mio>>,
                rule_name: egg::Symbol,
            ) -> Vec<Id> {
                let comp_id = subst[self.comp];
                if let Ok((_op_name, args)) = MioAnalysis::decompose_alu_ops(egraph, comp_id) {
                    let vid = subst["?v".parse().unwrap()];
                    if let Ok(op_id) = MioAnalysis::get_alu_op_id(egraph, comp_id) {
                        let salu_id = egraph.add(Mio::SAlu(
                            vec![op_id, vid]
                                .into_iter()
                                .chain(args.into_iter())
                                .collect(),
                        ));
                        egraph.union(eclass, salu_id);
                        return vec![salu_id];
                    } else {
                        vec![]
                    }
                } else {
                    vec![]
                }
            }
        }
        vec![
            rewrite!("stateful-ite-simpl"; "(stateful-alu alu-ite ?v true ?t1 ?t2)"
            => {
                SAluIteSimplApplier {
                    comp: "?t1".parse().unwrap()
                }
            }),
            rewrite!("stateful-ite-same-branch-simpl";
            "(stateful-alu alu-ite ?v ?c ?t1 ?t1)" => {
                SAluIteSimplApplier {
                    comp: "?t1".parse().unwrap()
                }
            }),
        ]
    }
}

mod test {
    use std::time::Duration;

    use egg::{EGraph, Extractor, Pattern, Runner, Searcher};

    use crate::{
        extractors::GreedyExtractor,
        language::{
            ir::{Mio, MioAnalysis},
            transforms::tables_to_egraph,
        },
        p4::p4ir::Table,
        rewrites::{
            alg_simp::{alg_simpl, predicate_rewrites, rel_comp_rewrites},
            domino::stateful::{
                bool_alu_rewrites, if_else_raw, nested_ifs, pred_raw, stateful_ite_simpl,
            },
            elaborator_conversion, lift_stateless,
            table_transformations::{
                lift_ite_compare, lift_ite_cond, lift_nested_ite_cond,
                parallelize_independent_tables, seq_elim,
            },
        },
        utils::testing::run_n_times,
    };

    fn test_domino_mapping(prog: Vec<Table>, filename: &'static str) -> Duration {
        let start_time = std::time::Instant::now();
        let (egraph, root) = tables_to_egraph(prog);
        let rewrites = seq_elim()
            .into_iter()
            .chain(super::stateless::arith_to_alu())
            .chain(elaborator_conversion())
            .chain(if_else_raw())
            .chain(pred_raw())
            .chain(bool_alu_rewrites())
            .chain(nested_ifs())
            .chain(rel_comp_rewrites())
            .chain(alg_simpl())
            .chain(lift_ite_compare())
            .chain(lift_ite_cond())
            .chain(lift_nested_ite_cond())
            .chain(predicate_rewrites())
            .chain(stateful_ite_simpl())
            .collect::<Vec<_>>();
        let runner = Runner::default()
            .with_egraph(egraph)
            .with_node_limit(10_000)
            .with_time_limit(Duration::from_secs(5));
        let runner = runner.run(rewrites.iter());
        let greedy_ext = GreedyExtractor::new(&runner.egraph, 1);
        let extractor = Extractor::new(&runner.egraph, greedy_ext);
        let (best_cost, best) = extractor.find_best(root);
        let end_time = std::time::Instant::now();
        // println!("best cost: {}", best_cost);
        // println!("best: {}", best.pretty(80));
        assert!(
            best_cost < usize::MAX,
            "Cannot map the following program:\n{}",
            best.pretty(80)
        );
        println!("time: {:?}", end_time - start_time);
        end_time - start_time
    }

    #[test]
    fn test_stateful_fw() {
        let run_fn =
            || test_domino_mapping(crate::p4::example_progs::stateful_fw(), "stateful_fw.pdf");
        let avg_time = run_n_times(10, run_fn, "domino_stateful_fw.json");
        println!("stateful fw avg time: {:?}", avg_time);
    }

    #[test]
    fn test_blue_increase() {
        let run_fn = || {
            test_domino_mapping(
                crate::p4::example_progs::blue_increase(),
                "blue_increase.pdf",
            )
        };
        let avg_time = run_n_times(10, run_fn, "domino_blue_increase.json");
        println!("blue increase avg time: {:?}", avg_time);
    }

    #[test]
    fn test_domino_rcp() {
        let run_fn = || test_domino_mapping(crate::p4::example_progs::rcp(), "rcp.pdf");
        let avg_time = run_n_times(10, run_fn, "domino_rcp.json");
        println!("RCP avg time: {:?}", avg_time);
    }

    #[test]
    fn test_domino_sampling() {
        let run_fn = || test_domino_mapping(crate::p4::example_progs::sampling(), "rcp.pdf");
        let avg_time = run_n_times(10, run_fn, "domino_sampling.json");
        println!("sampling avg time: {:?}", avg_time);
    }

    #[test]
    fn test_domino_marple_flow_new() {
        let run_fn = || {
            test_domino_mapping(
                crate::p4::example_progs::marple_new_flow(),
                "marple_new_flow.pdf",
            )
        };
        let avg_time = run_n_times(10, run_fn, "domino_marple_new_flow.json");
        println!("marple new flow avg time: {:?}", avg_time);
    }

    #[test]
    fn test_domino_marple_nmo() {
        let run_fn =
            || test_domino_mapping(crate::p4::example_progs::marple_nmo(), "marple_nmo.pdf");
        let avg_time = run_n_times(10, run_fn, "domino_marple_nmo.json");
        println!("marple nmo avg time: {:?}", avg_time);
    }

    #[test]
    fn test_domino_flowlet() {
        let run_fn = || test_domino_mapping(crate::p4::example_progs::flowlet(), "flowlet.pdf");
        let avg_time = run_n_times(10, run_fn, "domino_flowlet.json");
        println!("flowlet avg time: {:?}", avg_time);
    }
}
