use egg::{rewrite, EGraph, Id, Rewrite, Subst, Var};

use crate::language::{
    self,
    ir::{Mio, MioAnalysis},
    utils::{get_dependency, Dependency},
};

type RW = Rewrite<language::ir::Mio, language::ir::MioAnalysis>;
type EG = EGraph<Mio, MioAnalysis>;

// pub fn waw_elim() -> RW {
//     // WAW elimination is done by
//     // 1. merge matching keys
//     // 2. merge actions
// }

fn independent_actions(a1s: Var, a2s: Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
    move |egraph, _id, subst| {
        let c1 = subst[a1s];
        let c2 = subst[a2s];
        return get_dependency(
            &egraph[c1].data.max_read,
            &egraph[c1].data.max_write,
            &egraph[c2].data.max_read,
            &egraph[c2].data.max_write,
        ) == Dependency::INDEPENDENT;
    }
}

pub fn parallelize_independent_tables() -> RW {
    return rewrite!("parallel-indep-tables";
        "(table ?p2s ?a2s (table ?p1s ?a1s ?cont))"
            =>
        "(join (table ?p1s ?a1s ?cont) (table ?p2s ?a2s ?cont))"
         if independent_actions("?a1s".parse().unwrap(),
                                "?a2s".parse().unwrap()));
}

pub fn join_flatten() -> RW {
    rewrite!("join-flatten";
            "(join ?t1 (join ?t2 ?t3))"
                =>
            "(join ?t1 ?t2 ?t3)")
}

pub fn join_properties() -> Vec<RW> {
    vec![
        rewrite!(
            "join-assoc";
            "(join ?t1 (join ?t2 ?t3))"
                =>
            "(join (join ?t1 ?t2) ?t3)"
        ),
        rewrite!(
            "join-comm";
            "(join ?t1 ?t2)"
                =>
            "(join ?t2 ?t1)"
        ),
    ]
}

mod test {
    use std::path::PathBuf;

    use egg::{AstDepth, EGraph, Extractor, RecExpr, Runner};

    use crate::{
        extractors::GreedyExtractor,
        language::ir::{Mio, MioAnalysis},
    };

    #[test]
    fn test_example() {
        let prog = "(ite (land (= f8 1) (= f9 1))
                            (table (keys (= m1 const1))
                                   (actions (list
                                                (mapsto f1
                                                        (bitxor f2 1))
                                                (mapsto f4 f3)))
                                    id
                            )
                            (table  (keys (= m3 const3))
                                    (actions
                                            (list
                                                (mapsto f6 (bitshl f7 2))))
                                    (table (keys (= m2 const2))
                                            (actions (list
                                                        (mapsto f5 (+ f5 1))))
                                            id
                                    )
                                )
                            )
                        )"
        .parse::<RecExpr<Mio>>()
        .unwrap();
        let mut rewrites = super::join_properties();
        rewrites.extend(
            [
                super::join_flatten(),
                super::parallelize_independent_tables(),
            ]
            .into_iter(),
        );
        let mut egraph = EGraph::new(MioAnalysis::default());
        let rt = egraph.add_expr(&prog);
        let runner = Runner::<Mio, MioAnalysis>::new(MioAnalysis::default());
        let runner = runner.with_egraph(egraph).run(&rewrites);
        let egraph = runner.egraph;
        egraph.dot().to_pdf(PathBuf::from("test.pdf")).unwrap();
        let extractor = Extractor::new(&egraph, GreedyExtractor);
        let (best_cost, best_expr) = extractor.find_best(rt);
        println!("best cost: {}", best_cost);
        println!("best expr: {}", best_expr.pretty(80));
    }
}
