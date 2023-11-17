use egg::{rewrite, EGraph, Id, Subst, Var};

use crate::{
    language::ir::{Mio, MioAnalysis, MioAnalysisData, MioType},
    rewrites::is_greater_eq,
};

use super::RW;

pub fn is_integer(v: Var) -> impl Fn(&mut EGraph<Mio, MioAnalysis>, Id, &Subst) -> bool {
    move |egraph, _, subst| {
        let vid = subst[v];
        match &egraph[vid].data {
            MioAnalysisData::Action(u) => match u.checked_type {
                MioType::Int | MioType::BitInt(_) => true,
                _ => false,
            },
            _ => false,
        }
    }
}

pub fn alg_simpl() -> Vec<RW> {
    vec![
        rewrite!("add-sub-convert"; "(+ ?x (neg ?y))" => "(- ?x ?y)"),
        rewrite!("sub-neg-convert"; "(- 0 ?x)" => "(neg ?x)"),
        rewrite!("add-sub-elim"; "(- (+ ?x ?y) ?y)" => "?x"),
        rewrite!("sub-conv"; "(- ?x (- ?y ?z))" => "(+ (- ?x ?y) ?z)"),
        rewrite!("add-conv"; "(+ ?x (- ?y ?z))" => "(- (+ ?x ?y) ?z)"),
        rewrite!("add-zero"; "(+ ?x 0)" => "?x"),
        rewrite!("sub-zero"; "(- ?x 0)" => "?x"),
        rewrite!("double-to-shift"; "(+ ?x ?x)" => "(bitshl ?x 1)"),
        rewrite!("shl-shr-elim"; "(bitshr (bitshl ?x ?y) ?y)" => "?x"),
        rewrite!("shl-sum"; "(bitshl ?x (+ ?y ?z))" => "(bitshl (bitshl ?x ?y) ?z)"),
        rewrite!("shr-to-zero"; "(bitshr ?x ?y)" => "0" if is_greater_eq("?y".parse().unwrap(), 32)),
        rewrite!("sub-elim"; "(- ?x ?x)" => "0"),
        rewrite!("add-comm"; "(+ ?x ?y)" => "(+ ?y ?x)"),
        rewrite!("add-assoc"; "(+ ?x (+ ?y ?z))" => "(+ (+ ?x ?y) ?z)"),
        rewrite!("add-identity"; "?x" => "(+ ?x 0)"
        if is_integer("?x".parse().unwrap())),
    ]
}

pub fn predicate_rewrites() -> Vec<RW> {
    vec![
        rewrite!("and-elim-left"; "(land ?x false)" => "false"),
        rewrite!("and-elim-right"; "(land ?x true)" => "?x"),
        rewrite!("and-comm"; "(land ?x ?y)" => "(land ?y ?x)"),
        rewrite!("and-assoc"; "(land ?x (land ?y ?z))" => "(land (land ?x ?y) ?z)"),
        rewrite!("or-elim-left"; "(lor ?x true)" => "true"),
        rewrite!("or-elim-right"; "(lor ?x false)" => "?x"),
        rewrite!("or-comm"; "(lor ?x ?y)" => "(lor ?y ?x)"),
        rewrite!("or-assoc"; "(lor ?x (lor ?y ?z))" => "(lor (lor ?x ?y) ?z)"),
        rewrite!("demorgan-and"; "(lnot (land ?x ?y))" => "(lor (lnot ?x) (lnot ?y))"),
        rewrite!("demorgan-or"; "(lnot (lor ?x ?y))" => "(land (lnot ?x) (lnot ?y))"),
        rewrite!("demorgan-converse-and"; "(land (lnot ?x) (lnot ?y))" => "(lnot (lor ?x ?y))"),
        rewrite!("demorgan-converse-or"; "(lor (lnot ?x) (lnot ?y))" => "(lnot (land ?x ?y))"),
        rewrite!("ite-collapse"; "(ite ?c1 ?t3 (ite ?c2 ?t1 ?t2))" => "(ite ?c1 ?t3 ?t1)"), // iff c1 <=> not c2
        rewrite!("ite-true"; "(ite true ?t1 ?t2)" => "?t1"),
        rewrite!("ite-false"; "(ite false ?t1 ?t2)" => "?t2"),
        rewrite!("ite-same"; "(ite ?c ?t ?t)" => "?t"),
        rewrite!("ite-intro"; "?t" => "(ite true ?t ?t)"
                if is_integer("?t".parse().unwrap())),
        rewrite!("trivial-comp"; "true" => "(= 0 0)"),
    ]
}

pub fn rel_comp_rewrites() -> Vec<RW> {
    vec![
        rewrite!("not-eq-neq"; "(!= ?x ?y)" => "(lnot (= ?x ?y))"),
        rewrite!("neq-not-eq"; "(lnot (= ?x ?y))" => "(!= ?x ?y)"),
        rewrite!("gt-lt"; "(> ?x ?y)" => "(< ?y ?x)"),
        rewrite!("lt-gt"; "(< ?x ?y)" => "(> ?y ?x)"),
        rewrite!("lt-comp-lt-0"; "(< ?x ?y)" => "(< (- ?x ?y) 0)"),
        rewrite!("gt-comp-gt-0"; "(> ?x ?y)" => "(< 0 (- ?x ?y))"),
    ]
}
