use egg::{rewrite, EGraph, Id, Subst, Var};

use crate::{
    language::ir::{Mio, MioAnalysis, MioAnalysisData, MioType},
    rewrites::is_greater_eq,
};

use super::RW;

pub fn is_integer(v: Var) -> impl Fn(&mut EGraph<Mio, MioAnalysis>, Id, &Subst) -> bool {
    move |egraph, _, subst| {
        match &egraph[subst[v]].nodes[0] {
            Mio::Elaborate(_) => {
                return false;
            }
            _ => (),
        }
        let vid = subst[v];
        // if MioAnalysis::get_symbol(egraph, vid).is_some() {
        //     return true;
        // }
        match &egraph[vid].data {
            MioAnalysisData::Action(u) => match u.checked_type {
                MioType::Int | MioType::BitInt(_) => true,
                _ => false,
            },
            _ => false,
        }
    }
}

#[allow(dead_code)]
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

#[allow(dead_code)]
pub fn predicate_rewrites() -> Vec<RW> {
    vec![
        rewrite!("and-elim-left"; "(land ?x false)" => "false"),
        rewrite!("and-elim-right"; "(land ?x true)" => "?x"),
        rewrite!("and-comm"; "(land ?x ?y)" => "(land ?y ?x)"),
        rewrite!("and-assoc"; "(land ?x (land ?y ?z))" => "(land (land ?x ?y) ?z)"),
        rewrite!("and-assoc-rev"; "(land (land ?x ?y) ?z)" => "(land ?x (land ?y ?z))"),
        rewrite!("or-elim-left"; "(lor ?x true)" => "true"),
        rewrite!("or-elim-right"; "(lor ?x false)" => "?x"),
        rewrite!("or-comm"; "(lor ?x ?y)" => "(lor ?y ?x)"),
        rewrite!("or-assoc"; "(lor ?x (lor ?y ?z))" => "(lor (lor ?x ?y) ?z)"),
        rewrite!("demorgan-and"; "(lnot (land ?x ?y))" => "(lor (lnot ?x) (lnot ?y))"),
        rewrite!("demorgan-or"; "(lnot (lor ?x ?y))" => "(land (lnot ?x) (lnot ?y))"),
        rewrite!("demorgan-converse-and"; "(land (lnot ?x) (lnot ?y))" => "(lnot (lor ?x ?y))"),
        rewrite!("demorgan-converse-or"; "(lor (lnot ?x) (lnot ?y))" => "(lnot (land ?x ?y))"),
        // rewrite!("ite-collapse"; "(ite ?c1 ?t3 (ite ?c2 ?t1 ?t2))" => "(ite ?c1 ?t3 ?t1)"), // iff c1 <=> not c2
        rewrite!("ite-true"; "(ite true ?t1 ?t2)" => "?t1"),
        rewrite!("ite-false"; "(ite false ?t1 ?t2)" => "?t2"),
        rewrite!("ite-same"; "(ite ?c ?t ?t)" => "?t"),
        rewrite!("ite-combine"; "(ite ?c1 (ite ?c2 ?b1 ?d) ?d)" => "(ite (land ?c1 ?c2) ?b1 ?d)"),
        rewrite!("ite-intro"; "?t" => "(ite true ?t ?t)"
                if is_integer("?t".parse().unwrap())),
        rewrite!("trivial-comp"; "true" => "(= 0 0)"),
        rewrite!("true-not-false"; "(lnot false)" => "true"),
        rewrite!("false-not-true"; "(lnot true)" => "false"),
        rewrite!("not-not"; "(lnot (lnot ?x))" => "?x"),
        rewrite!("ite-reversed-cond"; "(ite ?c ?b1 ?b2)" => "(ite (lnot ?c) ?b2 ?b1)"),
    ]
}

pub fn rel_comp_rewrites() -> Vec<RW> {
    vec![
        rewrite!("not-eq-neq"; "(!= ?x ?y)" => "(lnot (= ?x ?y))"),
        rewrite!("neq-not-eq"; "(lnot (= ?x ?y))" => "(!= ?x ?y)"),
        rewrite!("not-neq-neg"; "(lnot (!= ?x ?y))" => "(= ?x ?y)"),
        rewrite!("not-lt-ge"; "(lnot (< ?x ?y))" => "(>= ?x ?y)"),
        rewrite!("gt-lt"; "(> ?x ?y)" => "(< ?y ?x)"),
        rewrite!("lt-gt"; "(< ?x ?y)" => "(> ?y ?x)"),
        rewrite!("lt-to-zero-cmp"; "(< ?x ?y)" => "(< 0 (- ?x ?y))"),
        rewrite!("lt-comp-lt-0"; "(< ?x ?y)" => "(< (- ?x ?y) 0)"),
        rewrite!("gt-comp-gt-0"; "(> ?x ?y)" => "(< 0 (- ?x ?y))"),
        rewrite!("lt-comp-sub"; "(< (- ?x ?y) ?z)" => "(> ?y (- ?x ?z))"),
        rewrite!("lt-to-zero-check"; "(< ?x ?y)" => "(< (- ?x ?y) 0)"
                if is_integer("?x".parse().unwrap())
                if is_integer("?y".parse().unwrap())),
        rewrite!("eq-to-zero-check"; "(= ?x ?y)" => "(!= 0 (- ?x ?y))"
                if is_integer("?x".parse().unwrap())
                if is_integer("?y".parse().unwrap())),
        rewrite!("neq-to-zero-check"; "(!= ?x ?y)" => "(!= (- ?x ?y) 0)"
                if is_integer("?x".parse().unwrap())
                if is_integer("?y".parse().unwrap())),
    ]
}
