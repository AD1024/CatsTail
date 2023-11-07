use egg::{rewrite, Applier, EGraph, Id, Language, Pattern, Rewrite, Subst, Var};

use crate::language::{
    self,
    ir::{Constant, Mio, MioAnalysis},
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

pub fn seq_elim() -> Vec<RW> {
    // work together with table splitting
    return vec![rewrite!("seq-elim-l";
            "(seq (seq ?t1 ?t2) ?t3)" => "(seq ?t1 (seq ?t2 ?t3))")];
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

pub fn split_table(n: usize) -> Vec<RW> {
    struct SplitApplier(Var, Var, usize);
    impl Applier<Mio, MioAnalysis> for SplitApplier {
        fn apply_one(
            &self,
            egraph: &mut EGraph<Mio, MioAnalysis>,
            eclass: Id,
            subst: &Subst,
            _searcher_ast: Option<&egg::PatternAst<Mio>>,
            _rule_name: egg::Symbol,
        ) -> Vec<Id> {
            let k1s = subst[self.0];
            let a1s = subst[self.1];
            let key_reads = MioAnalysis::read_set(egraph, k1s);
            // the remaining actions must not modify the keys
            // split out at most n actions a time
            let mut remained = vec![];
            let mut split = vec![];
            let split_bound = self.2;
            let mut index = 0;
            for a in egraph[a1s].nodes[0].children() {
                if MioAnalysis::write_set(egraph, *a).is_disjoint(&key_reads) {
                    remained.push(index);
                } else {
                    if split.len() == split_bound {
                        remained.push(index);
                    } else {
                        split.push(index);
                    }
                }
                index += 1;
            }
            if split.len() == 0 {
                // all actions does not modify keys
                split = if split_bound > remained.len() {
                    vec![remained.pop().unwrap()]
                } else {
                    remained.split_off(remained.len() - split_bound)
                };
            }
            debug_assert!(split.len() + remained.len() == index);
            debug_assert!(split.len() <= split_bound);

            let actions = egraph[a1s].nodes[0].children().to_vec();
            let remaining_actions = remained.iter().map(|i| actions[*i]).collect::<Vec<_>>();
            let split_actions = split.iter().map(|i| actions[*i]).collect::<Vec<_>>();
            let lhs_action_id = egraph.add(Mio::Actions(remaining_actions));
            let rhs_action_id = egraph.add(Mio::Actions(split_actions));
            let lhs_table = egraph.add(Mio::GIte([k1s, lhs_action_id]));
            let rhs_table = egraph.add(Mio::GIte([k1s, rhs_action_id]));
            // (seq (gite ?k1s ?remaining) (gite ?k1s ?split))
            let seq_id = egraph.add(Mio::Seq([lhs_table, rhs_table]));
            egraph.union(eclass, seq_id);
            vec![eclass]
        }
    }
    return vec![rewrite!("separate-action";
            "(gite ?k1s ?a1s)" => { SplitApplier("?k1s".parse().unwrap(), "?a1s".parse().unwrap(), n) })];
}

pub fn ite_to_gite() -> RW {
    rewrite!("ite-to-gite"; "(ite ?c ?t1 ?t2)" => "(gite (keys ?c1) (actions ?t1 ?t2))")
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
        rewrite!("shl-sum"; "(bitshl ?x (+ ?y ?z)" => "(bitshl (bitshl ?x ?y) ?z)"),
        rewrite!("shr-to-zero"; "(bitshr ?x ?y)" => "0" if is_greater_eq("?y".parse().unwrap(), 32)),
        rewrite!("sub-elim"; "(- ?x ?x)" => "0"),
        rewrite!("add-comm"; "(+ ?x ?y)" => "(+ ?y ?x)"),
        rewrite!("add-assoc"; "(+ ?x (+ ?y ?z))" => "(+ (+ ?x ?y) ?z)"),
    ]
}

pub fn predicate_rewrites() -> Vec<RW> {
    vec![
        rewrite!("and-elim-left"; "(land ?x false)" => "false"),
        rewrite!("and-elim-right"; "(land ?x true)" => "?x"),
        rewrite!("and-comm"; "(land ?x ?y)" => "(land ?y ?x)"),
        rewrite!("and-assoc"; "(land ?x (land ?y ?z))" => "(land (land ?x ?y) ?z)"),
        rewrite!("ite-collapse"; "(ite ?c1 ?t3 (ite ?c2 ?t1 ?t2))" => "(ite ?c1 ?t3 ?t1)"), // iff c1 <=> not c2
        rewrite!("ite-true"; "(ite true ?t1 ?t2)" => "?t1"),
        rewrite!("ite-false"; "(ite false ?t1 ?t2)" => "?t2"),
        rewrite!("ite-same"; "(ite ?c ?t ?t)" => "?t"),
    ]
}

pub mod tofino_alus {

    use super::{rewrite, RW};

    pub fn rel_op_rewrites() -> Vec<RW> {
        vec![
            // stateful alus does not support >= or <=, we need to convert these conversions
            rewrite!("ge-conv"; "(>= ?x ?y)" => "(not (< ?x ?y))"),
            rewrite!("le-conv"; "(<= ?x ?y)" => "(not (> ?x ?y))"),
        ]
    }

    pub mod stateless {
        use super::*;

        pub fn arith_to_alu() -> Vec<RW> {
            vec![
                rewrite!("add-to-alu"; "(+ ?x ?y)" => "(arith-alu alu-add ?x ?y)"),
                rewrite!("minus-to-alu"; "(- ?x ?y)" => "(arith-alu alu-sub ?x ?y)"),
                rewrite!("ite-to-max"; "(ite (> ?x ?y) ?x ?y)" => "(arith-alu alu-max ?x ?y)"),
                rewrite!("ite-to-min"; "(ite (< ?x ?y) ?x ?y)" => "(arith-alu alu-min ?x ?y)"),
            ]
        }
    }

    pub mod stateful {
        use super::*;
        pub fn conditional_assignments() -> Vec<RW> {
            vec![
                rewrite!("cond-assign-gt";
                    "(ite (> ?v1 ?v2) (arith-alu ?op1 ?x1 ?y1) (arith-alu ?op2 ?x2 ?y2))"
                        => "(salu (rel-alu alu-gt ?v1 ?v2) (arith-alu ?op1 ?x1 ?y1) (arith-alu ?op2 ?x2 ?y2))"),
                rewrite!("cond-assign-lt";
                    "(ite (< ?v1 ?v2) (arith-alu ?op1 ?x1 ?y1) (arith-alu ?op2 ?x2 ?y2))"
                        => "(salu (rel-alu alu-lt ?v1 ?v2) (arith-alu ?op1 ?x1 ?y1) (arith-alu ?op2 ?x2 ?y2))"),
                rewrite!("cond-assign-eq";
                    "(ite (= ?v1 ?v2) (arith-alu ?op1 ?x1 ?y1) (arith-alu ?op2 ?x2 ?y2))"
                        => "(salu (rel-alu alu-eq ?v1 ?v2) (arith-alu ?op1 ?x1 ?y1) (arith-alu ?op2 ?x2 ?y2))"),
            ]
        }
    }
}
