pub mod stateless {
    use egg::rewrite;

    use crate::rewrites::{is_mapped, AluApplier, RW};

    pub fn arith_to_alu() -> Vec<RW> {
        // https://github.com/CaT-mindepth/minDepthCompiler/blob/weighted-grammar-parallel-final/src/grammars/stateless_domino/stateless_new.sk
        vec![
            rewrite!("domino-add";
                "(+ ?x ?y)" => { AluApplier::new("arith-alu", "alu-add", vec!["?x", "?y"]) }
                if is_mapped("?x".parse().unwrap(), None)
                if is_mapped("?y".parse().unwrap(), None)),
            rewrite!("domino-sub";
                "(- ?x ?y)" => { AluApplier::new("arith-alu", "alu-sub", vec!["?x", "?y"]) }
                if is_mapped("?x".parse().unwrap(), None)
                if is_mapped("?y".parse().unwrap(), None)),
            rewrite!("domino-neq";
                "(!= ?x ?y)" => { AluApplier::new("rel-alu", "alu-neq", vec!["?x", "?y"]) }
                if is_mapped("?x".parse().unwrap(), None)
                if is_mapped("?y".parse().unwrap(), None)),
            rewrite!("domino-neq";
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
        ]
    }
}
