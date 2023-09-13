pub mod p4ir {
    use egg::Id;

    use crate::language::ir::Mio;

    #[derive(Debug, Clone)]
    pub enum BinOps {
        Add,
        Sub,
        Mul,
        Div,
        Shl,
        Shr,
        BitAnd,
        BitOr,
        BitXor,
        Eq,
        Ne,
        Lt,
        Le,
        Gt,
        Ge,
        And,
        Or,
        Xor,
    }

    impl BinOps {
        pub fn to_mio(&self, lhs: Id, rhs: Id) -> Mio {
            match self {
                Self::Add => Mio::Add([lhs, rhs]),
                Self::Sub => Mio::Sub([lhs, rhs]),
                Self::Shl => Mio::BitShl([lhs, rhs]),
                Self::Shr => Mio::BitShr([lhs, rhs]),
                Self::BitAnd => Mio::BitAnd([lhs, rhs]),
                Self::BitOr => Mio::BitOr([lhs, rhs]),
                Self::BitXor => Mio::BitXor([lhs, rhs]),
                Self::Eq => Mio::Eq([lhs, rhs]),
                Self::Ne => Mio::Neq([lhs, rhs]),
                Self::Lt => Mio::Lt([lhs, rhs]),
                Self::Le => Mio::Le([lhs, rhs]),
                Self::Gt => Mio::Gt([lhs, rhs]),
                Self::Ge => Mio::Ge([lhs, rhs]),
                Self::And => Mio::LAnd([lhs, rhs]),
                Self::Or => Mio::LOr([lhs, rhs]),
                Self::Xor => Mio::LXor([lhs, rhs]),
                _ => panic!("Not implemented"),
            }
        }
    }

    #[derive(Debug, Clone)]
    pub enum UnOps {
        Neg,
        Not,
        BitNot,
    }

    impl UnOps {
        pub fn to_mio(&self, arg: Id) -> Mio {
            match self {
                Self::Neg => Mio::Neg(arg),
                Self::Not => Mio::LNot(arg),
                Self::BitNot => Mio::BitNot(arg),
                _ => panic!("Not implemented"),
            }
        }
    }

    #[derive(Debug, Clone)]
    pub enum Expr {
        Var(String),
        Int(i32),
        Bool(bool),
        BinOpExpr(BinOps, Box<Expr>, Box<Expr>),
        UnOpExpr(UnOps, Box<Expr>),
    }

    #[derive(Debug, Clone)]
    pub enum Stmt {
        Assign(Expr, Expr),
        If(Expr, Box<Stmt>, Box<Stmt>),
        Block(Vec<Stmt>),
    }
}

pub mod macros {
    use super::p4ir::{BinOps, Expr, Stmt, UnOps};
    macro_rules! var {
        ($v:expr) => {
            Expr::Var($v.to_string())
        };
    }
    macro_rules! assign {
        ($x:expr => $y:expr) => {
            Stmt::Assign(var!($x), $y)
        };
    }
    macro_rules! ite {
        ($cond:expr, $then:expr, $else:expr) => {
            Stmt::If($cond, Box::new($then), Box::new($else))
        };
    }
    macro_rules! block {
        ($($stmt:expr),*) => {
            Stmt::Block(vec![$($stmt),*])
        };
    }
    macro_rules! and {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::And, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! or {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Or, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! not {
        ($e1:expr) => {
            Expr::UnOpExpr($crate::p4::p4ir::UnOps::Not, Box::new($e1))
        };
    }
    macro_rules! xor {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Xor, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! bitand {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr(
                $crate::p4::p4ir::BinOps::BitAnd,
                Box::new($e1),
                Box::new($e2),
            )
        };
    }
    macro_rules! bitor {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr(
                $crate::p4::p4ir::BinOps::BitOr,
                Box::new($e1),
                Box::new($e2),
            )
        };
    }
    macro_rules! bitxor {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr(
                $crate::p4::p4ir::BinOps::BitXor,
                Box::new($e1),
                Box::new($e2),
            )
        };
    }
    macro_rules! bitnot {
        (($e1:expr)) => {
            Expr::UnOpExpr($crate::p4::p4ir::UnOps::BitNot, Box::new($e1))
        };
    }
    macro_rules! neg {
        (($e1:expr)) => {
            Expr::UnOpExpr($crate::p4::p4ir::UnOps::Neg, Box::new($e1))
        };
    }
    macro_rules! add {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Add, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! sub {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Sub, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! mul {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Mul, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! div {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Div, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! shl {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Shl, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! shr {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Shr, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! eq {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Eq, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! ne {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Ne, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! lt {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Lt, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! le {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Le, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! gt {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Gt, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! ge {
        (($e1:expr), ($e2:expr)) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Ge, Box::new($e1), Box::new($e2))
        };
    }

    pub(crate) use {
        add, and, assign, bitand, bitnot, bitor, bitxor, block, div, eq, ge, gt, ite, le, lt, mul,
        ne, neg, not, or, shl, shr, sub, var, xor,
    };
}
