pub mod p4ir {
    use std::{collections::HashMap, rc::Rc};

    use egg::{Id, RecExpr};

    use crate::{
        language::{
            ir::{Constant, Mio},
            utils::interp_recexpr,
        },
        utils::RegionedMap,
    };

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

    impl Expr {
        fn to_mio_helper(expr: &Self, result: &mut RecExpr<Mio>) -> Id {
            match expr {
                Expr::Int(i) => result.add(Mio::Constant((*i).into())),
                Expr::Bool(b) => result.add(Mio::Constant((*b).into())),
                Expr::Var(v) => result.add(Mio::Symbol(v.clone())),
                Expr::BinOpExpr(op, lhs, rhs) => {
                    let lhs = Self::to_mio_helper(lhs, result);
                    let rhs = Self::to_mio_helper(rhs, result);
                    result.add(op.to_mio(lhs, rhs))
                }
                Expr::UnOpExpr(op, arg) => {
                    let arg = Self::to_mio_helper(arg, result);
                    result.add(op.to_mio(arg))
                }
            }
        }
        pub fn to_recexpr(expr: &Self) -> RecExpr<Mio> {
            let mut result = RecExpr::default();
            Self::to_mio_helper(expr, &mut result);
            result
        }
    }

    #[derive(Debug, Clone)]
    pub enum Stmt {
        Assign(Expr, Expr),
        If(Expr, Box<Stmt>, Box<Stmt>),
        Block(Vec<Stmt>),
        Read(String, String),
        Write(String, Expr),
    }

    pub fn interp(stmt: &Stmt, ctx: &mut HashMap<String, Mio>) {
        match stmt {
            Stmt::Block(stmts) => {
                for stmt in stmts {
                    interp(stmt, ctx);
                }
            }
            Stmt::If(cond, lb, rb) => {
                let cond = interp_recexpr(&Expr::to_recexpr(cond), ctx);
                if let Mio::Constant(Constant::Bool(cond)) = cond {
                    if cond {
                        interp(lb, ctx);
                    } else {
                        interp(rb, ctx);
                    }
                } else {
                    panic!("Condition is not a boolean");
                }
            }
            Stmt::Assign(field, value) => {
                let value = interp_recexpr(&Expr::to_recexpr(value), ctx);
                if let Expr::Var(field) = field {
                    ctx.insert(field.clone(), value);
                } else {
                    panic!("LHS of assignment is not a variable");
                }
            }
            Stmt::Read(from, to) => {
                if ctx.contains_key(from) {
                    let val = ctx.get(from).unwrap().clone();
                } else {
                    ctx.insert(to.clone(), Mio::Constant(Constant::Int(0)));
                }
            }
            Stmt::Write(gvar, expr) => {
                let value = interp_recexpr(&Expr::to_recexpr(expr), ctx);
                ctx.insert(gvar.clone(), value);
            }
        }
    }

    #[derive(Debug, Clone)]
    pub struct Table {
        pub name: String,
        pub keys: Vec<String>,
        pub actions: HashMap<String, Stmt>,
    }

    impl Table {
        pub fn new(name: String, keys: Vec<String>) -> Self {
            Self {
                name,
                keys,
                actions: HashMap::new(),
            }
        }

        pub fn add_action(&mut self, name: String, action: Stmt) {
            self.actions.insert(name, action);
        }
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
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Sub, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! mul {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Mul, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! div {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Div, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! shl {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Shl, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! shr {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Shr, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! eq {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Eq, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! ne {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Ne, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! lt {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Lt, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! le {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Le, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! gt {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Gt, Box::new($e1), Box::new($e2))
        };
    }
    macro_rules! ge {
        ($e1:expr, $e2:expr) => {
            Expr::BinOpExpr($crate::p4::p4ir::BinOps::Ge, Box::new($e1), Box::new($e2))
        };
    }

    macro_rules! p4_read {
        ($x:expr, $y:expr) => {
            Stmt::Read($x.to_string(), $y.to_string())
        };
    }

    macro_rules! p4_write {
        ($x:expr, $y:expr) => {
            Stmt::Write($x.to_string(), $y)
        };
    }

    pub(crate) use {
        add, and, assign, bitand, bitnot, bitor, bitxor, block, div, eq, ge, gt, ite, le, lt, mul,
        ne, neg, not, or, p4_read, p4_write, shl, shr, sub, var, xor,
    };
}

pub mod example_progs {
    use super::{
        macros::{add, assign, block, ite, lt, p4_read, p4_write, var},
        p4ir::{Expr, Stmt, Table},
    };

    pub fn rcp() -> Table {
        let set_pkt = block!(
            p4_read!("input_traffic_bytes_tmp", "input_traffic_bytes"),
            p4_read!("sum_rtt_tmp", "sum_rtt"),
            p4_read!("num_pkts_tmp", "num_pkts"),
            ite!(
                lt!(var!("meta.rtt"), Expr::Int(30)),
                block!(
                    assign!("sum_rtt_tmp" => add!(var!("sum_rtt_tmp"), var!("meta.rtt"))),
                    assign!("num_pkts_tmp" => add!(var!("num_pkts_tmp"), Expr::Int(1)))
                ),
                block!()
            ),
            p4_write!("input_traffic_bytes", var!("input_traffic_bytes_tmp")),
            p4_write!("sum_rtt", var!("sum_rtt_tmp")),
            p4_write!("num_pkts", var!("num_pkts_tmp"))
        );
        let mut table = Table::new("rcp_table".to_string(), vec!["meta.rcp_key".to_string()]);
        table.add_action("set_pkt".into(), set_pkt);
        return table;
    }
}
