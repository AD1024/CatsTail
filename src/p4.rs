pub mod p4ir {
    use std::collections::HashMap;

    use egg::{Id, RecExpr};

    use crate::{
        language::{
            ir::{Constant, Mio},
            utils::interp_recexpr,
        },
        utils::RegionedMap,
    };

    #[allow(dead_code)]
    #[derive(Debug, Clone, Hash, PartialEq, Eq)]
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
        #[allow(dead_code)]
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

    #[allow(dead_code)]
    #[derive(Debug, Clone, Hash, PartialEq, Eq)]
    pub enum UnOps {
        Neg,
        Not,
        BitNot,
    }

    #[allow(dead_code)]
    impl UnOps {
        pub fn to_mio(&self, arg: Id) -> Mio {
            match self {
                Self::Neg => Mio::Neg(arg),
                Self::Not => Mio::LNot(arg),
                Self::BitNot => Mio::BitNot(arg),
            }
        }
    }

    #[allow(dead_code)]
    #[derive(Debug, Clone, Hash, PartialEq, Eq)]
    pub enum Expr {
        Var(String),
        Int(i32),
        Bool(bool),
        BinOpExpr(BinOps, Box<Expr>, Box<Expr>),
        UnOpExpr(UnOps, Box<Expr>),
    }

    #[allow(dead_code)]
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
        pub fn is_true(&self) -> bool {
            match self {
                Expr::Bool(b) => *b,
                _ => false,
            }
        }
    }

    #[allow(dead_code)]
    #[derive(Debug, Clone)]
    pub enum Stmt {
        Assign(Expr, Expr),
        If(Expr, Box<Stmt>, Box<Stmt>),
        Block(Vec<Stmt>),
        Read(String, String),
        Write(String, String),
    }

    #[allow(dead_code)]
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
                    let _ = ctx.get(from).unwrap().clone();
                } else {
                    ctx.insert(to.clone(), Mio::Constant(Constant::Int(0)));
                }
            }
            Stmt::Write(gvar, expr) => {
                ctx.insert(gvar.clone(), ctx.get(expr).unwrap().clone());
            }
        }
    }

    #[derive(Debug, Clone)]
    pub struct Table {
        pub name: String,
        pub keys: Vec<String>,
        pub actions: HashMap<String, Stmt>,
    }

    #[allow(dead_code)]
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
            Stmt::Write($x.to_string(), $y.to_string())
        };
    }

    pub(crate) use {
        add, and, assign, bitand, bitnot, bitor, bitxor, block, div, eq, ge, gt, ite, le, lt, mul,
        ne, neg, not, or, p4_read, p4_write, shl, shr, sub, var, xor,
    };
}

pub mod example_progs {
    use super::{
        macros::*,
        p4ir::{Expr, Stmt, Table},
    };

    #[allow(dead_code)]
    pub fn rcp() -> Vec<Table> {
        let set_pkt = block!(
            assign!("input_traffic_bytes_tmp" => var!("global.input_traffic_bytes")),
            assign!("sum_rtt_tmp" => var!("global.sum_rtt")),
            assign!("num_pkts_tmp" => var!("global.num_pkts")),
            assign!("input_traffic_bytes_tmp" => add!(var!("input_traffic_bytes_tmp"), var!("meta.size_bytes"))),
            ite!(
                lt!(var!("meta.rtt"), Expr::Int(30)),
                block!(
                    assign!("sum_rtt_tmp" => add!(var!("sum_rtt_tmp"), var!("meta.rtt"))),
                    assign!("num_pkts_tmp" => add!(var!("num_pkts_tmp"), Expr::Int(1)))
                ),
                block!()
            ),
            assign!("global.input_traffic_bytes" => var!("input_traffic_bytes_tmp")),
            assign!("global.sum_rtt" => var!("sum_rtt_tmp")),
            assign!("global.num_pkts" => var!("num_pkts_tmp"))
        );
        let mut table = Table::new("rcp_table".to_string(), vec!["meta.rcp_key".to_string()]);
        table.add_action("set_pkt".into(), set_pkt);
        return vec![table];
    }

    #[allow(dead_code)]
    pub fn sampling() -> Vec<Table> {
        let set_pkt = block!(
            assign!("count_tmp" => var!("global.count")),
            ite!(
                eq!(var!("count_tmp"), Expr::Int(29)),
                block!(
                    assign!("meta.sample" => Expr::Int(1)),
                    assign!("count_tmp" => Expr::Int(0))
                ),
                block!(
                    assign!("meta.sample" => Expr::Int(0)),
                    assign!("count_tmp" => add!(var!("count_tmp"), Expr::Int(1)))
                )
            ),
            assign!("global.count" => var!("count_tmp"))
        );
        let mut table = Table::new(
            "sampling_table".to_string(),
            vec!["meta.sampling_key".to_string()],
        );
        table.add_action("set_pkt".into(), set_pkt);
        return vec![table];
    }

    #[allow(dead_code)]
    pub fn blue_increase() -> Vec<Table> {
        let set_pkt = block!(
            assign!("last_update_tmp" => var!("global.last_update")),
            assign!("p_mark_tmp" => var!("global.p_mark")),
            assign!("meta.now_plus_free" => sub!(var!("meta.now"), Expr::Int(10))),
            ite!(
                gt!(var!("meta.now_plus_free"), var!("last_update_tmp")),
                block!(
                    assign!("p_mark_tmp" => add!(var!("p_mark_tmp"), Expr::Int(1))),
                    assign!("last_update_tmp" => var!("meta.now"))
                ),
                block!()
            ),
            assign!("global.last_update" => var!("last_update_tmp")),
            assign!("global.p_mark" => var!("p_mark_tmp"))
        );
        let mut table = Table::new(
            "blue_increase_table".to_string(),
            vec!["meta.blue_increase_key".to_string()],
        );
        table.add_action("set_pkt".into(), set_pkt);
        return vec![table];
    }

    #[allow(dead_code)]
    pub fn flowlet() -> Vec<Table> {
        let set_pkt = block!(
            assign!("saved_hop_tmp" => var!("global.saved_hop")),
            assign!("last_time_tmp" => var!("global.last_time")),
            ite!(
                lt!(
                    sub!(var!("meta.arrival"), var!("last_time_tmp")),
                    Expr::Int(5)
                ),
                block!(assign!("saved_hop_tmp" => var!("meta.new_hop"))),
                block!()
            ),
            assign!("last_time_tmp" => var!("meta.arrival")),
            assign!("meta.next_hop" => var!("saved_hop_tmp")),
            assign!("global.saved_hop" => var!("saved_hop_tmp")),
            assign!("global.last_time" => var!("last_time_tmp"))
        );
        let mut table = Table::new(
            "flowlet_table".to_string(),
            vec!["meta.flowlet_key".to_string()],
        );
        table.add_action("set_pkt".into(), set_pkt);
        return vec![table];
    }

    #[allow(dead_code)]
    pub fn marple_nmo() -> Vec<Table> {
        let set_pkt = block!(
            assign!("count_tmp" => var!("global.count")),
            assign!("maxseq_tmp" => var!("global.maxseq")),
            ite!(
                lt!(var!("meta.seq"), var!("maxseq_tmp")),
                assign!("count_tmp" => add!(var!("count_tmp"), Expr::Int(1))),
                assign!("maxseq_tmp" => var!("meta.seq"))
            ),
            assign!("global.count" => var!("count_tmp")),
            assign!("global.maxseq" => var!("maxseq_tmp"))
        );
        let mut table = Table::new(
            "marple_nmo_table".to_string(),
            vec!["meta.marple_nmo_key".to_string()],
        );
        table.add_action("set_pkt".into(), set_pkt);
        return vec![table];
    }

    #[allow(dead_code)]
    pub fn marple_new_flow() -> Vec<Table> {
        let set_pkt = block!(
            assign!("count_tmp" => var!("global.count")),
            ite!(
                eq!(var!("count_tmp"), Expr::Int(0)),
                block!(
                    assign!("meta.new_flow" => Expr::Int(1)),
                    assign!("count_tmp" => Expr::Int(1))
                ),
                block!()
            ),
            assign!("global.count" => var!("count_tmp"))
        );
        let mut table = Table::new(
            "marple_new_flow_table".to_string(),
            vec!["meta.marple_new_flow_key".to_string()],
        );
        table.add_action("set_pkt".into(), set_pkt);
        return vec![table];
    }

    #[allow(dead_code)]
    pub fn stateful_fw() -> Vec<Table> {
        let set_pkt = block!(
            assign!("established_tmp" => var!("global.established")),
            assign!("meta.array_index" => add!(var!("meta.src"), var!("meta.dst"))),
            ite!(
                eq!(var!("meta.src"), Expr::Int(20)),
                assign!("established_tmp" => Expr::Int(1)),
                block!(ite!(
                    eq!(var!("meta.dst"), Expr::Int(20)),
                    ite!(
                        eq!(var!("established_tmp"), Expr::Int(0)),
                        assign!("meta.drop" => Expr::Int(1)),
                        assign!("meta.drop" => Expr::Int(0))
                    ),
                    block!()
                ))
            ),
            assign!("global.established" => var!("established_tmp"))
        );
        let mut table = Table::new(
            "stateful_fw_table".to_string(),
            vec!["meta.stateful_fw_key".to_string()],
        );
        table.add_action("set_pkt".into(), set_pkt);
        return vec![table];
    }

    #[allow(dead_code)]
    pub fn cetus_waw() -> Vec<Table> {
        let a1 = assign!("meta.b" => add!(var!("meta.c"), Expr::Int(1)));
        let a2 = assign!("meta.b" => Expr::Int(1));
        let mut table1 = Table::new("first_table".to_string(), vec!["meta.a".to_string()]);
        let mut table2 = Table::new("second_table".to_string(), vec!["meta.a".to_string()]);
        table1.add_action("a1".into(), a1);
        table2.add_action("a2".into(), a2);
        return vec![table1, table2];
    }

    #[allow(dead_code)]
    pub fn learn_filter() -> Vec<Table> {
        let set_pkt = block!(
            assign!("first_filter_tmp" => var!("global.first_filter")),
            assign!("second_filter_tmp" => var!("global.second_filter")),
            assign!("third_filter_tmp" => var!("global.third_filter")),
            ite!(
                and!(
                    and!(
                        not!(eq!(var!("first_filter_tmp"), Expr::Int(0))),
                        not!(eq!(var!("second_filter_tmp"), Expr::Int(0)))
                    ),
                    not!(eq!(var!("third_filter_tmp"), Expr::Int(0)))
                ),
                assign!("meta.member" => Expr::Int(1)),
                assign!("meta.member" => Expr::Int(0))
            ),
            assign!("first_filter_tmp" => Expr::Int(1)),
            assign!("second_filter_tmp" => Expr::Int(1)),
            assign!("third_filter_tmp" => Expr::Int(1)),
            assign!("global.first_filter" => var!("first_filter_tmp")),
            assign!("global.second_filter" => var!("second_filter_tmp")),
            assign!("global.third_filter" => var!("third_filter_tmp"))
        );
        let mut table = Table::new(
            "learn_filter_table".to_string(),
            vec!["meta.learn_filter_key".to_string()],
        );
        table.add_action("set_pkt".into(), set_pkt);
        return vec![table];
    }
}
