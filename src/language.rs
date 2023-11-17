use egg;

pub mod ir {
    use std::ops;
    use std::{
        collections::{HashMap, HashSet},
        fmt::Display,
        hash::Hash,
        str::FromStr,
    };

    use egg::{define_language, Analysis, DidMerge, EGraph, Id, Language};

    define_language! {
        pub enum Mio {
            "ite" = Ite([Id; 3]),
            // (GIte (keys k1 k2 k3...) (actions a1 a2 a3 ... default))
            // each action is in the form of
            // (elaborations (E table e1) (E table e2) ...)
            "gite" = GIte([Id; 2]),
            "keys" = Keys(Vec<Id>),
            "actions" = Actions(Vec<Id>),
            "elaborations" = Elaborations(Vec<Id>),
            // (E <table> <expr>)
            "E" = Elaborate([Id; 2]),
            // putting tables in the same stage; equivalent to T1 || T2
            // (join ?t1 ?t2)
            "join" = Join([Id; 2]),
            // Stage barrier; (seq ?t1 ?t2) denotes
            // putting t2 after the stage of t1
            "seq" = Seq([Id; 2]),
            // (arith-alu ?op ?a ?b ?imm)
            "arith-alu" = ArithAlu(Vec<Id>),
            // (rel-alu ?pred ?a ?b ?imm)
            "rel-alu" = RelAlu(Vec<Id>),
            "bool-alu" = BoolAlu(Vec<Id>),
            // syntax differs across backends
            // e.g. Intel tofino supports three outputs (with one modification to PHV)
            // (stateful-alu ?op ?dst ?src1 ?src2 ... ?src_n)
            "stateful-alu" = SAlu(Vec<Id>),
            // Logical operators
            "land" = LAnd([Id; 2]),
            "lor" = LOr([Id; 2]),
            "lnot" = LNot(Id),
            "lxor" = LXor([Id; 2]),
            // Bitwise operators
            "bitand" = BitAnd([Id; 2]),
            "bitor" = BitOr([Id; 2]),
            "bitnot" = BitNot(Id),
            "bitxor" = BitXor([Id; 2]),
            "bitshl" = BitShl([Id; 2]),
            "bitshr" = BitShr([Id; 2]),
            // Arithmetic operators
            "+" = Add([Id; 2]),
            "-" = Sub([Id; 2]),
            "min" = Min([Id; 2]),
            "max" = Max([Id; 2]),
            "neg" = Neg(Id),
            "write" = Write([Id; 2]),
            "read" = Read([Id; 2]),
            // Comparators
            "=" = Eq([Id; 2]),
            "<" = Lt([Id; 2]),
            ">" = Gt([Id; 2]),
            "<=" = Le([Id; 2]),
            ">=" = Ge([Id; 2]),
            "!=" = Neq([Id; 2]),
            "global" = Global(Id),
            "noop" = NoOp,
            ArithAluOps(ArithAluOps),
            BoolAluOps(BoolAluOps),
            RelAluOps(RelAluOps),
            Constant(Constant),
            Symbol(String),
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum MioType {
        Bool,
        Int,
        BitInt(usize),
        Table(Vec<usize>),
        List(Box<MioType>, usize),
        ActionList(usize),
        Unknown,
        // Meta(i32),
    }

    impl Default for MioType {
        fn default() -> Self {
            MioType::Unknown
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub enum ArithAluOps {
        Add,
        Sub,
        Max,
        Min,
        Not,
        Const,
        LocalSymbol,
        GlobalSymbol,
        Idle,
        Ite,
    }

    impl Display for ArithAluOps {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                ArithAluOps::Add => write!(f, "alu-add"),
                ArithAluOps::Sub => write!(f, "alu-sub"),
                ArithAluOps::Max => write!(f, "alu-max"),
                ArithAluOps::Min => write!(f, "alu-min"),
                ArithAluOps::Const => write!(f, "alu-const"),
                ArithAluOps::Not => write!(f, "alu-not"),
                ArithAluOps::Idle => write!(f, "alu-idle"),
                ArithAluOps::LocalSymbol => write!(f, "alu-local"),
                ArithAluOps::GlobalSymbol => write!(f, "alu-global"),
                ArithAluOps::Ite => write!(f, "alu-ite"),
            }
        }
    }

    impl FromStr for ArithAluOps {
        type Err = ();

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            match s {
                "alu-add" => Ok(ArithAluOps::Add),
                "alu-sub" => Ok(ArithAluOps::Sub),
                "alu-max" => Ok(ArithAluOps::Max),
                "alu-min" => Ok(ArithAluOps::Min),
                "alu-const" => Ok(ArithAluOps::Const),
                "alu-not" => Ok(ArithAluOps::Not),
                "alu-idle" => Ok(ArithAluOps::Idle),
                "alu-local" => Ok(ArithAluOps::LocalSymbol),
                "alu-global" => Ok(ArithAluOps::GlobalSymbol),
                "alu-ite" => Ok(ArithAluOps::Ite),
                _ => Err(()),
            }
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub enum RelAluOps {
        Eq,
        Lt,
        Gt,
        Le,
        Ge,
        Neq,
    }

    impl Display for RelAluOps {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                RelAluOps::Eq => write!(f, "alu-eq"),
                RelAluOps::Lt => write!(f, "alu-lt"),
                RelAluOps::Gt => write!(f, "alu-gt"),
                RelAluOps::Le => write!(f, "alu-le"),
                RelAluOps::Ge => write!(f, "alu-ge"),
                RelAluOps::Neq => write!(f, "alu-neq"),
            }
        }
    }

    impl FromStr for RelAluOps {
        type Err = ();

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            match s {
                "alu-eq" => Ok(RelAluOps::Eq),
                "alu-lt" => Ok(RelAluOps::Lt),
                "alu-gt" => Ok(RelAluOps::Gt),
                "alu-le" => Ok(RelAluOps::Le),
                "alu-ge" => Ok(RelAluOps::Ge),
                "alu-neq" => Ok(RelAluOps::Neq),
                _ => Err(()),
            }
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub enum BoolAluOps {
        And,
        Or,
        Not,
        Xor,
    }

    impl Display for BoolAluOps {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                BoolAluOps::And => write!(f, "alu-and"),
                BoolAluOps::Or => write!(f, "alu-or"),
                BoolAluOps::Not => write!(f, "alu-not"),
                BoolAluOps::Xor => write!(f, "alu-xor"),
            }
        }
    }

    impl FromStr for BoolAluOps {
        type Err = ();

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            match s {
                "alu-and" => Ok(BoolAluOps::And),
                "alu-or" => Ok(BoolAluOps::Or),
                "alu-not" => Ok(BoolAluOps::Not),
                "alu-xor" => Ok(BoolAluOps::Xor),
                _ => Err(()),
            }
        }
    }

    #[derive(Debug, Clone, PartialOrd, Ord, Eq, Hash)]
    pub enum Constant {
        Int(i32),
        BitInt(i32, usize),
        Bool(bool),
    }

    impl PartialEq for Constant {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (Constant::Int(_), Constant::BitInt(_, _)) => other == self,
                (Constant::Int(a), Constant::Int(b)) => a == b,
                (Constant::Bool(a), Constant::Bool(b)) => a == b,
                (Constant::BitInt(a, _), Constant::BitInt(b, _)) => a == b,
                (Constant::BitInt(a, _), Constant::Int(b)) => a == b,
                _ => false,
            }
        }
    }

    impl Display for Constant {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Constant::Int(i) => write!(f, "{}", i),
                Constant::Bool(b) => write!(f, "{}", b),
                Constant::BitInt(i, len) => write!(f, "{}[{}]", i, len),
            }
        }
    }

    impl From<i32> for Constant {
        fn from(i: i32) -> Self {
            Constant::Int(i)
        }
    }

    impl From<bool> for Constant {
        fn from(b: bool) -> Self {
            Constant::Bool(b)
        }
    }

    impl FromStr for Constant {
        type Err = ();

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            if let Ok(i) = s.parse::<i32>() {
                Ok(Constant::Int(i))
            } else if let Ok(b) = s.parse::<bool>() {
                Ok(Constant::Bool(b))
            } else {
                Err(())
            }
        }
    }

    impl std::ops::Add<Constant> for Constant {
        type Output = Constant;

        fn add(self, rhs: Constant) -> Self::Output {
            match (&self, &rhs) {
                (Constant::Int(_a), Constant::BitInt(_, _)) => rhs + self,
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a + b),
                (Constant::BitInt(a, s_a), Constant::BitInt(b, s_b)) => {
                    Constant::BitInt(a + b, *s_a.max(s_b))
                }
                (Constant::BitInt(a, s_a), Constant::Int(b)) => Constant::BitInt(a + b, *s_a),
                _ => panic!("Addition of non-integers: {:?} + {:?}", self, rhs),
            }
        }
    }

    impl std::ops::Sub<Constant> for Constant {
        type Output = Constant;

        fn sub(self, rhs: Constant) -> Self::Output {
            match (&self, &rhs) {
                (Constant::Int(_a), Constant::BitInt(_, _)) => (-rhs) - (-self),
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a - b),
                (Constant::BitInt(a, s_a), Constant::BitInt(b, s_b)) => {
                    Constant::BitInt(a - b, *s_a.max(s_b))
                }
                (Constant::BitInt(a, s_a), Constant::Int(b)) => Constant::BitInt(a - b, *s_a),
                _ => panic!("Subtraction of non-integers"),
            }
        }
    }

    impl std::ops::Neg for Constant {
        type Output = Constant;

        fn neg(self) -> Self::Output {
            match self {
                Constant::Int(a) => Constant::Int(-a),
                Constant::BitInt(a, s) => Constant::BitInt(-a, s),
                _ => panic!("Negation of non-integers"),
            }
        }
    }

    impl std::ops::BitAnd<Constant> for Constant {
        type Output = Constant;

        fn bitand(self, rhs: Constant) -> Self::Output {
            match (&self, &rhs) {
                (Constant::Int(_a), Constant::BitInt(_, _)) => rhs & self,
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a & b),
                (Constant::BitInt(a, s_a), Constant::BitInt(b, s_b)) => {
                    Constant::BitInt(a & b, *s_a.max(s_b))
                }
                (Constant::BitInt(a, s_a), Constant::Int(b)) => Constant::BitInt(a & b, *s_a),
                _ => panic!("Bitwise and of non-integers"),
            }
        }
    }

    impl std::ops::BitOr<Constant> for Constant {
        type Output = Constant;

        fn bitor(self, rhs: Constant) -> Self::Output {
            match (&self, &rhs) {
                (Constant::Int(_a), Constant::BitInt(_, _)) => rhs | self,
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a | b),
                (Constant::BitInt(a, s_a), Constant::BitInt(b, s_b)) => {
                    Constant::BitInt(a | b, *s_a.max(s_b))
                }
                (Constant::BitInt(a, s_a), Constant::Int(b)) => Constant::BitInt(a | b, *s_a),
                _ => panic!("Bitwise or of non-integers"),
            }
        }
    }

    impl std::ops::BitXor<Constant> for Constant {
        type Output = Constant;

        fn bitxor(self, rhs: Constant) -> Self::Output {
            match (&self, &rhs) {
                (Constant::Int(_a), Constant::BitInt(_, _)) => rhs ^ self,
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a ^ b),
                (Constant::BitInt(a, s_a), Constant::BitInt(b, s_b)) => {
                    Constant::BitInt(a ^ b, *s_a.max(s_b))
                }
                (Constant::BitInt(a, s_a), Constant::Int(b)) => Constant::BitInt(a ^ b, *s_a),
                _ => panic!("Bitwise xor of non-integers"),
            }
        }
    }

    impl std::ops::Shl<Constant> for Constant {
        type Output = Constant;

        fn shl(self, rhs: Constant) -> Self::Output {
            match (self, rhs) {
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a << b),
                (Constant::BitInt(a, s), Constant::Int(b)) => Constant::BitInt(a << b, s),
                _ => panic!("Bitwise shift left of non-integers"),
            }
        }
    }

    impl std::ops::Shr<Constant> for Constant {
        type Output = Constant;

        fn shr(self, rhs: Constant) -> Self::Output {
            match (self, rhs) {
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a >> b),
                (Constant::BitInt(a, s), Constant::Int(b)) => Constant::BitInt(a >> b, s),
                _ => panic!("Bitwise shift right of non-integers"),
            }
        }
    }

    impl std::ops::Not for Constant {
        type Output = Constant;

        fn not(self) -> Self::Output {
            match self {
                Constant::Int(a) => Constant::Int(!a),
                Constant::Bool(b) => Constant::Bool(!b),
                Constant::BitInt(a, s) => Constant::BitInt(!a, s),
            }
        }
    }

    impl Constant {
        pub fn as_bool(&self) -> Option<bool> {
            match self {
                Constant::Bool(b) => Some(*b),
                _ => None,
            }
        }

        pub fn as_int(&self) -> Option<i32> {
            match self {
                Constant::Int(i) => Some(*i),
                _ => None,
            }
        }
    }

    pub struct MioAnalysis {
        context: HashMap<String, Constant>,
        gamma: HashMap<String, MioType>,
        var_counter: usize,
    }

    impl Default for MioAnalysis {
        fn default() -> Self {
            MioAnalysis {
                context: HashMap::new(),
                gamma: HashMap::new(),
                var_counter: 0,
            }
        }
    }

    impl MioAnalysis {
        pub fn new(ctx: HashMap<String, Constant>, gamma: HashMap<String, MioType>) -> Self {
            MioAnalysis {
                context: ctx,
                gamma,
                var_counter: 0,
            }
        }

        pub fn new_var(&mut self, ty: MioType) -> String {
            let result = format!("var_{}", self.var_counter);
            self.gamma.insert(result.clone(), ty);
            self.var_counter += 1;
            return result;
        }

        pub fn new_table_name(&mut self, derived_from: Option<String>) -> String {
            let result = if let Some(derived_from) = derived_from {
                format!("table_{}", derived_from)
            } else {
                format!("table_{}", self.var_counter)
            };
            self.var_counter += 1;
            return result;
        }

        pub fn get_table_name(egraph: &egg::EGraph<Mio, Self>, id: Id) -> Option<String> {
            match &egraph[id].data {
                MioAnalysisData::Dataflow(RWAnalysis { table_name, .. }) => table_name.clone(),
                _ => None,
            }
        }

        pub fn type_unification(lhs_ty: &MioType, rhs_ty: &MioType) -> MioType {
            match (lhs_ty, rhs_ty) {
                (MioType::Bool, MioType::Bool) => MioType::Bool,
                (MioType::BitInt(len_l), MioType::BitInt(len_r)) => {
                    MioType::BitInt(*len_l.max(len_r))
                }
                (MioType::Int, MioType::BitInt(_))
                | (MioType::BitInt(_), MioType::Int)
                | (MioType::Int, MioType::Int) => MioType::Int,
                // (MioType::Int, MioType::Bool)
                // | (MioType::Bool, MioType::Int)
                // | (MioType::BitInt(_), MioType::Bool)
                // | (MioType::Bool, MioType::BitInt(_)) => MioType::Int,
                (MioType::List(t1, len_l), MioType::List(t2, len_r)) => {
                    assert_eq!(len_l, len_r);
                    MioType::List(Box::new(Self::type_unification(t1, t2)), *len_l)
                }
                (MioType::ActionList(len_l), MioType::ActionList(len_r)) => {
                    assert_eq!(len_l, len_r);
                    MioType::ActionList(*len_l)
                }
                (MioType::Table(sizes_l), MioType::Table(sizes_r)) => {
                    // Combining two table types, representing all possible sizes of the tables in
                    // the e-class
                    return MioType::Table(
                        sizes_l
                            .iter()
                            .chain(sizes_r.iter())
                            .cloned()
                            .collect::<HashSet<_>>()
                            .into_iter()
                            .collect(),
                    );
                }
                (MioType::Unknown, _) => rhs_ty.clone(),
                (_, MioType::Unknown) => lhs_ty.clone(),
                (_, _) => panic!("Cannot unify types {:?} and {:?}", lhs_ty, rhs_ty),
            }
        }

        pub fn eval_unop(expr: &Mio, x: Option<Constant>) -> Option<Constant> {
            Some(match expr {
                Mio::Neg(_) => Constant::Int(0) - (x?),
                Mio::LNot(_) => !(x?),
                Mio::BitNot(_) => !(x?),
                _ => panic!("eval_unop called with non-unary operator"),
            })
        }

        pub fn eval_binop(
            expr: &Mio,
            lhs: Option<Constant>,
            rhs: Option<Constant>,
        ) -> Option<Constant> {
            Some(match expr {
                Mio::Add(_) => lhs? + rhs?,
                Mio::Sub(_) => lhs? - rhs?,
                Mio::BitAnd(_) => lhs? & rhs?,
                Mio::BitOr(_) => lhs? | rhs?,
                Mio::BitXor(_) => lhs? ^ rhs?,
                Mio::BitShl(_) => lhs? << rhs?,
                Mio::BitShr(_) => lhs? >> rhs?,
                Mio::LAnd(_) => Constant::Bool(lhs?.as_bool()? && rhs?.as_bool()?),
                Mio::LOr(_) => Constant::Bool(lhs?.as_bool()? || rhs?.as_bool()?),
                Mio::LXor(_) => Constant::Bool(lhs?.as_bool()? ^ rhs?.as_bool()?),
                Mio::Eq(_) => Constant::Bool(lhs? == rhs?),
                Mio::Lt(_) => Constant::Bool(lhs? < rhs?),
                Mio::Gt(_) => Constant::Bool(lhs? > rhs?),
                Mio::Le(_) => Constant::Bool(lhs? <= rhs?),
                Mio::Ge(_) => Constant::Bool(lhs? >= rhs?),
                Mio::Neq(_) => Constant::Bool(lhs? != rhs?),
                _ => panic!("eval_binop called with non-binary operator"),
            })
        }

        pub fn new_action_data(
            reads: HashSet<String>,
            writes: HashSet<String>,
            checked_type: MioType,
            constant: Option<Constant>,
            elaborations: HashSet<String>,
        ) -> MioAnalysisData {
            MioAnalysisData::Action(ActionAnalysis {
                reads,
                writes,
                constant,
                elaborations,
                checked_type,
            })
        }

        pub fn new_dataflow_data(
            reads: HashSet<String>,
            writes: HashSet<String>,
            table_name: Option<String>,
        ) -> MioAnalysisData {
            MioAnalysisData::Dataflow(RWAnalysis {
                reads,
                writes,
                table_name,
            })
        }

        pub fn get_constant(egraph: &egg::EGraph<Mio, Self>, id: Id) -> Option<Constant> {
            match &egraph[id].data {
                MioAnalysisData::Action(u) => u.constant.clone(),
                _ => panic!("Dataflow {:?} has no constant", id),
            }
        }

        pub fn get_type(egraph: &egg::EGraph<Mio, Self>, id: Id) -> MioType {
            match &egraph[id].data {
                MioAnalysisData::Action(u) => u.checked_type.clone(),
                _ => panic!("Dataflow {:?} has no type", id),
            }
        }

        pub fn read_set<'a>(egraph: &'a egg::EGraph<Mio, Self>, id: Id) -> &'a HashSet<String> {
            match &egraph[id].data {
                MioAnalysisData::Action(u) => &u.reads,
                MioAnalysisData::Dataflow(d) => &d.reads,
                _ => panic!("Empty Analysis @ {}", id),
            }
        }

        pub fn write_set<'a>(egraph: &'a egg::EGraph<Mio, Self>, id: Id) -> &'a HashSet<String> {
            match &egraph[id].data {
                MioAnalysisData::Action(u) => &u.writes,
                MioAnalysisData::Dataflow(d) => &d.writes,
                _ => panic!("Empty Analysis @ {}", id),
            }
        }

        pub fn elaborations<'a>(egraph: &'a egg::EGraph<Mio, Self>, id: Id) -> &'a HashSet<String> {
            match &egraph[id].data {
                MioAnalysisData::Action(u) => &u.elaborations,
                _ => panic!("Dataflow {:?} has no elaborations", id),
            }
        }

        pub fn set_elaboration(
            egraph: &mut egg::EGraph<Mio, Self>,
            id: Id,
            elaborations: HashSet<String>,
        ) {
            match &mut egraph[id].data {
                MioAnalysisData::Action(u) => u.elaborations = elaborations,
                _ => panic!("Dataflow {:?} has no elaborations", id),
            }
        }

        pub fn add_to_elaboration(
            egraph: &mut egg::EGraph<Mio, Self>,
            id: Id,
            elaboration: String,
        ) {
            match &mut egraph[id].data {
                MioAnalysisData::Action(u) => u.elaborations.insert(elaboration),
                _ => panic!("Dataflow {:?} has no elaborations", id),
            };
        }

        pub fn is_alu_op(egraph: &egg::EGraph<Mio, MioAnalysis>, id: Id, alu_op: &str) -> bool {
            match &egraph[id].nodes[0] {
                Mio::ArithAluOps(op) => op == &alu_op.parse().unwrap(),
                Mio::RelAluOps(op) => op == &alu_op.parse().unwrap(),
                _ => false,
            }
        }

        pub fn add_expr(
            egraph: &mut egg::EGraph<Mio, MioAnalysis>,
            op: &'static str,
            operands: Vec<Id>,
        ) -> Id {
            match op {
                "+" => egraph.add(Mio::Add([operands[0], operands[1]])),
                "-" => egraph.add(Mio::Sub([operands[0], operands[1]])),
                "min" => egraph.add(Mio::Min([operands[0], operands[1]])),
                "max" => egraph.add(Mio::Max([operands[0], operands[1]])),
                "neg" => egraph.add(Mio::Neg(operands[0])),
                "write" => egraph.add(Mio::Write([operands[0], operands[1]])),
                "read" => egraph.add(Mio::Read([operands[0], operands[1]])),
                "land" => egraph.add(Mio::LAnd([operands[0], operands[1]])),
                "lor" => egraph.add(Mio::LOr([operands[0], operands[1]])),
                "lnot" => egraph.add(Mio::LNot(operands[0])),
                "lxor" => egraph.add(Mio::LXor([operands[0], operands[1]])),
                "bitand" => egraph.add(Mio::BitAnd([operands[0], operands[1]])),
                "bitor" => egraph.add(Mio::BitOr([operands[0], operands[1]])),
                "bitnot" => egraph.add(Mio::BitNot(operands[0])),
                "bitxor" => egraph.add(Mio::BitXor([operands[0], operands[1]])),
                "bitshl" => egraph.add(Mio::BitShl([operands[0], operands[1]])),
                "bitshr" => egraph.add(Mio::BitShr([operands[0], operands[1]])),
                "=" => egraph.add(Mio::Eq([operands[0], operands[1]])),
                "<" => egraph.add(Mio::Lt([operands[0], operands[1]])),
                ">" => egraph.add(Mio::Gt([operands[0], operands[1]])),
                "<=" => egraph.add(Mio::Le([operands[0], operands[1]])),
                ">=" => egraph.add(Mio::Ge([operands[0], operands[1]])),
                "!=" => egraph.add(Mio::Neq([operands[0], operands[1]])),
                _ => panic!("Unknown operator {}", op),
            }
        }

        pub fn has_leaf(egraph: &egg::EGraph<Mio, MioAnalysis>, id: Id) -> bool {
            return egraph[id].nodes.iter().any(|x| x.is_leaf());
        }

        pub fn has_stateful_elaboration(egraph: &egg::EGraph<Mio, MioAnalysis>, id: Id) -> bool {
            return Self::elaborations(egraph, id)
                .iter()
                .any(|x| x.contains("global."));
        }

        pub fn has_stateless_elaboration(egraph: &egg::EGraph<Mio, MioAnalysis>, id: Id) -> bool {
            return Self::elaborations(egraph, id)
                .iter()
                .filter(|x| !x.contains("global."))
                .count()
                > 0;
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq, Default)]
    pub struct RWAnalysis {
        // For checking whether dataflow is preserved
        // by rewrites; used for Control nodes and tables
        pub reads: HashSet<String>,
        pub writes: HashSet<String>,
        pub table_name: Option<String>,
    }

    #[derive(Debug, Clone, PartialEq, Eq, Default)]
    pub struct ActionAnalysis {
        pub reads: HashSet<String>,
        pub writes: HashSet<String>,
        pub checked_type: MioType,
        pub constant: Option<Constant>,
        pub elaborations: HashSet<String>,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum MioAnalysisData {
        Dataflow(RWAnalysis),
        Action(ActionAnalysis),
        Empty,
    }

    impl Analysis<Mio> for MioAnalysis {
        type Data = MioAnalysisData;

        fn modify(egraph: &mut egg::EGraph<Mio, Self>, id: Id) {
            // when there are constants, we can add a new node to the e-class
            // with the constant value
            if let Mio::Symbol(sym) = &egraph[id].nodes[0] {
                let alu_symbol = if sym.starts_with("global.") {
                    egraph.add(Mio::ArithAluOps(ArithAluOps::GlobalSymbol))
                } else {
                    egraph.add(Mio::ArithAluOps(ArithAluOps::LocalSymbol))
                };
                let sym_node = egraph.add(Mio::ArithAlu(vec![alu_symbol, id]));
                let f = egraph.union(id, sym_node);
                if f {
                    egraph.rebuild();
                }
            }
            if let MioAnalysisData::Action(ActionAnalysis {
                constant: Some(constant),
                checked_type,
                elaborations,
                ..
            }) = egraph[id].data.clone()
            {
                let new_id = egraph.add(Mio::Constant(constant.clone()));
                let const_op = egraph.add(Mio::ArithAluOps(ArithAluOps::Const));
                let alu_const = egraph.add(Mio::ArithAlu(vec![const_op, new_id]));
                let f = egraph.union(id, new_id);
                let f = egraph.union(id, alu_const) || f;
                if f {
                    egraph.rebuild();
                }
                let rt = egraph.find(id);
                egraph[rt].data = MioAnalysis::new_action_data(
                    HashSet::new(),
                    HashSet::new(),
                    checked_type.clone(),
                    Some(constant.clone()),
                    elaborations.clone(),
                )
            }
        }

        fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
            if let MioAnalysisData::Empty = b {
                return DidMerge(false, false);
            }
            if let MioAnalysisData::Empty = a {
                *a = b;
                return DidMerge(true, false);
            }
            if let (MioAnalysisData::Dataflow(lhs), MioAnalysisData::Dataflow(rhs)) = (&a, &b) {
                assert_eq!(lhs.reads, rhs.reads);
                assert_eq!(lhs.writes, rhs.writes);
                return DidMerge(false, false);
            }
            if let (MioAnalysisData::Action(lhs), MioAnalysisData::Dataflow(rhs)) = (&a, &b) {
                assert_eq!(lhs.reads, rhs.reads);
                assert_eq!(lhs.writes, rhs.writes);
                return DidMerge(false, false);
            }
            if let (MioAnalysisData::Dataflow(lhs), MioAnalysisData::Action(rhs)) = (&a, &b) {
                assert_eq!(lhs.reads, rhs.reads);
                assert_eq!(lhs.writes, rhs.writes);
                *a = b;
                return DidMerge(true, false);
            }
            if let (MioAnalysisData::Action(u1), MioAnalysisData::Action(u2)) = (&a, &b) {
                let ty = Self::type_unification(&u1.checked_type, &u2.checked_type);
                let merged = MioAnalysis::new_action_data(
                    u1.reads.union(&u2.reads).cloned().collect(),
                    u1.writes.union(&u2.writes).cloned().collect(),
                    ty,
                    u1.constant.clone().or(u2.constant.clone()),
                    u1.elaborations.union(&u2.elaborations).cloned().collect(),
                );
                let a_merged = merged != *a;
                let b_merged = merged != b;
                *a = merged;
                return DidMerge(a_merged, b_merged);
            }
            panic!("Cannot merge {:?} and {:?}", a, b);
        }

        fn make(egraph: &egg::EGraph<Mio, Self>, enode: &Mio) -> Self::Data {
            match enode {
                Mio::Elaborate([_, e]) => {
                    return MioAnalysis::new_action_data(
                        MioAnalysis::read_set(egraph, *e).clone(),
                        MioAnalysis::write_set(egraph, *e).clone(),
                        MioAnalysis::get_type(egraph, *e),
                        MioAnalysis::get_constant(egraph, *e),
                        MioAnalysis::elaborations(egraph, *e).clone(),
                    );
                }
                Mio::NoOp => MioAnalysisData::Dataflow(Default::default()),
                Mio::Global(v) => {
                    let v_data = match &egraph[*v].data {
                        MioAnalysisData::Action(v_data) => v_data,
                        _ => panic!("Global variable {:?} has no type", v),
                    };
                    MioAnalysis::new_action_data(
                        v_data.reads.clone(),
                        v_data.writes.clone(),
                        v_data.checked_type.clone(),
                        v_data.constant.clone(),
                        HashSet::new(),
                    )
                }
                // the || operator
                Mio::Join(tables) => {
                    if let [MioAnalysisData::Dataflow(t1), MioAnalysisData::Dataflow(t2)] =
                        tables.map(|t| &egraph[t].data).as_slice()
                    {
                        return MioAnalysisData::Dataflow(RWAnalysis {
                            reads: t1.reads.union(&t2.reads).cloned().collect(),
                            writes: t1.writes.union(&t2.writes).cloned().collect(),
                            table_name: None,
                        });
                    }
                    panic!(
                        "Join expects children to be tables or controls, {:?} and {:?} provided",
                        egraph[tables[0]].data, egraph[tables[1]].data
                    );
                }
                Mio::Seq([t1, t2]) => match (&egraph[*t1].data, &egraph[*t2].data) {
                    (MioAnalysisData::Dataflow(d1), MioAnalysisData::Dataflow(d2)) => {
                        let reads = d1.reads.union(&d2.reads).cloned().collect();
                        let writes = d1.writes.union(&d2.writes).cloned().collect();
                        MioAnalysis::new_dataflow_data(reads, writes, None)
                    }
                    _ => panic!("Seq expects children to be tables/dataflows"),
                },
                Mio::Ite([cond, lb, rb]) => {
                    let cond_type = Self::get_type(egraph, *cond);
                    Self::type_unification(&cond_type, &MioType::Bool);
                    let reads = HashSet::from_iter(
                        Self::read_set(egraph, *cond)
                            .iter()
                            .chain(Self::read_set(egraph, *lb).iter())
                            .chain(Self::read_set(egraph, *rb).iter())
                            .cloned(),
                    );
                    let writes = HashSet::from_iter(
                        Self::write_set(egraph, *cond)
                            .iter()
                            .chain(Self::write_set(egraph, *lb).iter())
                            .chain(Self::write_set(egraph, *rb).iter())
                            .cloned(),
                    );

                    MioAnalysis::new_action_data(
                        reads,
                        writes,
                        Self::type_unification(
                            &Self::get_type(egraph, *lb),
                            &Self::get_type(egraph, *rb),
                        ),
                        None,
                        HashSet::new(),
                    )
                }
                Mio::Write([field, value]) => {
                    if let (MioAnalysisData::Action(_u), MioAnalysisData::Action(v)) =
                        (&egraph[*field].data, &egraph[*value].data)
                    {
                        let elaboration = Self::read_set(egraph, *field).clone();
                        return MioAnalysis::new_action_data(
                            v.reads.clone(),
                            v.writes.union(&elaboration).cloned().collect(),
                            v.checked_type.clone(),
                            v.constant.clone(),
                            elaboration,
                        );
                    }
                    panic!("Write operator takes a field and an update");
                }
                Mio::Keys(keys) => MioAnalysis::new_action_data(
                    keys.iter()
                        .map(|k| match &egraph[*k].data {
                            MioAnalysisData::Action(u) => u.reads.clone(),
                            _ => panic!("Key entries cannot be control nodes"),
                        })
                        .reduce(|x, y| x.union(&y).map(|x| x.into()).collect())
                        .unwrap_or_default(),
                    HashSet::new(),
                    MioType::Unknown,
                    None,
                    HashSet::new(),
                ),
                Mio::Elaborations(actions)
                | Mio::ArithAlu(actions)
                | Mio::RelAlu(actions)
                | Mio::BoolAlu(actions)
                | Mio::SAlu(actions)
                | Mio::Actions(actions) => {
                    let mut reads = HashSet::new();
                    let mut writes = HashSet::new();
                    let mut elaborations = HashSet::new();
                    for u in actions.iter().map(|id| &egraph[*id].data) {
                        match u {
                            MioAnalysisData::Action(u) => {
                                reads = reads.union(&u.reads).cloned().collect();
                                writes = writes.union(&u.writes).cloned().collect();
                                elaborations =
                                    elaborations.union(&u.elaborations).cloned().collect();
                            }
                            MioAnalysisData::Empty => (),
                            _ => {
                                panic!("Use control operators to compose applications");
                            }
                        }
                    }
                    MioAnalysis::new_action_data(
                        reads,
                        writes,
                        MioType::Unknown,
                        None,
                        elaborations,
                    )
                }
                Mio::GIte(params) => {
                    let keys_reads = match &egraph[params[0]].data {
                        MioAnalysisData::Action(u) => {
                            assert_eq!(u.writes.len(), 0, "Keys should not write to any variable");
                            u.reads.clone()
                        }
                        _ => panic!("Key entries cannot be control nodes"),
                    };
                    let (action_reads, action_writes) = match &egraph[params[1]].data {
                        MioAnalysisData::Action(u) => (u.reads.clone(), u.writes.clone()),
                        _ => panic!("Action entries cannot be control nodes"),
                    };
                    MioAnalysis::new_dataflow_data(
                        keys_reads.union(&action_reads).cloned().collect(),
                        action_writes.clone(),
                        // populated by the table converter
                        None,
                    )
                }
                Mio::BitNot(x) | Mio::Neg(x) => {
                    let _ = Self::type_unification(&Self::get_type(egraph, *x), &MioType::Int);
                    let constant = Self::eval_unop(enode, Self::get_constant(egraph, *x));
                    Self::new_action_data(
                        Self::read_set(egraph, *x).clone(),
                        Self::write_set(egraph, *x).clone(),
                        Self::get_type(egraph, *x),
                        constant,
                        HashSet::new(),
                    )
                }
                Mio::LNot(x) => {
                    let _ = Self::type_unification(&Self::get_type(egraph, *x), &MioType::Bool);
                    let constant = Self::eval_unop(enode, Self::get_constant(egraph, *x));
                    Self::new_action_data(
                        Self::read_set(egraph, *x).clone(),
                        Self::write_set(egraph, *x).clone(),
                        Self::get_type(egraph, *x),
                        constant,
                        HashSet::new(),
                    )
                }
                Mio::Add([a, b])
                | Mio::Sub([a, b])
                | Mio::Min([a, b])
                | Mio::Max([a, b])
                | Mio::BitAnd([a, b])
                | Mio::BitOr([a, b])
                | Mio::BitXor([a, b])
                | Mio::BitShl([a, b])
                | Mio::BitShr([a, b]) => {
                    // Note that for an update, `elaboration` is tracking the output variables
                    // these are propagated to `writes` to their parents
                    // However, when handling an e-class here, we only consider `elaboration`
                    // since computations (without the effects) can be replayed
                    let a_type = Self::get_type(egraph, *a);
                    let b_type = Self::get_type(egraph, *b);
                    let ret_type = Self::type_unification(&a_type, &b_type);
                    let _ = Self::type_unification(&ret_type, &MioType::Int);
                    let reads = Self::read_set(egraph, *a)
                        .union(Self::read_set(egraph, *b))
                        .cloned()
                        .collect();
                    let writes: HashSet<String> = Self::write_set(egraph, *a)
                        .union(Self::write_set(egraph, *b))
                        .cloned()
                        .collect();
                    let constant = Self::eval_binop(
                        enode,
                        Self::get_constant(egraph, *a),
                        Self::get_constant(egraph, *b),
                    );
                    Self::new_action_data(
                        reads,
                        writes
                            .union(
                                &Self::elaborations(egraph, *a)
                                    .union(Self::elaborations(egraph, *b))
                                    .cloned()
                                    .collect(),
                            )
                            .cloned()
                            .collect(),
                        ret_type,
                        constant,
                        HashSet::new(),
                    )
                }
                Mio::LAnd([a, b]) | Mio::LOr([a, b]) | Mio::LXor([a, b]) => {
                    let a_type = Self::get_type(egraph, *a);
                    let b_type = Self::get_type(egraph, *b);
                    let ret_type = Self::type_unification(&a_type, &b_type);
                    let _ = Self::type_unification(&ret_type, &MioType::Bool);
                    let reads = Self::read_set(egraph, *a)
                        .union(Self::read_set(egraph, *b))
                        .cloned()
                        .collect();
                    let writes: HashSet<_> = Self::write_set(egraph, *a)
                        .union(Self::write_set(egraph, *b))
                        .cloned()
                        .collect();
                    let constant = Self::eval_binop(
                        enode,
                        Self::get_constant(egraph, *a),
                        Self::get_constant(egraph, *b),
                    );
                    let elaborations = Self::elaborations(egraph, *a)
                        .union(Self::elaborations(egraph, *b))
                        .cloned()
                        .collect();
                    let writes = writes.union(&elaborations).cloned().collect();
                    Self::new_action_data(reads, writes, ret_type, constant, elaborations)
                }
                Mio::Eq([a, b])
                | Mio::Lt([a, b])
                | Mio::Gt([a, b])
                | Mio::Le([a, b])
                | Mio::Ge([a, b])
                | Mio::Neq([a, b]) => {
                    let a_type = Self::get_type(egraph, *a);
                    let b_type = Self::get_type(egraph, *b);
                    let ret_type = Self::type_unification(&a_type, &b_type);
                    let _ = Self::type_unification(&ret_type, &MioType::Int);
                    let reads = Self::read_set(egraph, *a)
                        .union(Self::read_set(egraph, *b))
                        .cloned()
                        .collect();
                    let writes: HashSet<_> = Self::write_set(egraph, *a)
                        .union(Self::write_set(egraph, *b))
                        .cloned()
                        .collect();
                    let constant = Self::eval_binop(
                        enode,
                        Self::get_constant(egraph, *a),
                        Self::get_constant(egraph, *b),
                    );
                    Self::new_action_data(
                        reads,
                        writes
                            .union(
                                &Self::elaborations(egraph, *a)
                                    .union(Self::elaborations(egraph, *b))
                                    .cloned()
                                    .collect(),
                            )
                            .cloned()
                            .collect(),
                        MioType::Bool,
                        constant,
                        HashSet::new(),
                    )
                }
                Mio::ArithAluOps(_) | Mio::RelAluOps(_) | Mio::BoolAluOps(_) => {
                    Self::new_action_data(
                        HashSet::new(),
                        HashSet::new(),
                        MioType::Unknown,
                        None,
                        HashSet::new(),
                    )
                }
                Mio::Read([field, pre_state]) => Self::new_action_data(
                    Self::read_set(egraph, *field).clone(),
                    Self::write_set(egraph, *pre_state).clone(),
                    Self::get_type(egraph, *field),
                    Self::get_constant(egraph, *field),
                    HashSet::new(),
                ),
                Mio::Constant(c) => {
                    let ty = match c {
                        Constant::Bool(_) => MioType::Bool,
                        Constant::Int(_) => MioType::Int,
                        Constant::BitInt(_, b) => MioType::BitInt(*b),
                    };
                    Self::new_action_data(
                        HashSet::new(),
                        HashSet::new(),
                        ty,
                        Some(c.clone()),
                        HashSet::new(),
                    )
                }
                Mio::Symbol(sym) => Self::new_action_data(
                    if sym.contains(".") {
                        HashSet::from([sym.clone()])
                    } else {
                        HashSet::new()
                    },
                    HashSet::new(),
                    if egraph.analysis.gamma.contains_key(sym) {
                        egraph.analysis.gamma[sym].clone()
                    } else {
                        // println!(
                        //     "Warning: Symbol {:?} not found in {:?}",
                        //     sym, egraph.analysis.gamma
                        // );
                        MioType::Int
                    },
                    egraph.analysis.context.get(sym).cloned(),
                    HashSet::new(),
                ),
            }
        }
    }
}

pub mod utils {
    use std::collections::{HashMap, HashSet};

    use egg::{Id, RecExpr};

    use crate::utils::RegionedMap;

    use super::{
        ir::{Constant, Mio, MioAnalysis},
        *,
    };

    #[derive(Debug, Clone, PartialEq)]
    pub enum Dependency {
        WAW,
        WAR,
        RAW,
        UNKNOWN,
        INDEPENDENT,
    }

    pub fn get_dependency(
        lhs_reads: &HashSet<String>,
        lhs_writes: &HashSet<String>,
        rhs_reads: &HashSet<String>,
        rhs_writes: &HashSet<String>,
    ) -> Dependency {
        let mut result = Dependency::INDEPENDENT;
        if lhs_writes.intersection(rhs_writes).count() > 0 {
            result = Dependency::WAW;
        }
        if lhs_reads.intersection(rhs_writes).count() > 0 {
            if result != Dependency::INDEPENDENT {
                return Dependency::UNKNOWN;
            } else {
                result = Dependency::WAR;
            }
        }
        if lhs_writes.intersection(rhs_reads).count() > 0 {
            if result != Dependency::INDEPENDENT {
                return Dependency::UNKNOWN;
            } else {
                result = Dependency::RAW;
            }
        }
        result
    }

    /// Big-step semantics of Mio
    fn interp_rec(rt: usize, expr: &RecExpr<Mio>, ctx: &HashMap<String, Mio>) -> Mio {
        let current = &expr.as_ref()[rt];
        match current {
            Mio::Ite([cond, lb, rb]) => {
                let cond = interp_rec(usize::from(*cond), expr, ctx);
                if let Mio::Constant(c) = cond {
                    if c.as_bool().unwrap() {
                        interp_rec(usize::from(*lb), expr, ctx)
                    } else {
                        interp_rec(usize::from(*rb), expr, ctx)
                    }
                } else {
                    panic!("Condition should be a boolean");
                }
            }
            Mio::GIte([keys, actions]) => {
                let keys = interp_rec(usize::from(*keys), expr, ctx);
                if let Mio::Keys(_keys) = keys {
                    if let Mio::Actions(_actions) = interp_rec(usize::from(*actions), expr, ctx) {
                        // can't really evaluate a table since
                        // entry values are not known at this time
                        todo!()
                    } else {
                        panic!("Actions expression should be an Actions node");
                    }
                } else {
                    panic!("Keys expression should be a Keys node");
                }
            }
            Mio::Constant(_) => current.clone(),
            Mio::Symbol(s) => {
                if let Some(c) = ctx.get(s) {
                    c.clone()
                } else {
                    current.clone()
                }
            }
            Mio::BitAnd([lhs, rhs])
            | Mio::BitOr([lhs, rhs])
            | Mio::BitXor([lhs, rhs])
            | Mio::BitShl([lhs, rhs])
            | Mio::BitShr([lhs, rhs])
            | Mio::Add([lhs, rhs])
            | Mio::Sub([lhs, rhs])
            | Mio::Eq([lhs, rhs])
            | Mio::Lt([lhs, rhs])
            | Mio::Gt([lhs, rhs])
            | Mio::Le([lhs, rhs])
            | Mio::Ge([lhs, rhs])
            | Mio::Neq([lhs, rhs])
            | Mio::LAnd([lhs, rhs])
            | Mio::LOr([lhs, rhs]) => {
                let lhs = interp_rec(usize::from(*lhs), expr, ctx);
                let rhs = interp_rec(usize::from(*rhs), expr, ctx);
                if let (Mio::Constant(c1), Mio::Constant(c2)) = (lhs, rhs) {
                    Mio::Constant(MioAnalysis::eval_binop(current, Some(c1), Some(c2)).unwrap())
                } else {
                    current.clone()
                }
            }
            Mio::Neg(x) | Mio::BitNot(x) | Mio::LNot(x) => {
                if let Mio::Constant(c) = interp_rec(usize::from(*x), expr, ctx) {
                    Mio::Constant(MioAnalysis::eval_unop(current, Some(c)).unwrap())
                } else {
                    current.clone()
                }
            }
            _ => unimplemented!(),
        }
    }

    pub fn interp_recexpr(expr: &RecExpr<Mio>, ctx: &HashMap<String, Mio>) -> Mio {
        interp_rec(expr.as_ref().len() - 1, expr, ctx)
    }
}

pub mod transforms {
    use std::{
        collections::{HashMap, HashSet},
        rc::Rc,
        thread::current,
    };

    use egg::{Analysis, EGraph, Id, Language, RecExpr};

    use crate::{
        language::ir::MioAnalysisData,
        p4::{
            self,
            p4ir::{Expr, Stmt, Table, UnOps},
        },
        utils::RegionedMap,
    };

    use super::{
        ir::{Constant, Mio, MioAnalysis},
        *,
    };

    pub fn insert_expr(
        expr: &p4::p4ir::Expr,
        built: &RegionedMap<String, (Expr, Id)>,
        condition: &Expr,
        recexpr: &mut RecExpr<Mio>,
        reads: &mut HashMap<String, Expr>,
    ) -> Id {
        match expr {
            Expr::Int(v) => recexpr.add(Mio::Constant(Constant::Int(*v))),
            Expr::Bool(b) => recexpr.add(Mio::Constant(Constant::Bool(*b))),
            Expr::Var(name) => {
                if let Some(v) = built.get(name) {
                    v.1
                } else {
                    if name.contains(".") {
                        reads.insert(name.clone(), condition.clone());
                    }
                    recexpr.add(Mio::Symbol(name.clone()))
                }
            }
            Expr::BinOpExpr(op, lhs, rhs) => {
                let lhs_id = insert_expr(lhs, built, condition, recexpr, reads);
                let rhs_id = insert_expr(rhs, built, condition, recexpr, reads);
                recexpr.add(op.to_mio(lhs_id, rhs_id))
            }
            Expr::UnOpExpr(op, expr) => {
                let expr_id = insert_expr(expr, built, condition, recexpr, reads);
                recexpr.add(op.to_mio(expr_id))
            }
        }
    }

    fn walk_stmt(
        stmt: &Stmt,
        built: RegionedMap<String, (Expr, Id)>,
        condition: &Expr,
        recexpr: &mut RecExpr<Mio>,
        reads: &mut HashMap<String, Expr>,
        writes: &mut HashMap<String, Expr>,
    ) -> RegionedMap<String, (Expr, Id)> {
        match stmt {
            Stmt::Block(stmts) => {
                let mut c = built;
                for stmt in stmts {
                    c = walk_stmt(stmt, c, condition, recexpr, reads, writes);
                }
                c
            }
            Stmt::Assign(field, v) => {
                if let Expr::Var(field) = field {
                    let v_id = insert_expr(v, &built, condition, recexpr, reads);
                    let mut c = built;
                    if field.contains(".") {
                        writes.insert(field.clone(), condition.clone());
                    }
                    c.insert(field.clone(), (condition.clone(), v_id));
                    c
                } else {
                    panic!("Assigning to non-variable");
                }
            }
            Stmt::Read(x, y) => {
                // let val = built.get(x).unwrap();
                let lhs = recexpr.add(Mio::Symbol(x.clone()));
                let rhs = recexpr.add(Mio::Symbol(y.clone()));
                recexpr.add(Mio::Read([lhs, rhs]));
                reads.insert(y.clone(), condition.clone());
                let mut c = built;
                c.insert(y.clone(), (condition.clone(), rhs));
                c.insert(x.clone(), (condition.clone(), lhs));
                c
            }
            Stmt::Write(x, y) => {
                let lhs = recexpr.add(Mio::Symbol(x.clone()));
                debug_assert!(built.contains_key(y));
                let rhs = built.get(y).unwrap().1;
                writes.insert(x.clone(), condition.clone());
                let id = recexpr.add(Mio::Write([lhs, rhs]));
                let mut c = built;
                c.insert(x.clone(), (condition.clone(), id));
                c
            }
            Stmt::If(cond, ib, eb) => {
                let mut current = built.clone();
                let parent = Rc::new(built);
                let ib_built = RegionedMap::new(Some(parent.clone()));
                let eb_built = RegionedMap::new(Some(parent));
                let ib_built = walk_stmt(ib, ib_built, cond, recexpr, reads, writes);
                let mut eb_built = walk_stmt(
                    eb,
                    eb_built,
                    &Expr::UnOpExpr(UnOps::Not, Box::new(cond.clone())),
                    recexpr,
                    reads,
                    writes,
                );
                let mut delta = HashMap::new();
                for ib_k in ib_built.keys() {
                    if eb_built.contains_key_local(ib_k) {
                        // both if branch and else branch modified
                        let ib_v = ib_built.get_local(ib_k).unwrap().clone();
                        let eb_v = eb_built.get_local(ib_k).unwrap().clone();
                        let eb_id = eb_v.1.clone();
                        let new_id = if ib_v.0.is_true() {
                            ib_v.1.clone()
                        } else {
                            let ib_cid = insert_expr(&ib_v.0, &current, condition, recexpr, reads);
                            recexpr.add(Mio::Ite([ib_cid, ib_v.1.clone(), eb_id]))
                        };
                        delta.insert(ib_k.clone(), (condition.clone(), new_id));
                        eb_built.remove(ib_k);
                    } else {
                        let ib_v = ib_built.get_local(ib_k).unwrap().clone();
                        let new_id = if ib_v.0.is_true() {
                            ib_v.1.clone()
                        } else {
                            let eb = if current.contains_key(ib_k) {
                                let (cond, value) = current.get(ib_k).unwrap();
                                if cond.is_true() {
                                    value.clone()
                                } else {
                                    let default_branch =
                                        insert_expr(cond, &current, condition, recexpr, reads);
                                    let sym = recexpr.add(Mio::Symbol(ib_k.clone()));
                                    recexpr.add(Mio::Ite([default_branch, value.clone(), sym]))
                                }
                            } else {
                                recexpr.add(Mio::Symbol(ib_k.clone()))
                            };
                            let e = Mio::Ite([
                                insert_expr(&ib_v.0, &current, condition, recexpr, reads),
                                ib_v.1.clone(),
                                eb,
                            ]);
                            recexpr.add(e)
                        };
                        delta.insert(ib_k.clone(), (condition.clone(), new_id));
                    }
                }
                for eb_k in eb_built.keys() {
                    if ib_built.contains_key(eb_k) {
                        continue;
                    }
                    let eb_v = eb_built.get(eb_k).unwrap().clone();
                    let ib = if current.contains_key(eb_k) {
                        current.get(eb_k).unwrap().1.clone()
                    } else {
                        recexpr.add(Mio::Symbol(eb_k.clone()))
                    };
                    let e = Mio::Ite([
                        insert_expr(&eb_v.0, &current, condition, recexpr, reads),
                        eb_v.1.clone(),
                        ib.clone(),
                    ]);
                    let new_id = recexpr.add(e);
                    delta.insert(eb_k.clone(), (condition.clone(), new_id));
                }
                for (k, v) in delta.into_iter() {
                    current.insert(k, v);
                }
                current
            }
        }
    }

    pub fn stmt_to_recexpr(
        stmt: &Stmt,
    ) -> (
        RecExpr<Mio>,
        RegionedMap<String, (Expr, Id)>,
        HashMap<String, Expr>,
        HashMap<String, Expr>,
    ) {
        let mut recexpr = RecExpr::<Mio>::default();
        let mut reads = HashMap::new();
        let mut writes = HashMap::new();
        let built = RegionedMap::default();
        let built = walk_stmt(
            stmt,
            built,
            &Expr::Bool(true),
            &mut recexpr,
            &mut reads,
            &mut writes,
        );
        (recexpr, built, reads, writes)
    }

    pub fn tables_to_egraph(mut tables: Vec<Table>) -> (EGraph<Mio, MioAnalysis>, Id) {
        let mut egraph = EGraph::<Mio, MioAnalysis>::default();
        let mut table_ids = vec![];
        while let Some(table) = tables.pop() {
            let mut action_elaborations = vec![];
            let table_name_id = egraph.add(Mio::Symbol(table.name.clone()));
            for (_action_name, action) in table.actions {
                let (recexpr, built, _reads, writes) = stmt_to_recexpr(&action);
                let mut worklist = vec![];
                for k in writes.keys() {
                    debug_assert!(built.contains_key(k));
                    let (_, id) = built.get(k).unwrap();
                    worklist.push((k.clone(), *id));
                }
                worklist.sort_by(|a, b| b.1.cmp(&a.1));
                let mut action_ids = vec![];
                while let Some((k, id)) = worklist.pop() {
                    let expr = recexpr[id].build_recexpr(|id| recexpr[id].clone());
                    println!("{} =>\n{}", k, expr.pretty(80));
                    let egraph_id = egraph.add_expr(&expr);
                    let egraph_id = egraph.add(Mio::Elaborate([table_name_id, egraph_id]));
                    if let MioAnalysisData::Action(u) = &mut egraph[egraph_id].data {
                        println!("Action update {}:\n{:?}", k, u);
                        u.writes = u
                            .writes
                            .union(&HashSet::from([k.clone()]))
                            .cloned()
                            .collect();
                        u.elaborations = HashSet::from([k.clone()]);
                    } else {
                        panic!("Should be an action data for {}", k);
                    }
                    action_ids.push(egraph_id);
                }
                action_elaborations.push(action_ids);
            }
            let keys = table
                .keys
                .iter()
                .map(|k| egraph.add(Mio::Symbol(k.clone())))
                .collect();
            let actions = action_elaborations
                .iter()
                .map(|ids| egraph.add(Mio::Elaborations(ids.clone())))
                .collect();
            let keys_id = egraph.add(Mio::Keys(keys));
            let actions_id = egraph.add(Mio::Actions(actions));
            let gite_id = egraph.add(Mio::GIte([keys_id, actions_id]));
            match egraph[gite_id].data {
                MioAnalysisData::Dataflow(ref mut d) => {
                    d.table_name = Some(table.name.clone());
                }
                _ => panic!("GIte should have dataflow data"),
            }
            if table_ids.len() == 0 {
                table_ids.push(gite_id);
            } else {
                let prev_id = table_ids.pop().unwrap();
                let seq_id = egraph.add(Mio::Seq([gite_id, prev_id]));
                table_ids.push(seq_id);
            }
        }
        return (egraph, table_ids.pop().unwrap());
    }
}

mod test {
    use std::collections::{HashMap, HashSet};

    use egg::{EGraph, Id, Language, RecExpr};

    use super::{
        ir::{Constant, Mio, MioAnalysis},
        transforms::{stmt_to_recexpr, tables_to_egraph},
    };
    use crate::{
        language::utils::interp_recexpr,
        p4::{
            example_progs,
            macros::*,
            p4ir::{interp, Expr, Stmt},
        },
    };

    #[test]
    fn test_table_to_egraph() {
        tables_to_egraph(example_progs::rcp());
    }

    fn run_walk_stmt(stmts: Stmt, ctx: &HashMap<String, Mio>) {
        let (recexpr, built, _reads, _writes) = stmt_to_recexpr(&stmts);
        // egraph.dot().to_pdf("stmt_to_egraph.pdf").unwrap();
        println!("Stmt:\n{:?}", stmts);
        let mut p4ctx = ctx.clone();
        interp(&stmts, &mut p4ctx);
        for (v, val) in built.iter() {
            let expr = recexpr[val.1].build_recexpr(|id| recexpr[id].clone());
            let result = interp_recexpr(&expr, &ctx);
            let default = &Mio::Symbol(v.clone());
            let stmt_eval = p4ctx.get(v).unwrap_or(default);
            println!(
                "Stmt eval: {:?}",
                p4ctx.get(v).unwrap_or(&Mio::Symbol(v.clone()))
            );
            println!("Mio eval: {:?}", result);
            assert_eq!(stmt_eval, &result);
        }
    }

    fn extract_unit(egraph: &EGraph<Mio, MioAnalysis>, root: Id) -> RecExpr<Mio> {
        let mut worklist = vec![root];
        let mut visited = HashSet::new();
        let mut mem: HashMap<Id, Id> = HashMap::new();
        visited.insert(root);

        let mut result = RecExpr::<Mio>::default();

        while !worklist.is_empty() {
            let front = *worklist.last().unwrap();
            let node = egraph[front].nodes[0].clone();
            let mut ok = true;
            for child in node.children() {
                if !visited.contains(&child) {
                    worklist.push(child.clone());
                    ok = false;
                }
            }
            if ok {
                let new_id = result.add(node.map_children(|c| mem[&c]));
                mem.insert(front, new_id);
                visited.insert(front);
                worklist.pop();
            }
        }
        return result;
    }

    #[test]
    fn test_walk_stmt() {
        let ctx = HashMap::from([
            ("c1".to_string(), Mio::Constant(Constant::Bool(true))),
            ("c2".to_string(), Mio::Constant(Constant::Bool(false))),
            ("c3".to_string(), Mio::Constant(Constant::Bool(false))),
            ("c4".to_string(), Mio::Constant(Constant::Bool(true))),
            ("c".to_string(), Mio::Constant(Constant::Bool(true))),
        ]);
        let stmt = block!(
            assign!("a" => Expr::Int(1)),
            ite!(
                var!("c1"),
                block!(
                    ite!(not!(var!("c3")), assign!("b" => Expr::Int(10)), block!()),
                    ite!(
                        var!("c2"),
                        ite!(
                            var!("c3"),
                            assign!("a" => Expr::Int(2)),
                            assign!("a" => var!("b"))
                        ),
                        assign!("a" => Expr::Int(4))
                    )
                ),
                assign!("a" => Expr::Int(5))
            )
        );
        run_walk_stmt(stmt, &ctx);
        let stmt1 = Stmt::Block(vec![
            Stmt::Assign(Expr::Var("a".to_string()), Expr::Int(1)),
            Stmt::Assign(Expr::Var("b".to_string()), Expr::Int(2)),
            Stmt::If(
                Expr::Var("c".to_string()),
                Box::new(Stmt::Assign(Expr::Var("a".to_string()), Expr::Int(3))),
                Box::new(Stmt::Assign(Expr::Var("b".to_string()), Expr::Int(4))),
            ),
        ]);
        run_walk_stmt(stmt1, &ctx);

        let stmt2 = block!(
            assign!("a" => Expr::Int(1)),
            assign!("b" => Expr::Int(2)),
            ite!(
                var!("c1"),
                ite!(
                    var!("c2"),
                    assign!("a" => var!("b")),
                    assign!("b" => Expr::Int(4))
                ),
                block!(
                    assign!("a" => Expr::Int(5)),
                    ite!(
                        and!(var!("c3"), var!("c4")),
                        assign!("b" => Expr::Int(6)),
                        block!(
                            assign!("b" => Expr::Int(7)),
                            assign!("a" => add!(var!("a"), var!("b")))
                        )
                    )
                )
            )
        );
        run_walk_stmt(stmt2, &ctx);
    }
}
