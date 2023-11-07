use egg;

pub mod ir {
    use std::ops;
    use std::{
        collections::{HashMap, HashSet},
        fmt::Display,
        hash::Hash,
        str::FromStr,
    };

    use egg::{define_language, Analysis, DidMerge, Id};

    define_language! {
        pub enum Mio {
            "ite" = Ite([Id; 3]),
            // (GIte (keys k1 k2 k3...) (actions a1 a2 a3 ... default))
            "gite" = GIte([Id; 2]),
            "keys" = Keys(Vec<Id>),
            "actions" = Actions(Vec<Id>),
            // putting tables in the same stage; equivalent to T1 || T2
            // (join ?t1 ?t2)
            "join" = Join([Id; 2]),
            // Stage barrier; (seq ?t1 ?t2) denotes
            // putting t2 after the stage of t1
            "seq" = Seq([Id; 2]),
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
                _ => panic!("Addition of non-integers"),
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
    }

    impl Default for MioAnalysis {
        fn default() -> Self {
            MioAnalysis {
                context: HashMap::new(),
                gamma: HashMap::new(),
            }
        }
    }

    impl MioAnalysis {
        pub fn new(ctx: HashMap<String, Constant>, gamma: HashMap<String, MioType>) -> Self {
            MioAnalysis {
                context: ctx,
                gamma,
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
        ) -> MioAnalysisData {
            MioAnalysisData::Dataflow(RWAnalysis { reads, writes })
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
            }
        }

        pub fn write_set<'a>(egraph: &'a egg::EGraph<Mio, Self>, id: Id) -> &'a HashSet<String> {
            match &egraph[id].data {
                MioAnalysisData::Action(u) => &u.writes,
                MioAnalysisData::Dataflow(d) => &d.writes,
            }
        }

        pub fn elaborations<'a>(egraph: &'a egg::EGraph<Mio, Self>, id: Id) -> &'a HashSet<String> {
            match &egraph[id].data {
                MioAnalysisData::Action(u) => &u.elaborations,
                _ => panic!("Dataflow {:?} has no elaborations", id),
            }
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq, Default)]
    pub struct RWAnalysis {
        // For checking whether dataflow is preserved
        // by rewrites; used for Control nodes and tables
        pub reads: HashSet<String>,
        pub writes: HashSet<String>,
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
    }

    impl Analysis<Mio> for MioAnalysis {
        type Data = MioAnalysisData;

        fn modify(egraph: &mut egg::EGraph<Mio, Self>, id: Id) {
            // when there are constants, we can add a new node to the e-class
            // with the constant value
            if let MioAnalysisData::Action(ActionAnalysis {
                constant: Some(constant),
                ..
            }) = &egraph[id].data
            {
                let new_id = egraph.add(Mio::Constant(constant.clone()));
                egraph.union(id, new_id);
            }
        }

        fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
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
                        MioAnalysis::new_dataflow_data(reads, writes)
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
                Mio::Actions(actions) => {
                    let mut reads = HashSet::new();
                    let mut writes = HashSet::new();
                    let mut elaborations = HashSet::new();
                    for u in actions.iter().map(|id| &egraph[*id].data) {
                        match u {
                            MioAnalysisData::Dataflow(d) => {
                                panic!("Use control operators to compose applications");
                            }
                            MioAnalysisData::Action(u) => {
                                reads = reads.union(&u.reads).cloned().collect();
                                writes = writes.union(&u.writes).cloned().collect();
                                elaborations =
                                    elaborations.union(&u.elaborations).cloned().collect();
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
                        ret_type,
                        constant,
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
                    HashSet::new(),
                    HashSet::new(),
                    if egraph.analysis.gamma.contains_key(sym) {
                        egraph.analysis.gamma[sym].clone()
                    } else {
                        // println!(
                        //     "Warning: Symbol {:?} not found in {:?}",
                        //     sym, egraph.analysis.gamma
                        // );
                        MioType::Unknown
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
    use std::rc::Rc;

    use egg::{EGraph, Id};

    use crate::{
        p4::{
            self,
            p4ir::{Expr, Stmt, UnOps},
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
        egraph: &mut EGraph<Mio, MioAnalysis>,
    ) -> Id {
        match expr {
            Expr::Int(v) => egraph.add(Mio::Constant(Constant::Int(*v))),
            Expr::Bool(b) => egraph.add(Mio::Constant(Constant::Bool(*b))),
            Expr::Var(name) => {
                if let Some(v) = built.get(name) {
                    v.1
                } else {
                    egraph.add(Mio::Symbol(name.clone()))
                }
            }
            Expr::BinOpExpr(op, lhs, rhs) => {
                let lhs_id = insert_expr(lhs, built, egraph);
                let rhs_id = insert_expr(rhs, built, egraph);
                egraph.add(op.to_mio(lhs_id, rhs_id))
            }
            Expr::UnOpExpr(op, expr) => {
                let expr_id = insert_expr(expr, built, egraph);
                egraph.add(op.to_mio(expr_id))
            }
        }
    }

    fn walk_stmt(
        stmt: &Stmt,
        built: RegionedMap<String, (Expr, Id)>,
        condition: &Expr,
        egraph: &mut EGraph<Mio, MioAnalysis>,
    ) -> RegionedMap<String, (Expr, Id)> {
        match stmt {
            Stmt::Block(stmts) => {
                let mut c = built;
                for stmt in stmts {
                    c = walk_stmt(stmt, c, condition, egraph);
                }
                c
            }
            Stmt::Assign(field, v) => {
                if let Expr::Var(field) = field {
                    let v_id = insert_expr(v, &built, egraph);
                    let mut c = built;
                    c.insert(field.clone(), (condition.clone(), v_id));
                    c
                } else {
                    panic!("Assigning to non-variable");
                }
            }
            Stmt::Read(x, y) => {
                // let val = built.get(x).unwrap();
                let lhs = egraph.add(Mio::Symbol(x.clone()));
                let rhs = egraph.add(Mio::Symbol(y.clone()));
                egraph.add(Mio::Read([lhs, rhs]));
                let mut c = built;
                c.insert(y.clone(), (condition.clone(), rhs));
                c
            }
            Stmt::Write(x, y) => {
                let lhs = egraph.add(Mio::Symbol(x.clone()));
                let rhs = insert_expr(y, &built, egraph);
                egraph.add(Mio::Write([lhs, rhs]));
                built
            }
            Stmt::If(cond, ib, eb) => {
                let mut current = built.clone();
                let parent = Rc::new(built);
                let ib_built = RegionedMap::new(Some(parent.clone()));
                let eb_built = RegionedMap::new(Some(parent));
                let ib_built = walk_stmt(ib, ib_built, cond, egraph);
                let mut eb_built = walk_stmt(
                    eb,
                    eb_built,
                    &Expr::UnOpExpr(UnOps::Not, Box::new(cond.clone())),
                    egraph,
                );
                // In theory we can use an SMT solver to check whether path conditions are
                // negations of each other; this will gives us a compact ite representation.
                // w/o SMT, we can get an ite representation in the form of
                // ite(c1, e1, ite(c2, e2, ...)) fall-through to default value
                for ib_k in ib_built.keys() {
                    if eb_built.contains_key_local(ib_k) {
                        let ib_v = ib_built.get_local(ib_k).unwrap().clone();
                        let eb_v = eb_built.get_local(ib_k).unwrap().clone();
                        let eb = if current.contains_key(ib_k) {
                            let (cond, body) = current.get(ib_k).unwrap();
                            let default_branch = insert_expr(cond, &current, egraph);
                            let sym = egraph.add(Mio::Symbol(ib_k.clone()));
                            egraph.add(Mio::Ite([default_branch, body.clone(), sym]))
                        } else {
                            egraph.add(Mio::Symbol(ib_k.clone()))
                        };
                        let eb_vid = insert_expr(&eb_v.0, &current, egraph);
                        let e = Mio::Ite([
                            insert_expr(&ib_v.0, &current, egraph),
                            ib_v.1.clone(),
                            egraph.add(Mio::Ite([eb_vid, eb_v.1.clone(), eb])),
                        ]);
                        let new_id = egraph.add(e);
                        current.insert(ib_k.clone(), (condition.clone(), new_id));
                        eb_built.remove(ib_k);
                    } else {
                        let ib_v = ib_built.get_local(ib_k).unwrap().clone();
                        let eb = if current.contains_key(ib_k) {
                            let (cond, value) = current.get(ib_k).unwrap();
                            let default_branch = insert_expr(cond, &current, egraph);
                            let sym = egraph.add(Mio::Symbol(ib_k.clone()));
                            egraph.add(Mio::Ite([default_branch, value.clone(), sym]))
                        } else {
                            egraph.add(Mio::Symbol(ib_k.clone()))
                        };
                        let e =
                            Mio::Ite([insert_expr(&ib_v.0, &current, egraph), ib_v.1.clone(), eb]);
                        let new_id = egraph.add(e);
                        current.insert(ib_k.clone(), (condition.clone(), new_id));
                    }
                }
                for eb_k in eb_built.keys() {
                    let eb_v = eb_built.get(eb_k).unwrap().clone();
                    let ib = if current.contains_key(eb_k) {
                        current.get(eb_k).unwrap().1.clone()
                    } else {
                        egraph.add(Mio::Symbol(eb_k.clone()))
                    };
                    let e = Mio::Ite([
                        insert_expr(&eb_v.0, &current, egraph),
                        eb_v.1.clone(),
                        ib.clone(),
                    ]);
                    let new_id = egraph.add(e);
                    current.insert(eb_k.clone(), (condition.clone(), new_id));
                }
                current
            }
        }
    }

    pub fn stmt_to_egraph(
        stmt: &Stmt,
    ) -> (EGraph<Mio, MioAnalysis>, RegionedMap<String, (Expr, Id)>) {
        let mut egraph = EGraph::new(MioAnalysis::default());
        let built = RegionedMap::default();
        let built = walk_stmt(stmt, built, &Expr::Bool(true), &mut egraph);
        (egraph, built)
    }
}

mod test {
    use std::collections::{HashMap, HashSet};

    use egg::{EGraph, Id, Language, RecExpr};

    use super::{
        ir::{Constant, Mio, MioAnalysis},
        transforms::stmt_to_egraph,
    };
    use crate::{
        language::utils::interp_recexpr,
        p4::{
            macros::*,
            p4ir::{interp, Expr, Stmt},
        },
    };

    fn run_walk_stmt(stmts: Stmt, ctx: &HashMap<String, Mio>) {
        let (egraph, built) = stmt_to_egraph(&stmts);
        // egraph.dot().to_pdf("stmt_to_egraph.pdf").unwrap();
        println!("Stmt:\n{:?}", stmts);
        let mut p4ctx = ctx.clone();
        interp(&stmts, &mut p4ctx);
        for (v, val) in built.iter() {
            let expr = extract_unit(&egraph, val.1);
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
