use egg;

pub mod ir {
    use std::ops;
    use std::{
        collections::{HashMap, HashSet},
        fmt::Display,
        hash::Hash,
        str::FromStr,
    };

    use egg::{define_language, Analysis, Id};

    define_language! {
        pub enum Mio {
            "ite" = Ite([Id; 3]),
            "table" = Table([Id; 3]),
            "keys" = Keys(Vec<Id>),
            "actions" = Actions(Vec<Id>),
            "mapsto" = MapsTo([Id; 2]),
            // lists
            "append" = Append([Id; 2]),
            "list" = List(Vec<Id>),
            // putting tables in the same stage;
            // (join ?t1 ?t2)
            "join" = Join([Id; 2]),
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
            "default" = DefaultTable,
            Constant(Constant),
            Symbol(String),
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum MioType {
        Bool,
        Int,
        Table(Vec<usize>),
        List(Box<MioType>, usize),
        ActionList(usize),
        Unknown,
        // Meta(i32),
    }

    #[derive(Debug, Clone, PartialEq, PartialOrd, Ord, Eq, Hash)]
    pub enum Constant {
        Int(i32),
        Bool(bool),
    }

    impl Display for Constant {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Constant::Int(i) => write!(f, "{}", i),
                Constant::Bool(b) => write!(f, "{}", b),
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
            match (self, rhs) {
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a + b),
                _ => panic!("Addition of non-integers"),
            }
        }
    }

    impl std::ops::Sub<Constant> for Constant {
        type Output = Constant;

        fn sub(self, rhs: Constant) -> Self::Output {
            match (self, rhs) {
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a - b),
                _ => panic!("Subtraction of non-integers"),
            }
        }
    }

    impl std::ops::BitAnd<Constant> for Constant {
        type Output = Constant;

        fn bitand(self, rhs: Constant) -> Self::Output {
            match (self, rhs) {
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a & b),
                _ => panic!("Bitwise and of non-integers"),
            }
        }
    }

    impl std::ops::BitOr<Constant> for Constant {
        type Output = Constant;

        fn bitor(self, rhs: Constant) -> Self::Output {
            match (self, rhs) {
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a | b),
                _ => panic!("Bitwise or of non-integers"),
            }
        }
    }

    impl std::ops::BitXor<Constant> for Constant {
        type Output = Constant;

        fn bitxor(self, rhs: Constant) -> Self::Output {
            match (self, rhs) {
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a ^ b),
                _ => panic!("Bitwise xor of non-integers"),
            }
        }
    }

    impl std::ops::Shl<Constant> for Constant {
        type Output = Constant;

        fn shl(self, rhs: Constant) -> Self::Output {
            match (self, rhs) {
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a << b),
                _ => panic!("Bitwise shift left of non-integers"),
            }
        }
    }

    impl std::ops::Shr<Constant> for Constant {
        type Output = Constant;

        fn shr(self, rhs: Constant) -> Self::Output {
            match (self, rhs) {
                (Constant::Int(a), Constant::Int(b)) => Constant::Int(a >> b),
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

        pub fn type_unification(&self, lhs_ty: &MioType, rhs_ty: &MioType) -> MioType {
            match (lhs_ty, rhs_ty) {
                (MioType::Bool, MioType::Bool) => MioType::Bool,
                (MioType::Int, MioType::Int) => MioType::Int,
                (MioType::List(t1, len_l), MioType::List(t2, len_r)) => {
                    assert_eq!(len_l, len_r);
                    MioType::List(Box::new(self.type_unification(t1, t2)), *len_l)
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
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct MioAnalysisData {
        pub local_reads: HashMap<Mio, HashSet<Id>>,
        pub local_writes: HashMap<Mio, HashSet<Id>>,
        pub max_read: HashSet<Id>,
        pub max_write: HashSet<Id>,
        pub constant: Option<Constant>,
        pub checked_type: MioType,
        pub elaboration: HashSet<String>,
    }

    impl Default for MioAnalysisData {
        fn default() -> Self {
            let x = 1;
            MioAnalysisData {
                local_reads: HashMap::new(),
                local_writes: HashMap::new(),
                max_read: HashSet::new(),
                max_write: HashSet::new(),
                constant: None,
                checked_type: MioType::Unknown,
                elaboration: HashSet::new(),
            }
        }
    }

    impl Analysis<Mio> for MioAnalysis {
        type Data = MioAnalysisData;

        fn modify(egraph: &mut egg::EGraph<Mio, Self>, id: Id) {
            // when there are constants, we can add a new node to the e-class
            // with the constant value
            if let Some(constant) = egraph[id].data.constant.clone() {
                let new_id = egraph.add(Mio::Constant(constant));
                egraph.union(id, new_id);
            }
        }

        fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> egg::DidMerge {
            let max_read = a.max_read.union(&b.max_read).cloned().collect();
            let max_write = a.max_write.union(&b.max_write).cloned().collect();
            let local_reads = a
                .local_reads
                .iter()
                .chain(b.local_reads.iter())
                .map(|(k, v)| {
                    let mut v = v.clone();
                    v.extend(b.local_reads.get(k).unwrap_or(&HashSet::new()).clone());
                    (k.clone(), v)
                })
                .collect();
            let local_writes = a
                .local_writes
                .iter()
                .chain(b.local_writes.iter())
                .map(|(k, v)| {
                    let mut v = v.clone();
                    v.extend(b.local_writes.get(k).unwrap_or(&HashSet::new()).clone());
                    (k.clone(), v)
                })
                .collect();
            let ty = self.type_unification(&a.checked_type, &b.checked_type);
            // println!("Unify {:?} {:?} to {:?}", a.checked_type, b.checked_type, ty);
            let new = MioAnalysisData {
                max_read,
                max_write,
                local_reads,
                local_writes,
                constant: a.constant.clone().or(b.constant.clone()),
                checked_type: ty,
                elaboration: a.elaboration.union(&b.elaboration).cloned().collect(),
            };
            return egg::DidMerge(new != *a, new != b);
        }

        fn make(egraph: &egg::EGraph<Mio, Self>, enode: &Mio) -> Self::Data {
            match enode {
                Mio::DefaultTable => MioAnalysisData {
                    max_read: HashSet::new(),
                    max_write: HashSet::new(),
                    local_reads: HashMap::new(),
                    local_writes: HashMap::new(),
                    constant: None,
                    checked_type: MioType::Table(vec![0]),
                    elaboration: HashSet::new(),
                },
                Mio::Global(v) => MioAnalysisData {
                    max_read: HashSet::new(),
                    max_write: HashSet::new(),
                    local_reads: HashMap::new(),
                    local_writes: HashMap::new(),
                    constant: None,
                    checked_type: egraph[*v].data.checked_type.clone(),
                    elaboration: HashSet::new(),
                },
                Mio::Join(tables) => {
                    let reads = tables
                        .iter()
                        .map(|id| egraph[*id].data.max_read.clone())
                        .reduce(|a, b| a.union(&b).cloned().collect())
                        .unwrap_or_default();
                    let writes = tables
                        .iter()
                        .map(|id| egraph[*id].data.max_write.clone())
                        .reduce(|a, b| a.union(&b).cloned().collect())
                        .unwrap_or_default();
                    let local_reads = HashMap::from([(enode.clone(), reads.clone())]);
                    let local_writes = HashMap::from([(enode.clone(), writes.clone())]);
                    if let (MioType::Table(t1), MioType::Table(t2)) = (
                        &egraph[tables[0]].data.checked_type,
                        &egraph[tables[1]].data.checked_type,
                    ) {
                        let mut sizes = HashSet::new();
                        for s1 in t1.iter() {
                            for s2 in t2.iter() {
                                sizes.insert(s1 + s2);
                            }
                        }
                        return MioAnalysisData {
                            max_read: reads,
                            max_write: writes,
                            local_reads,
                            local_writes,
                            constant: None,
                            checked_type: MioType::Table(sizes.into_iter().collect()),
                            elaboration: HashSet::new(),
                        };
                    }
                    panic!(
                        "Join expects two tables, {:?} and {:?} provided",
                        egraph[tables[0]].data.checked_type, egraph[tables[1]].data.checked_type
                    );
                }
                Mio::Append([xs, ys]) => {
                    let reads = egraph[*xs].data.max_read.clone();
                    let writes = egraph[*ys].data.max_write.clone();
                    let local_reads = HashMap::from([(enode.clone(), reads.clone())]);
                    let local_writes = HashMap::from([(enode.clone(), writes.clone())]);
                    if let (MioType::List(ty_l, len_l), MioType::List(ty_r, len_r)) = (
                        &egraph[*xs].data.checked_type,
                        &egraph[*ys].data.checked_type,
                    ) {
                        return MioAnalysisData {
                            max_read: reads,
                            max_write: writes,
                            local_reads,
                            local_writes,
                            constant: None,
                            checked_type: MioType::List(
                                Box::new(egraph.analysis.type_unification(&ty_l, &ty_r)),
                                len_l + len_r,
                            ),
                            elaboration: HashSet::new(),
                        };
                    }
                    panic!(
                        "Append expects two lists, {:?} and {:?} provided",
                        egraph[*xs].data.checked_type, egraph[*ys].data.checked_type
                    );
                }
                Mio::List(params) => {
                    let mut reads = HashSet::new();
                    let mut writes = HashSet::new();
                    for param in params {
                        reads.extend(egraph[*param].data.max_read.clone());
                        writes.extend(egraph[*param].data.max_write.clone());
                    }
                    let local_reads = HashMap::from([(
                        enode.clone(),
                        params
                            .iter()
                            .map(|id| egraph[*id].data.max_read.clone())
                            .reduce(|a, b| a.union(&b).cloned().collect())
                            .unwrap_or_default(),
                    )]);
                    let local_writes = HashMap::from([(
                        enode.clone(),
                        params
                            .iter()
                            .map(|id| egraph[*id].data.max_write.clone())
                            .reduce(|a, b| a.union(&b).cloned().collect())
                            .unwrap_or_default(),
                    )]);
                    MioAnalysisData {
                        max_read: reads,
                        max_write: writes,
                        local_reads,
                        local_writes,
                        constant: None,
                        checked_type: MioType::List(
                            Box::new(
                                params
                                    .iter()
                                    .map(|id| egraph[*id].data.checked_type.clone())
                                    .reduce(|x, y| egraph.analysis.type_unification(&x, &y))
                                    // TODO: a proper way is to use the e-class Id for Meta-typevars
                                    .unwrap_or(MioType::Unknown),
                            ),
                            params.len(),
                        ),
                        elaboration: HashSet::new(),
                    }
                }
                Mio::Write([field, value]) | Mio::MapsTo([field, value]) => {
                    let reads = egraph[*value].data.max_read.clone();
                    let writes = HashSet::from([*field]);
                    let ty = egraph.analysis.type_unification(
                        &egraph[*field].data.checked_type,
                        &egraph[*value].data.checked_type,
                    );
                    MioAnalysisData {
                        local_reads: HashMap::from([(enode.clone(), reads.clone())]),
                        local_writes: HashMap::from([(enode.clone(), writes.clone())]),
                        max_read: reads,
                        max_write: writes,
                        constant: egraph[*value].data.constant.clone(),
                        checked_type: ty,
                        elaboration: HashSet::new(),
                    }
                }
                Mio::Keys(keys) => {
                    let reads = keys
                        .iter()
                        .map(|id| egraph[*id].data.max_read.clone())
                        .reduce(|a, b| a.union(&b).cloned().collect())
                        .unwrap_or_default();
                    let checked_type = keys
                        .iter()
                        .map(|id| egraph[*id].data.checked_type.clone())
                        .reduce(|x, y| egraph.analysis.type_unification(&x, &y))
                        .unwrap_or(MioType::Unknown);
                    if let MioType::Bool = checked_type {
                        return MioAnalysisData {
                            max_read: reads.clone(),
                            max_write: HashSet::new(),
                            local_reads: HashMap::from([(enode.clone(), reads)]),
                            local_writes: HashMap::from([(enode.clone(), HashSet::new())]),
                            constant: None,
                            checked_type: MioType::List(Box::new(MioType::Bool), keys.len()),
                            elaboration: HashSet::new(),
                        };
                    }
                    panic!(
                        "All keys have to be of type Bool, {:?} provided",
                        checked_type
                    );
                }
                Mio::Actions(actions) => {
                    let reads = actions
                        .iter()
                        .map(|id| egraph[*id].data.max_read.clone())
                        .reduce(|a, b| a.union(&b).cloned().collect())
                        .unwrap_or_default();
                    let writes = actions
                        .iter()
                        .map(|id| egraph[*id].data.max_write.clone())
                        .reduce(|a, b| a.union(&b).cloned().collect())
                        .unwrap_or_default();
                    let param_types = actions
                        .iter()
                        .map(|id| egraph[*id].data.checked_type.clone())
                        .collect::<Vec<_>>();
                    param_types.iter().for_each(|x| match x {
                        MioType::List(_, _) => (),
                        _ => panic!("All actions have to be of type List, {:?} provided", x),
                    });

                    MioAnalysisData {
                        max_read: reads.clone(),
                        max_write: writes.clone(),
                        local_reads: HashMap::from([(enode.clone(), reads)]),
                        local_writes: HashMap::from([(enode.clone(), writes)]),
                        constant: None,
                        checked_type: MioType::ActionList(param_types.len()),
                        elaboration: HashSet::new(),
                    }
                }
                Mio::Table(params) => {
                    // (table (keys ?p1 ?p2 ... ?pn)
                    //        (actions
                    //          (list
                    //              (mapsto ?f1 ?v1)
                    //              (mapsto ?f2 ?v2) ...)
                    //          (list
                    //              (mapsto ?f3 ?v3) ...) ...)
                    //        ?parent)
                    let parent_type = egraph[params[2]].data.checked_type.clone();
                    if let MioType::Table(_) = parent_type {
                        let reads = egraph[params[0]].data.max_read.clone();
                        let writes = egraph[params[1]].data.max_write.clone();
                        let keys_type = egraph[params[0]].data.checked_type.clone();
                        let actions_type = egraph[params[1]].data.checked_type.clone();
                        if let (MioType::List(_, key_len), MioType::ActionList(action_len)) =
                            (&keys_type, &actions_type)
                        {
                            assert_eq!(key_len, action_len, "Keys and actions must have the same length, {:?} and {:?} provided in {:?}", key_len, action_len, enode);
                            return MioAnalysisData {
                                max_read: reads.clone(),
                                max_write: writes.clone(),
                                local_reads: HashMap::from([(enode.clone(), reads)]),
                                local_writes: HashMap::from([(enode.clone(), writes)]),
                                constant: None,
                                checked_type: MioType::Table(vec![key_len.clone()]),
                                elaboration: HashSet::new(),
                            };
                        }
                        panic!(
                            "Keys and actions must be lists, {:?} and {:?} provided in {:?}",
                            keys_type, actions_type, enode
                        );
                    }
                    panic!(
                        "The parent of a tables must also be a table, {:?} provided in {:?}",
                        parent_type, enode
                    );
                }
                Mio::Ite([cond, ib, eb]) => {
                    let max_reads = [cond, ib, eb]
                        .iter()
                        .map(|&id| egraph[*id].data.max_read.clone())
                        .reduce(|a, b| a.union(&b).cloned().collect())
                        .unwrap_or_default();
                    let max_writes = [cond, ib, eb]
                        .iter()
                        .map(|&id| egraph[*id].data.max_write.clone())
                        .reduce(|a, b| a.union(&b).cloned().collect())
                        .unwrap_or_default();
                    let local_reads = HashMap::from([(enode.clone(), max_reads.clone())]);
                    let local_writes = HashMap::from([(enode.clone(), max_writes.clone())]);
                    let _ = egraph
                        .analysis
                        .type_unification(&egraph[*cond].data.checked_type, &MioType::Bool);
                    let ty = egraph.analysis.type_unification(
                        &egraph[*ib].data.checked_type,
                        &egraph[*eb].data.checked_type,
                    );
                    MioAnalysisData {
                        max_read: max_reads,
                        max_write: max_writes,
                        local_reads,
                        local_writes,
                        constant: None,
                        checked_type: ty,
                        elaboration: HashSet::new(),
                    }
                }
                Mio::BitNot(x) | Mio::Neg(x) => {
                    let _ = egraph
                        .analysis
                        .type_unification(&egraph[*x].data.checked_type, &MioType::Int);
                    egraph[*x].data.clone()
                }
                Mio::LNot(x) => {
                    let _ = egraph
                        .analysis
                        .type_unification(&egraph[*x].data.checked_type, &MioType::Bool);
                    egraph[*x].data.clone()
                }
                Mio::Add([a, b])
                | Mio::Sub([a, b])
                | Mio::BitAnd([a, b])
                | Mio::BitOr([a, b])
                | Mio::BitXor([a, b])
                | Mio::BitShl([a, b])
                | Mio::BitShr([a, b]) => {
                    let _ = egraph
                        .analysis
                        .type_unification(&egraph[*a].data.checked_type, &MioType::Int);
                    let _ = egraph
                        .analysis
                        .type_unification(&egraph[*b].data.checked_type, &MioType::Int);
                    let mut reads = egraph[*a].data.max_read.clone();
                    reads.extend(egraph[*b].data.max_read.clone());
                    let mut writes = egraph[*a].data.max_write.clone();
                    writes.extend(egraph[*b].data.max_write.clone());
                    let local_reads = HashMap::from([(enode.clone(), reads.clone())]);
                    let local_writes = HashMap::from([(enode.clone(), writes.clone())]);
                    MioAnalysisData {
                        max_read: reads,
                        max_write: writes,
                        local_reads,
                        local_writes,
                        constant: MioAnalysis::eval_binop(
                            enode,
                            egraph[*a].data.constant.clone(),
                            egraph[*b].data.constant.clone(),
                        ),
                        checked_type: MioType::Int,
                        elaboration: HashSet::new(),
                    }
                }
                Mio::LAnd([a, b]) | Mio::LOr([a, b]) | Mio::LXor([a, b]) => {
                    let _ = egraph
                        .analysis
                        .type_unification(&egraph[*a].data.checked_type, &MioType::Bool);
                    let _ = egraph
                        .analysis
                        .type_unification(&egraph[*b].data.checked_type, &MioType::Bool);
                    let mut reads = egraph[*a].data.max_read.clone();
                    reads.extend(egraph[*b].data.max_read.clone());
                    let mut writes = egraph[*a].data.max_write.clone();
                    writes.extend(egraph[*b].data.max_write.clone());
                    let local_reads = HashMap::from([(enode.clone(), reads.clone())]);
                    let local_writes = HashMap::from([(enode.clone(), writes.clone())]);
                    MioAnalysisData {
                        max_read: reads,
                        max_write: writes,
                        local_reads,
                        local_writes,
                        constant: MioAnalysis::eval_binop(
                            enode,
                            egraph[*a].data.constant.clone(),
                            egraph[*b].data.constant.clone(),
                        ),
                        checked_type: MioType::Bool,
                        elaboration: HashSet::new(),
                    }
                }
                Mio::Eq([a, b])
                | Mio::Lt([a, b])
                | Mio::Gt([a, b])
                | Mio::Le([a, b])
                | Mio::Ge([a, b])
                | Mio::Neq([a, b]) => {
                    let _ = egraph
                        .analysis
                        .type_unification(&egraph[*a].data.checked_type, &MioType::Int);
                    let _ = egraph
                        .analysis
                        .type_unification(&egraph[*b].data.checked_type, &MioType::Int);
                    let mut reads = egraph[*a].data.max_read.clone();
                    reads.extend(egraph[*b].data.max_read.clone());
                    let mut writes = egraph[*a].data.max_write.clone();
                    writes.extend(egraph[*b].data.max_write.clone());
                    let local_reads = HashMap::from([(enode.clone(), reads.clone())]);
                    let local_writes = HashMap::from([(enode.clone(), writes.clone())]);
                    MioAnalysisData {
                        max_read: reads,
                        max_write: writes,
                        local_reads,
                        local_writes,
                        constant: MioAnalysis::eval_binop(
                            enode,
                            egraph[*a].data.constant.clone(),
                            egraph[*b].data.constant.clone(),
                        ),
                        checked_type: MioType::Bool,
                        elaboration: HashSet::new(),
                    }
                }
                Mio::Read([field, _]) => MioAnalysisData {
                    max_read: HashSet::from([field.clone()]),
                    max_write: HashSet::new(),
                    local_reads: HashMap::from([(enode.clone(), HashSet::from([field.clone()]))]),
                    local_writes: HashMap::new(),
                    constant: None,
                    checked_type: egraph[*field].data.checked_type.clone(),
                    elaboration: HashSet::new(),
                },
                Mio::Constant(c) => {
                    let ty = match c {
                        Constant::Bool(_) => MioType::Bool,
                        Constant::Int(_) => MioType::Int,
                    };
                    MioAnalysisData {
                        max_read: HashSet::new(),
                        max_write: HashSet::new(),
                        local_reads: HashMap::new(),
                        local_writes: HashMap::new(),
                        constant: Some(c.clone()),
                        checked_type: ty,
                        elaboration: HashSet::new(),
                    }
                }
                Mio::Symbol(sym) => MioAnalysisData {
                    max_read: HashSet::new(),
                    max_write: HashSet::new(),
                    local_reads: HashMap::new(),
                    local_writes: HashMap::new(),
                    constant: egraph.analysis.context.get(&enode.to_string()).cloned(),
                    checked_type: if egraph.analysis.gamma.contains_key(sym) {
                        egraph.analysis.gamma[sym].clone()
                    } else {
                        // println!(
                        //     "Warning: Symbol {:?} not found in {:?}",
                        //     sym, egraph.analysis.gamma
                        // );
                        MioType::Unknown
                    },
                    elaboration: HashSet::new(),
                },
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
        lhs_reads: &HashSet<Id>,
        lhs_writes: &HashSet<Id>,
        rhs_reads: &HashSet<Id>,
        rhs_writes: &HashSet<Id>,
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
                if let Mio::Constant(Constant::Bool(b)) = interp_rec(usize::from(*cond), expr, ctx)
                {
                    if b {
                        interp_rec(usize::from(*lb), expr, ctx)
                    } else {
                        interp_rec(usize::from(*rb), expr, ctx)
                    }
                } else {
                    panic!("Condition of ite must evaluate to a boolean");
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
    use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

    use egg::{EGraph, Id};

    use crate::{
        p4::{
            self,
            p4ir::{BinOps, Expr, Stmt, UnOps},
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
