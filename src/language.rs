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
            "store" = Store([Id; 2]),
            "load" = Load(Id),
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
                _ => panic!("Bitwise not of non-integers"),
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
    }

    impl Default for MioAnalysisData {
        fn default() -> Self {
            MioAnalysisData {
                local_reads: HashMap::new(),
                local_writes: HashMap::new(),
                max_read: HashSet::new(),
                max_write: HashSet::new(),
                constant: None,
                checked_type: MioType::Unknown,
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
                },
                Mio::Global(v) => MioAnalysisData {
                    max_read: HashSet::new(),
                    max_write: HashSet::new(),
                    local_reads: HashMap::new(),
                    local_writes: HashMap::new(),
                    constant: None,
                    checked_type: egraph[*v].data.checked_type.clone(),
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
                    if let (MioType::Table(t1), MioType::Table(t2)) = (&egraph[tables[0]].data.checked_type, &egraph[tables[1]].data.checked_type) {
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
                    }
                }
                Mio::Store([field, value]) | Mio::MapsTo([field, value]) => {
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
                    }
                }
                Mio::Load(field) => MioAnalysisData {
                    max_read: HashSet::from([field.clone()]),
                    max_write: HashSet::new(),
                    local_reads: HashMap::from([(enode.clone(), HashSet::from([field.clone()]))]),
                    local_writes: HashMap::new(),
                    constant: None,
                    checked_type: egraph[*field].data.checked_type.clone(),
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
                    }
                }
                Mio::Symbol(sym) => MioAnalysisData {
                    max_read: HashSet::new(),
                    max_write: HashSet::new(),
                    local_reads: HashMap::new(),
                    local_writes: HashMap::new(),
                    constant: egraph.analysis.context.get(&enode.to_string()).cloned(),
                    checked_type: if (egraph.analysis.gamma.contains_key(sym)) {
                        egraph.analysis.gamma[sym].clone()
                    } else {
                        // println!(
                        //     "Warning: Symbol {:?} not found in {:?}",
                        //     sym, egraph.analysis.gamma
                        // );
                        MioType::Unknown
                    },
                },
            }
        }
    }
}

pub mod utils {
    use std::collections::HashSet;

    use egg::Id;

    use super::{
        ir::{Mio, MioAnalysis},
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

    pub fn merge_branch(lhs: &Mio, rhs: &Mio) {}

    pub fn merge_table(
        egraph: &mut egg::EGraph<Mio, MioAnalysis>,
        lhs: &Mio,
        rhs: &Mio,
        lhs_reads: &HashSet<Id>,
        lhs_writes: &HashSet<Id>,
        rhs_reads: &HashSet<Id>,
        rhs_writes: &HashSet<Id>,
    ) -> Option<Id> {
        if let (Mio::Table(lhs_params), Mio::Table(rhs_params)) = (lhs, rhs) {
            match get_dependency(lhs_reads, lhs_writes, rhs_reads, rhs_writes) {
                Dependency::UNKNOWN => None,
                Dependency::WAW => {
                    let predicates_lhs = lhs_params[..lhs_params.len() / 2].to_vec();
                    let predicates_rhs = rhs_params[..rhs_params.len() / 2].to_vec();
                    let branches_lhs =
                        lhs_params[lhs_params.len() / 2..lhs_params.len() - 1].to_vec();
                    let branches_rhs =
                        rhs_params[rhs_params.len() / 2..rhs_params.len() - 1].to_vec();

                    let mut new_predicates = Vec::new();
                    let mut new_branches = Vec::new();
                    for (lb, lp) in branches_lhs.iter().zip(predicates_lhs.iter()) {
                        for (rb, rp) in branches_rhs.iter().zip(predicates_rhs.iter()) {
                            let lb_data = &egraph[*lb].data;
                            let rb_data = &egraph[*rb].data;
                            if lb_data.max_write.intersection(&rb_data.max_write).count() == 0 {
                                // Independent branches
                                new_predicates.push(lp.clone());
                                new_branches.push(lb.clone());
                                new_predicates.push(rp.clone());
                                new_branches.push(rb.clone());
                            }
                        }
                    }
                    todo!()
                }
                _ => unimplemented!(),
            }
        } else {
            panic!("merge_table called with non-table arguments");
        }
    }
}
