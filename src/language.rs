use egg;

pub mod ir {
    use std::collections::{HashMap, HashSet};

    use egg::{define_language, Analysis, Id};

    define_language! {
        pub enum Mio {
            "ite" = Ite([Id; 3]),
            "table" = Table(Vec<Id>),
            // "split" = Split(Vec<Id>),
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
            // Arithmetic operators
            "add" = Add([Id; 2]),
            "sub" = Sub([Id; 2]),
            "store" = Store([Id; 2]),
            "load" = Load(Id),
            Symbol(String),
            Number(i32),
        }
    }

    pub struct MioAnalysis;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct MioAnalysisData {
        pub local_reads: HashMap<Mio, HashSet<Id>>,
        pub local_writes: HashMap<Mio, HashSet<Id>>,
        pub max_read: HashSet<Id>,
        pub max_write: HashSet<Id>,
    }

    impl Default for MioAnalysisData {
        fn default() -> Self {
            MioAnalysisData {
                local_reads: HashMap::new(),
                local_writes: HashMap::new(),
                max_read: HashSet::new(),
                max_write: HashSet::new(),
            }
        }
    }

    impl Analysis<Mio> for MioAnalysis {
        type Data = MioAnalysisData;

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
            let new = MioAnalysisData {
                max_read,
                max_write,
                local_reads,
                local_writes,
            };
            return egg::DidMerge(new != *a, new != b);
        }

        fn make(egraph: &egg::EGraph<Mio, Self>, enode: &Mio) -> Self::Data {
            match enode {
                Mio::Table(params) => {
                    let mut reads = HashSet::new();
                    let mut writes = HashSet::new();
                    for param in params {
                        reads.extend(egraph[*param].data.max_read.clone());
                        writes.extend(egraph[*param].data.max_write.clone());
                    }
                    let predicates = params[..params.len() / 2].to_vec();
                    let branches = params[params.len() / 2..params.len() - 1].to_vec();
                    let local_reads = HashMap::from([(
                        enode.clone(),
                        predicates
                            .iter()
                            .chain(branches.iter())
                            .map(|id| egraph[*id].data.max_read.clone())
                            .reduce(|a, b| a.union(&b).cloned().collect())
                            .unwrap_or_default(),
                    )]);
                    let local_writes = HashMap::from([(
                        enode.clone(),
                        branches
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
                    }
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
                    MioAnalysisData {
                        max_read: max_reads,
                        max_write: max_writes,
                        local_reads,
                        local_writes,
                    }
                }
                Mio::BitNot(x) | Mio::LNot(x) => egraph[*x].data.clone(),
                Mio::Add([a, b])
                | Mio::Sub([a, b])
                | Mio::BitAnd([a, b])
                | Mio::BitOr([a, b])
                | Mio::BitXor([a, b])
                | Mio::LAnd([a, b])
                | Mio::LOr([a, b])
                | Mio::LXor([a, b]) => {
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
                    }
                }
                Mio::Store([field, val]) => {
                    let reads = egraph[*val].data.max_read.clone();
                    let mut writes = egraph[*val].data.max_write.clone();
                    writes.insert(field.clone());
                    let local_reads = HashMap::from([(enode.clone(), reads.clone())]);
                    let local_writes =
                        HashMap::from([(enode.clone(), HashSet::from([field.clone()]))]);
                    MioAnalysisData {
                        max_read: reads,
                        max_write: writes,
                        local_reads,
                        local_writes,
                    }
                }
                Mio::Load(field) => MioAnalysisData {
                    max_read: HashSet::from([field.clone()]),
                    max_write: HashSet::new(),
                    local_reads: HashMap::from([(enode.clone(), HashSet::from([field.clone()]))]),
                    local_writes: HashMap::new(),
                },
                Mio::Symbol(_) | Mio::Number(_) => Default::default(),
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
    enum Dependency {
        WAW,
        WAR,
        RAW,
        UNKNOWN,
    }

    fn get_dependency(
        lhs_reads: &HashSet<Id>,
        lhs_writes: &HashSet<Id>,
        rhs_reads: &HashSet<Id>,
        rhs_writes: &HashSet<Id>,
    ) -> Dependency {
        let mut result = Dependency::UNKNOWN;
        if lhs_writes.intersection(rhs_writes).count() > 0 {
            result = Dependency::WAW;
        }
        if lhs_reads.intersection(rhs_writes).count() > 0 {
            if result != Dependency::UNKNOWN {
                return Dependency::UNKNOWN;
            } else {
                result = Dependency::WAR;
            }
        }
        if lhs_writes.intersection(rhs_reads).count() > 0 {
            if result != Dependency::UNKNOWN {
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
    ) -> Option<Mio> {
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
                    for i in 0..predicates_lhs.len() {
                        for j in 0..predicates_rhs.len() {
                            // merge entry i of lhs and entry j of rhs
                            let predicate =
                                egraph.add(Mio::LAnd([predicates_lhs[i], predicates_rhs[j]]));
                        }
                    }
                    Some(Mio::Table(vec![]))
                }
                _ => unimplemented!(),
            }
        } else {
            None
        }
    }
}
