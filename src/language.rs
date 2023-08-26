use egg;

pub mod ir {
    use std::{
        collections::{HashMap, HashSet},
        hash::Hash,
    };

    use egg::{define_language, Analysis, Id};

    define_language! {
        pub enum Mio {
            "ite" = Ite([Id; 3]),
            "table" = Table([Id; 3]),
            "keys" = Keys(Vec<Id>),
            "actions" = Actions(Vec<Id>),
            "mapsto" = MapsTo([Id; 2]),
            "list" = List(Vec<Id>),
            // putting tables in the same stage
            "join" = Join(Vec<Id>),
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
                    MioAnalysisData {
                        max_read: reads,
                        max_write: writes,
                        local_reads,
                        local_writes,
                    }
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
                    }
                }
                Mio::MapsTo([field, value]) => {
                    let reads = egraph[*value].data.max_read.clone();
                    let writes = HashSet::from([*field]);
                    MioAnalysisData {
                        local_reads: HashMap::from([(enode.clone(), reads.clone())]),
                        local_writes: HashMap::from([(enode.clone(), writes.clone())]),
                        max_read: reads,
                        max_write: writes,
                    }
                }
                Mio::Keys(keys) => {
                    let reads = keys
                        .iter()
                        .map(|id| egraph[*id].data.max_read.clone())
                        .reduce(|a, b| a.union(&b).cloned().collect())
                        .unwrap_or_default();
                    MioAnalysisData {
                        max_read: reads.clone(),
                        max_write: HashSet::new(),
                        local_reads: HashMap::from([(enode.clone(), reads)]),
                        local_writes: HashMap::from([(enode.clone(), HashSet::new())]),
                    }
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
                    MioAnalysisData {
                        max_read: reads.clone(),
                        max_write: writes.clone(),
                        local_reads: HashMap::from([(enode.clone(), reads)]),
                        local_writes: HashMap::from([(enode.clone(), writes)]),
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
                    let mut reads = egraph[params[0]].data.max_read.clone();
                    let mut writes = egraph[params[1]].data.max_write.clone();

                    MioAnalysisData {
                        max_read: reads.clone(),
                        max_write: writes.clone(),
                        local_reads: HashMap::from([(enode.clone(), reads)]),
                        local_writes: HashMap::from([(enode.clone(), writes)]),
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
