use core::num;
use std::collections::HashSet;

use egg::{CostFunction, EGraph, Extractor, Language};

use crate::language::ir::{Mio, MioAnalysis};

pub struct GreedyExtractor<'a> {
    pub egraph: &'a EGraph<Mio, MioAnalysis>,
    pub stateful_update_limit: usize,
    pub stateless_update_limit: usize,
    pub effect_disjoint: bool,
    pub stateful_reg_per_alu: usize,
    whitelist: HashSet<Mio>,
}

impl<'a> GreedyExtractor<'a> {
    pub fn new(egraph: &'a EGraph<Mio, MioAnalysis>, stateful_reg_per_alu: usize) -> Self {
        Self {
            egraph,
            stateful_update_limit: usize::MAX,
            stateless_update_limit: usize::MAX,
            effect_disjoint: false,
            whitelist: HashSet::new(),
            stateful_reg_per_alu,
        }
    }
}

impl<'a> CostFunction<Mio> for GreedyExtractor<'a> {
    type Cost = usize;

    fn cost<C>(&mut self, enode: &Mio, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        // AstDepth with exception that `join` operators are considered not
        // increasing the depth of the tree.
        let base: usize = match enode {
            Mio::Join(_) => 0,
            Mio::ArithAlu(chs) | Mio::RelAlu(chs) => {
                if self.whitelist.contains(enode) {
                    for ch in chs.iter() {
                        for node in self.egraph[*ch].nodes.iter() {
                            match node {
                                Mio::ArithAlu(_) | Mio::RelAlu(_) => {
                                    self.whitelist.insert(node.clone());
                                }
                                _ => {}
                            }
                        }
                    }
                    self.whitelist.remove(enode);
                    0
                } else {
                    usize::MAX
                }
            }
            Mio::SAlu(chs) => {
                for ch in chs.iter() {
                    for node in self.egraph[*ch].nodes.iter() {
                        match node {
                            Mio::ArithAlu(_) | Mio::RelAlu(_) => {
                                self.whitelist.insert(node.clone());
                            }
                            _ => {}
                        }
                    }
                }
                1
            }
            Mio::ArithAluOps(_) | Mio::BoolAluOps(_) | Mio::RelAluOps(_) => 0,
            Mio::GIte(_) => 1,
            Mio::Actions(_) => 1,
            Mio::Elaborations(_) => 0,
            Mio::Elaborate([_, v, e]) => {
                if MioAnalysis::stateful_reads(self.egraph, *e)
                    .union(&MioAnalysis::stateful_reads(self.egraph, *v))
                    .count()
                    > self.stateful_reg_per_alu
                {
                    return usize::MAX;
                }
                // println!("{:?} <== {:?}", self.egraph[*v].nodes, MioAnalysis::has_stateful_reads(self.egraph, *e));
                if MioAnalysis::has_stateful_reads(self.egraph, *v)
                    || MioAnalysis::has_stateful_reads(self.egraph, *e)
                {
                    let mut is_mapped = false;
                    for node in self.egraph[*e].nodes.iter() {
                        match node {
                            Mio::SAlu(_) => {
                                is_mapped = true;
                            }
                            _ => {}
                        }
                    }
                    if is_mapped {
                        0
                    } else {
                        usize::MAX
                    }
                } else {
                    for node in self.egraph[*e].nodes.iter() {
                        match node {
                            Mio::ArithAlu(_) | Mio::RelAlu(_) => {
                                self.whitelist.insert(node.clone());
                            }
                            _ => {}
                        }
                    }
                    0
                }
            }
            Mio::Keys(_) => 1,
            Mio::Seq(_) => 1,
            Mio::Symbol(_) => 0,
            Mio::Constant(_) => 0,
            _ => 1000,
        };
        let child_cost = enode.fold(0, |max, id| max.max(costs(id)));
        base.saturating_add(child_cost)
    }
}
