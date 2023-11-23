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
            Mio::ArithAluOps(_) | Mio::RelAluOps(_) => 0,
            // Mio::Ite(_) => 1,
            Mio::GIte(_) => 1,
            Mio::Actions(_) => 1,
            Mio::Elaborations(elabs) => {
                let mut num_stateful_updates = HashSet::new();
                let mut num_stateless_upates = HashSet::new();
                let mut c = 0;
                for elaboration in elabs.iter() {
                    if MioAnalysis::has_stateful_elaboration(self.egraph, *elaboration) {
                        num_stateful_updates
                            .extend(MioAnalysis::elaborations(self.egraph, *elaboration).iter());
                    }
                    if MioAnalysis::has_stateless_elaboration(self.egraph, *elaboration) {
                        num_stateless_upates
                            .extend(MioAnalysis::elaborations(self.egraph, *elaboration).iter());
                    }
                    if num_stateful_updates.len() > self.stateful_update_limit
                        || num_stateless_upates.len() > self.stateless_update_limit
                    {
                        c = usize::MAX;
                    }
                    if self.effect_disjoint {
                        if num_stateful_updates.len() > 1 && num_stateless_upates.len() > 1 {
                            c = usize::MAX;
                        }
                    }
                }
                c
            }
            Mio::Elaborate([_, v, e]) => {
                if MioAnalysis::has_stateful_reads(self.egraph, *v) {
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
                        let gvar = MioAnalysis::get_symbol(self.egraph, *v);
                        if MioAnalysis::read_set(self.egraph, *e)
                            .iter()
                            .filter(|&x| x != &gvar)
                            .count()
                            <= self.stateful_reg_per_alu
                        {
                            0
                        } else {
                            usize::MAX
                        }
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
            _ => usize::MAX,
        };
        let child_cost = enode.fold(0, |max, id| max.max(costs(id)));
        base.saturating_add(child_cost)
    }
}
