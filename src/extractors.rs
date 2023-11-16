use core::num;

use egg::{CostFunction, EGraph, Extractor, Language};

use crate::language::ir::{Mio, MioAnalysis};

pub struct GreedyExtractor<'a> {
    pub egraph: &'a EGraph<Mio, MioAnalysis>,
    pub stateful_update_limit: usize,
    pub stateless_update_limit: usize,
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
            Mio::ArithAlu(_) | Mio::RelAlu(_) | Mio::SAlu(_) => 1,
            Mio::ArithAluOps(_) | Mio::RelAluOps(_) => 0,
            // Mio::Ite(_) => 1,
            Mio::GIte(_) => 1,
            Mio::Actions(_) => 1,
            Mio::Elaborations(elabs) => {
                let mut num_stateful_updates = 0;
                let mut num_stateless_upates = 0;
                for elaboration in elabs.iter() {
                    if MioAnalysis::has_stateful_elaboration(self.egraph, *elaboration) {
                        num_stateful_updates += 1;
                    }
                    if MioAnalysis::has_stateless_elaboration(self.egraph, *elaboration) {
                        num_stateless_upates += 1;
                    }
                    if num_stateful_updates > self.stateful_update_limit
                        || num_stateless_upates > self.stateless_update_limit
                    {
                        return usize::MAX;
                    }
                }
                0
            }
            Mio::Elaborate(_) => 0,
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
