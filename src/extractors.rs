use egg::{CostFunction, Extractor, Language};

use crate::language::ir::Mio;

pub struct GreedyExtractor;
impl CostFunction<Mio> for GreedyExtractor {
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
            Mio::Ite(_) => 1,
            Mio::GIte(_) => 1,
            Mio::Actions(_) => 1,
            Mio::Elaborations(_) => 1,
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
