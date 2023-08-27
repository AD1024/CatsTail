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
        let base = match enode {
            Mio::Join(_) => 0,
            _ => 1,
        };
        base + enode.fold(0, |max, id| max.max(costs(id)))
    }
}
