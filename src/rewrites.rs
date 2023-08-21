use egg::Rewrite;

use crate::language;

type RW = Rewrite<language::ir::Mio, language::ir::MioAnalysis>;

// pub fn waw_elim() -> RW {
//     // WAW elimination is done by
//     // 1. merge matching keys
//     // 2. merge actions
// }
