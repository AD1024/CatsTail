# CatsTail: Compiling packet programs via Equality Saturation
## TODOs
- Implement rewrites, including table parallelizing, merging and algebraic simplifications
- Create some test cases

## Questions
- Tagged elaboration may cause issues when two tables have common (sub-)expressions in their actions because this can cause the elaboration set include fields that are written to from both tables. However, read/write analysis depends on the elaboration tags, which might make some table include fields being written to from another table into their write set. 
    - Potential solution: making the elaboration tag not simply a `HashSet` but `HashMap<TableTag, FieldId>` so that when aggregating read/write sets for a table, we can know which fields that are tagged with the elaboration should we include. This will also require us to make the read/write set to be `HashMap<TableTag, FieldId>`.