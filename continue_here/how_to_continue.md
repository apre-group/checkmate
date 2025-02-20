# How to continue

We are implementing the subtree-supertree mode for conditional actions.
We are considering whether and how the conditions in the subtree need to be propagated to the supetree and the other way round.

## Wi and Cr

Currently the conditions in the subtree do not really affect the result of the supertree.
The conditions in the supertree could be stored in the subtree as initial constraints, but if they are not,
the subtree will make additional case splits if necessary and some of the cases will never be applicable due
to further constraints in the conditions of the supertree.

## Pr

The conditions in the subtree should be considered in the analysis of the supertree, and they are to
some extent, as they are stored in the ConditionalUtilities data structure when we save the result of the subtree.
They are also in the solver during checking.

We however have an inconsistent example, where the entire tree is practical (`market-entry-conditional.json`), but the
supertree `market-supertree.json` (with inserted result of the subtree `market-subtree.json`) is reported to be
not practical. We do not know yet where the bug lies, but we suspect it is when we determine the overlapping or the
implication of the current case considered while analyzing the result of the subtree.