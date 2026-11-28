# Graffiti.pc #189, d=6: further restrictions on three-cut components

Under the degree-six Graffiti hypotheses and 3-connectivity (defined
by connectedness after deleting fewer than three vertices), a
three-vertex separator leaves at most two components if either one
component is a singleton or every vertex outside the separator has
degree at least six. No restriction on edges inside the separator is
needed. The actual-graph theorems are
`Graffiti189LongestPath.ThresholdSix.ThreeCut.three_cut_at_most_two_with_singleton`
and `Graffiti189LongestPath.ThresholdSix.ThreeCut.three_cut_at_most_two_of_high_outside`.

In a prospective three-component deletion with nonsingleton shores,
`no_two_universal_nonsingleton_shores` rules out universal terminal
ports on two different shores. This is not a spanning-path theorem.

## Replay

Use Lean/Mathlib v4.19.0. Put the object closure of the
[isolated-terminal three-cut package](../graffiti-189-degree-six-three-cut-isolated-terminal/)
on LEAN_PATH. Compile the modules in the displayed order of
StrictReplay.log with `-j1 -s32768 -DElab.async=false -DwarningAsError=true`.
The axiom output contains only propext, Classical.choice, Quot.sound.
