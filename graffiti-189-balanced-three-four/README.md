# Graffiti.pc #189: common (3,4) versus exclusive (2,3)

In the named orientation the four-contact endpoint on the common shore corresponds to the three-contact endpoint on the all-exclusive shore. All other assumptions are the degree-five Graffiti.pc #189 premises and actual two-component distance-two 2-cut with at least two common contacts on the common shore. Both mixed and nonmixed alternatives are covered. General #189 and reversed alignment (4,3) vs (2,3) are not covered.

The full theorem for this case is `traceable_of_balanced_three_four_opposite_two_three`. With Lean 4.19.0 and Mathlib v4.19.0, first compile dependencies of the earlier [(3,3) package](../graffiti-189-balanced-three-three/) and make those objects available on the search path. Compile this package in `modules.txt` order using `-j1 -s 65536 -DElab.async=false -DwarningAsError=true`. The full theorem for this cut case was replayed with only propext, Classical.choice, and Quot.sound.
