# Graffiti.pc #189: the omitted-component order bound

Lean proves that for second-smallest degree (d\ge7) and connectivity at least (d-2), any counterexample to #189 has order at least (5d-9). This strengthens the [normalized attachment and order bound](../graffiti-189-high-pin-order). The full conjecture remains open.

The omitted component either already has at least (2d-6) vertices, or has enough internal degree for terminal Ore to give a spanning path between any two distinct prescribed vertices. In the latter case, the path game forbids close pins supported by distinct porters. Counting pin positions with this stronger separation gives the stated bound. See [the wing lemmas](src/WideWing189.lean) and [the final theorem](src/FurtherOrder189.lean).

Use Lean and Mathlib 4.19.0. Compile the preceding order-bound package and its dependencies and the public TerminalOreAdapter199 from [the reserved-edge splice package](../graffiti-199-single-exception-closure), then replay these two files with `bash replay.sh` and the resulting object directories on LEAN_PATH. The [recorded replay](StrictReplay.log) rebuilt the four prerequisite order modules along with these two and reports only standard axioms. No bounded graph search is used.
