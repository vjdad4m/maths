# Graffiti.pc #189: one-exception terminal routing

**Strict Lean partial.** At connectivity at least (d-2), under the exact cap and the second-smallest-degree hypothesis, a nontraceable graph has:

* at least **22 vertices** for (d=6);
* at least **(5d-8) vertices** for (d\ge7).

These strengthen the previous first-slack bounds but do not finish the unrestricted-order or low-connectivity cases.

[BorderWing189](src/BorderWing189.lean) handles an omitted component of order at most (2d-6). It gives a path between any distinct prescribed terminals that omits at most one vertex of the component. The only potentially low-degree vertex is deleted first: every remaining vertex has induced degree at least (d-3) and the remaining order is at most (2d-7), so the remaining graph satisfies terminal Ore. If the exceptional vertex is itself a terminal, it has at least two internal neighbors and can be attached through a neighbor different from the other terminal, giving a spanning terminal path. Splicing this route forces a long gap between pins of distinct porters.

[SixBorder189](src/SixBorder189.lean) uses this for omitted components of order five or six. On a hypothetical counterexample of order at most 21, four pins in the narrow interval force two disjoint short gaps. A short gap has just one common porter, and there are too few porters among the four pins to account for the high-degree vertices of the component.

[UltraOrder189](src/UltraOrder189.lean) excludes the borderline component order (2d-6) for a hypothetical counterexample of order at most (5d-9); the smaller-component argument counts blocks starting at index one instead of zero to retain one more position.

Lean and Mathlib 4.19.0. Compile the previous first-slack package (including WideWing189 and its prerequisite TerminalOreAdapter199), append the precompiled prerequisites to the Mathlib LEAN_PATH, and run replay.sh. Builds use warnings as errors and a fresh object directory.
