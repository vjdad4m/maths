# Graffiti.pc #189: degree six, connectivity at least three, order 20

This is a partial result. In a connected graph of order 20 with vertex connectivity at least three, at most one vertex of degree below six, and at most seven vertices at even distance from each vertex (including itself), any nonspanning longest path has 13 or 14 edges. The result does not settle either of those lengths.

The initial reduction leaves lengths 13, 14 and 18. At length 18 only one vertex is omitted. Endpoint swaps and path rotations exclude this final long-path case.

The entry point is `longest_nonspanning_length_thirteen_or_fourteen` in `SixThree20ShortFrontier189.lean`. The dependencies through order 19 are in the [previous package](../graffiti-189-degree-six-three-connected-nineteen/). Replayed with Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. The final theorem uses only propext, Classical.choice and Quot.sound.
