# Graffiti.pc #189: half-connectivity range

Assume that a finite connected simple graph has at most d+1 even-distance
vertices from every vertex, counting the vertex itself, and that any two
distinct vertices include one of degree at least d. Assume deleting
any set of fewer than k vertices preserves connectivity. If
**k ≥ 1,000,000 and 2k ≥ d + 100**, then the graph has a spanning path.
This is a restricted result, asymptotically down to half the degree
threshold. The unrestricted conjecture is not resolved by it.

The proof uses a longest path with a high omitted root. If the omitted
star minus that root is robust, the one-low Pósa cycle bound supplies
the terminal routes. Otherwise a small cut splits the star. A robust
large side supports its own long cycle and nearly k disjoint hooks,
with at most one of those hooks discarded to avoid the universal root.
Two small sides instead admit prescribed-terminal spanning paths by
one-exception Ore. Nonrobustness of a large side supplies a third side
after one extra deletion; each nonflexible first port misses at least
two of the three sides. The spacing bounds combine with the shell-three
donor mass estimates in all branches.

Main theorem
`Graffiti189LongestPath.HalfBandDeficit.traceable_of_half_connectivity`
is in `HalfBandCombined189.lean`. Separate editable sources are in
`modules/`. Replay with the pinned Lean, Mathlib, and earlier #189
compiled interfaces on LEAN_PATH.

See the [final declaration](HalfBandDeficit189.lean), [strict replay log](VERIFIED.log), and [five-ninths predecessor](../graffiti-189-five-ninths-connectivity/).

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
