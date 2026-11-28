# Graffiti.pc #189: no order-24 graph at exact degree six and connectivity at least three

Let G be a finite connected simple graph such that each vertex has at most
seven vertices at even distance (including itself). Assume deletion of
fewer than three vertices preserves connectivity, at most one vertex has
degree less than six, and a degree-six vertex exists. Then G cannot have
order 24. Combined with the separately established order-at-most-24
bound under the same hypotheses, this gives order at most 23.

Exact theorem:
`Graffiti189LongestPath.Equality24Profile.impossible_order_twenty_four_at_degree_six_three_connected`
in `src/Equality24Complete189.lean`. This is an order exclusion, not a
spanning-path proof for the remaining orders.

The exact degree-six root has radius at most four and second shell at least
four. A minimum cover of the third shell by first-shell selectors has
three or four selectors with distinct private second-shell representatives.
The third shell has size 11 or 12 and the cover has capacity 12. Thus it
is a full partition, a partition with one group one short, or full with
one shared vertex. Canonical labeling pins the exceptional group or shared
vertex and preserves a private third-shell witness for each selector.
There are 16 resulting frames. Each LRAT RUP trace is replayed through
kernel-checked proof terms and its exact CNF is identified with the checked
list of typed rules. No solver result or external checker is trusted.

## Replay

Lean 4.19.0 and its pinned Mathlib. Put these predecessor object closures
on LEAN_PATH:
- [order-24 second shell](../graffiti-189-degree-six-order24-second-shell/),
  and the transitive radius and equality modules used by it;
- `SixLayer25Cover189`, from `proof-sources.zip` in
  [degree-six connectivity-four proof](../graffiti-189-degree-six-four-connected-complete/);
- `GraphSat189` and `GraphRup189`, with the pinned Mathlib
  `Mathlib.Tactic.Sat.FromLRAT` object, as used by that same proof.

Run `./replay.sh` with `lean` on PATH. It compiles one module at a time.
The retained final frame files are the replay inputs: regeneration using
CaDiCaL is optional and not part of verification. The diagnostic generator
and both solver-selection logs describe those inputs. The T4B4M0 frame
uses the already checked strong pilot; the remaining frames use the smaller
initial-plus-learned choice from the two variants. All 16 and the final
dispatcher use standard axioms only.

`Equality24SecondSmallest189.lean` instantiates the required degree-six
root from the exact second-smallest-degree-six condition, expressed by
the pairwise lower bound and two distinct degrees at most six. It also
gives the order-at-most-23 conclusion when supplied the previous
order-at-most-24 bound. See [prerequisite pins](PREREQUISITES.md).
