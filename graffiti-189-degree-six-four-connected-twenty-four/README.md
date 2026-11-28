# Graffiti.pc #189: order 24 at second-degree threshold six

The original even-distance bound suffices for traceability of every
finite connected simple graph on at most 24 vertices, under the
degree-six threshold and connectivity at least four. The degree premise
requires that among any two vertices at least one has degree at least
six. The even-distance cap is seven vertices including the center.
This is a partial result for the conjecture, not an unrestricted proof.

The normalized longest-path reduction leaves the following frontier
beyond the earlier order-23 theorem:

- With a five-vertex active omitted component and spine length 17 or
  18, four pin positions have exactly one short gap. Even when other
  omitted vertices are present, the saturated residual distance-two
  budget controls the cheap pin and the adjacent flanks. Endpoint
  counts, three explicit longer-path substitutions, and a
  three-charge obstruction exclude all layouts.
- With a six-vertex active omitted component and spine length 17, the
  induced graph has a Hamilton path between every pair of terminals
  except at most one unordered pair. There are too many high vertices
  requiring pins for that single exceptional pair to cover.
- For the two outer-pair edge cases with seven or eight omitted vertices,
  the internal distance-two charges and the cheap-pin charges together
  leave at most two neighbors beyond the three known endpoint choices.
- With a nine-vertex active omitted component and spine length 14,
  two exclusive cheap pairs exhaust the pins. The other high vertices
  contain a six-vertex marked core with minimum degree three, giving a
  longer substitution.

Main: `Graffiti189LongestPath.SixFourOrderTwentyFour.traceable_order_twenty_four`.
All declared proof endpoints use only standard Lean axioms. Checked
RUP proof terms establish the finite marked-wing claims; a SAT solver
is not used during replay.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
