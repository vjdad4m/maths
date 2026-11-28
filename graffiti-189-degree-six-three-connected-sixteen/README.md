# Graffiti.pc #189: degree six and connectivity at least three through order 16

Let a finite connected simple graph on at most sixteen vertices remain
connected after deletion of fewer than three vertices. Suppose every
even-distance set (counting its center) has cardinality at most seven,
and every pair of distinct vertices contains one of degree at least six.
Then there is a spanning simple path. This is not the unrestricted
degree-six theorem.

An unspanning longest path can rotate to have two high endpoints. Their
disjoint endpoint marks force at least twelve edges. A high omitted
vertex can have at most three neighbors on the path, hence requires
at least three other omitted vertices, which is impossible at this
order. There is therefore a unique low omitted vertex. Its three
attachment positions have disjoint flanks that fill its even-distance
budget. If either endpoint were joined to a non-near attachment,
rotation would make a former flank an endpoint. Its only new flank
position would force a prohibited gap of two in the original path.
Counting the resulting holes in the two endpoint-mark sets forces a
path too long for the graph.

Main theorem:
`Graffiti189LongestPath.SixThreeSixteen.traceable_six_at_three_connectivity_order_sixteen`.
Use Lean and Mathlib 4.19.0, with earlier
`PinRunSeparator189`, `MultiPinRotation189`, `Rigidity189`, `OneSlack189` and
`SmallSeparator189` on LEAN_PATH. Compile the four modules in the order shown
by StrictReplay.log. All audited declarations use only the standard axioms.
