# Graffiti.pc #189: degree six and connectivity at least three through order 17

Let a finite connected simple graph on at most seventeen vertices remain
connected after deletion of fewer than three vertices. Suppose the even
distance set at each vertex, including itself, has at most seven vertices
and at most one vertex has degree below six. Then the graph has a spanning
simple path.

The previous order-16 argument forces a longest path to have at least
twelve edges after the endpoint normalization. At order 17, a high omitted
vertex would have exactly three path attachments and would see all three
other omitted vertices. A second such high vertex and the paired-pin
exclusion force its six flanks to saturate its distance-two budget. The
same holds after every same-support rotation, eliminating a chord needed
by the endpoint mark count. After this excludes any high omitted vertex,
the unique-low-vertex argument again forces too long a path.

Main declaration:
`Graffiti189LongestPath.SixThreeSeventeen.traceable_six_at_three_connectivity_order_seventeen`.
Use Lean and Mathlib 4.19.0 and
[the order-16 proof objects](../graffiti-189-degree-six-three-connected-sixteen/)
and their prerequisites on LEAN_PATH. Compile the six modules in the
order listed in StrictReplay.log. All audited axioms are standard only.
