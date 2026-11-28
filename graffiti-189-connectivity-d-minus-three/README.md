# Graffiti.pc #189: complete range d≥403, connectivity at least d−3

The finite graph theorem `traceable_of_connectivity_d_minus_three` assumes
k≥400, connectedness after deleting fewer than k vertices, up to k+4
even-distance vertices at each vertex (including itself), and that any two
distinct vertices include one of degree at least k+3. It concludes a spanning
path. Thus take d=k+3; unlike the earlier d−2 result, this includes the
entire finite graph class with connectivity exactly d−3 in this degree range.
No normalized root, path geometry, or cut-shape premise is required.

The proof groups third-shell gateways using their omitted-shore donors.
When donors are sparse, several gateways share one distance-two budget; when
dense, adjacent donors' distinct representative gateways already occupy many
distance-two slots. The resulting order upper bound contradicts the weighted
spacing lower bound from a k-hook fan and terminal routes in a large shore.
Hall with deficit six and the already formalized one-low-degree circumference
bound supply shore connectivity and those routes.

`DeficitThreeAll189.lean` is the verified amalgamation of the source fragments
under `modules/`, with foundational imports hoisted. Replay with Lean/Mathlib
4.19 and prior #189 theorem objects on LEAN_PATH. This is not unrestricted
Graffiti.pc #189.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
