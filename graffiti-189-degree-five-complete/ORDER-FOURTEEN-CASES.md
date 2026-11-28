# Graffiti.pc #189, order fourteen at the degree-five threshold

Take a finite connected simple graph with at most one degree below 5 and at most six even-distance vertices from every vertex (including the starting vertex). The target at this threshold is a spanning path. Earlier checked reductions eliminate orders at least 15 and, at order 14, reduce an obstruction to an adjacent two-cut with shores of orders 1 and 11. The other order-14 cuts have already been covered.

Let the adjacent cut be a,b. A large-shore vertex is classified by which endpoint is nearer (a, b, or equal), and whether its nearer distance is even or odd; these six classes give the usual ordered profile (EA, EB, EC, OA, OB, OC). Exchange a and b when necessary. The exact previous arithmetic/profile dispatcher gives five remaining canonical rows. Existing direct arguments rule out the three rows with EC=0. For the remaining two rows:

* EC1 profile (2,3,1,1,2,2). Both equal-odd vertices are neighboring both terminals (common ports), and all three strict-odd vertices are neighboring their nearer terminal. The distance-two dark part consists of the two EA vertices, three EB vertices, and the sole EC vertex e. The checked finite adjacency implications force a path from a through one common port, then e, then the other common port, then the sole A-exclusive port. That port adjoins both EA vertices. Removing e and the ports, EA∪EB induces a five-vertex graph of minimum degree three. The fixed-terminal Ore theorem gives a spanning path from one EA vertex to a selected EB vertex. It extends to a B-exclusive port, then b, then the other B-exclusive port. Prepend the singleton and a to get the required path.
* EC2 profile (2,2,2,1,1,3). There are two or three common ports. With two common ports, the one remaining equal-odd (dark) vertex has distances (3,3). The six even-distance vertices have their prescribed depth-two profiles; both strict-odd vertices are ports. The resulting normalized geometry is impossible: a kernel-checked RUP refutation turns the degree, required edges, and even-distance budget into a contradiction. The three-common case has a separate routing certificate.

The finite proof is not an unchecked solver invocation. Lean establishes the truth of every retained CNF root clause for an arbitrary simple graph under the exact labeled hypotheses. A proof term then refutes the supplied DIMACS clauses via the accompanying LRAT/RUP records. The bridge case uses the refutation on the negation of the required edges; the final path is constructed from actual walks and a checked Ore result, never from a SAT route witness. A graph isomorphism transports the results back from Fin 14; surjectivity of the labeling follows from coverage of each exact class, not an assumption that the classes exhaust the graph.

Combining order fourteen with the earlier order bound reduces any degree-five counterexample to order at most 13. Neither this package nor such an order reduction addresses the remaining order-at-most-13 argument or arbitrary second-smallest degree.

## Replay and declarations

This directory contains the EC1-multi and EC2-two-common branches. The
three-common route and final adjacent-cut dispatcher belong to separate
packages. The two graph-level entry points live in
`Graffiti189LongestPath.CrossSaturation.FiveAdjacent.SingletonRUP`:

* `traceable_of_adjacent_singleton_eleven_EC1_multi`
* `no_order_fourteen_EC2_two_common`

Use Lean 4.19.0, Mathlib 4.19.0, and prior checked objects on LEAN_PATH,
including the singleton order-fourteen EC1 package, the order-sixteen
singleton depth tools, and the earlier adjacent two-cut path toolkit.
The proof-term helpers `DiversityElevenMathlibRup384b` and
`DiversityElevenCircuitBits384b` are reused from the #384b formalization;
they must also appear on LEAN_PATH including their checked Mathlib
`FromLRAT` dependency. Run `replay.sh` to check the manifest, then build
the modules from source in order with warnings promoted to errors.
