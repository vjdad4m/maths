# Graffiti.pc #384b when triangle count one is absent

**Every finite connected simple graph of order greater than two in which no vertex belongs to exactly one triangle satisfies the catalogue inequality** `γ₂(G) ≤ ⌊n − |T|/2⌋`. Here T is the set of distinct counts of incident triangles and includes a realized zero. The theorem is independent of graph order, number of leaves, and triangle-count diversity. [MissingOne.lean](MissingOne.lean)

**For the unrestricted conjecture, it suffices at every order cutoff to check one leaf attached to a connected, all-positive core where every edge is in a triangle and some degree-two vertex lies in exactly one triangle.** The root is arbitrary and can coincide with that degree-two vertex. More generally, if a connected graph has positive-score vertices in different components of its triangle-edge subgraph, it satisfies the bound. This second conclusion allows score one. The connected single-leaf class with a score-one ear remains open in this work. [EarComponent.lean](EarComponent.lean) · [EarCoreReduction.lean](EarCoreReduction.lean)

## Proof of the missing-one theorem

Write J for the spanning subgraph consisting of edges in triangles. An earlier maximum-cut argument shows that a failure with no score one has exactly two cubic vertices in J. They are nonadjacent, have scores two and three, and have exactly two crossing neighbors each in every maximum cut. The high vertices, those of degree at least three in J, have distinct scores and are split evenly between the two shores. The embedded predecessor proves that the common half-size m is at most six.

If a maximum cut separated the cubics, every high vertex outside their four crossing neighbors would miss the opposite cubic. Each opposite shore has at most two vertices that can branch within that shore. The existing two-center edge bound and the predecessor's link bound then constrain at least 2m−4 distinct scores to the interval from two through ⌊(3m−3)/2⌋, forcing m≤3. But a six-high graph cannot have the required cubics. The score-two cubic has two nonadjacent neighbors. If either missed the score-three cubic it would have at most three neighbors, making a third cubic. If both see the score-three cubic, they must be adjacent because its three neighbors form a clique. The prior small-high lower bound deals with fewer than six high vertices. Thus both cubics lie in the same shore of every maximum cut. [SplitShore.lean](SplitShore.lean) · [CubicSide.lean](CubicSide.lean)

Call their high shore A and the other B. The edges within A form a matching. Each cubic has its own matched partner. Among the m−2 ordinary vertices of A, these two partners have no internal neighbor. A vertex of B missing both cubics has at most one neighbor in B. Its score is bounded by the size of its opposite neighborhood plus the number of edges induced there. [MatchingSide.lean](MatchingSide.lean)

* **Four per shore.** Every vertex of B must meet a cubic, since a vertex missing both would have score less than four. Each therefore sees exactly one cubic and both ordinary vertices of A. Retain the score-two cubic and the score-three cubic's two opposite neighbors. The other two vertices of B cannot be adjacent, since that would give the score-two cubic a third triangle. Their required degree supplies a neighbor among the two retained vertices of B. All five omitted vertices have two retained neighbors. [EightExchange.lean](EightExchange.lean)
* **Five per shore.** Some vertex of B misses both cubics. The three ordinary vertices of A have no edges between them, so this vertex has score at most three. It cannot be either fixed cubic.
* **Six per shore.** At least two vertices of B miss both cubics. Their distinct scores are at least four, so one has score at least five. There is at most one edge among the four ordinary vertices of A. The score-five vertex must see all four, and the edge must be present. Now every ordinary vertex of A has a matched partner. There are at least five nonadjacent ordinary pairs eligible for simultaneous removal from A. An opposite vertex can obstruct the removal of a pair only if it has exactly three neighbors in A and sees both removed vertices. Each such vertex that sees zero, one, or two cubics obstructs at most three, one, or zero pairs, respectively. The shared neighbor of all four ordinary vertices supplies no obstruction. The four cubic incidences among the other five opposite vertices imply at most nine obstruction incidences. Thus some candidate pair has at most one obstruction. Retain that obstruction if present, or otherwise retain the shared neighbor. Replacing the pair by this one vertex gives five retained high vertices and seven safe omissions. [ShoreDonors.lean](ShoreDonors.lean)

The new modules use cardinalities and adjacency arguments directly. No external search, finite graph catalogue, or numerical solver is required. The cutoff package supplies the rooted one-leaf construction, disjoint local palettes under equality, and the deterministic reduction to thirteen. The new component corollary applies the complete missing-one theorem to the single-leaf instance on each positive component in turn. Each would need a vertex of score one, while distinct components cannot share a positive score in a failure.

## Replay

The source archive embeds the exact 80-module predecessor (SHA-256 `abe06d005062cddf33e5efe42dc7d678672adddf6fa9ec1d9e1e517ad140b28e`). It also includes the eight new Lean sources, expected object hashes, and a replay entry point. The full chain contains 88 project modules, with 13 axiom reports for the eight additions. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

Set `CROSSFOUR_LEAN_BIN` to the binary directory for Lean 4.19.0 (commit `6caaee842e94`) and `CROSSFOUR_MATHLIB` to built Mathlib v4.19.0 (commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`). Inside the extracted source archive run

~~~sh
python3 -B replay_missing_one.py
~~~

For a segmented replay, pass `--component-log /absolute/path/to/CompleteCold.log`. This authenticates all 80 predecessor objects before compiling the eight additions. Each new source is compiled synchronously with warnings treated as errors. The checker compares source and object hashes and audits each printed axiom set. [Replay script](replay_missing_one.py) · [Source hashes](SOURCES.sha256) · [Object hashes](OBJECTS.sha256)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
