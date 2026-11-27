# AutoGraphForge row 595

**Disproved by a 22-vertex connected 4-regular graph.** Its harmonic index is 11, its maximum matching has 10 edges, and row 595 would require 21/2 ≤ 10. The construction is a specialization of Henning and Yeo's 2007 Proposition 4. The contribution here is a source-audited, kernel-checked application to Ján Pastorek's AutoGraphForge row, including the exact unbounded family. [Pinned normalized statement, line 595](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L595) · [Henning and Yeo](https://doi.org/10.1007/s00373-007-0757-5)

## Statement and graph

The source proposes H(G) − 1/2 ≤ ν(G) for every nontrivial Eulerian regular graph. The domain consists of simple undirected graphs of order at least two. Eulerian requires connectedness and even degree at every vertex. The matching number ν maximizes the number of pairwise disjoint edges. The harmonic index H sums 2/(deg u + deg v) once per unordered edge uv. On a positive d-regular graph each edge contributes 1/d and the degree sum gives H = |V|/2. Thus the row holds precisely when some matching covers all but at most one vertex. Lean proves the equivalent integer criterion |V| ≤ 2ν + 1. [AutoGraphForge wrapper](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py) · [GraphCalc classes](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Harmonic index](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/graph_indices.py#L932-L980) · [Maximum matching optimizer](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L690-L765)

Arrange s ≥ 1 hubs in cyclic order. Between each hub i and its successor put two separate five-vertex blocks, each a K₅ with edge 01 deleted. Join port 0 to i and port 1 to its successor. All vertices have degree four. Each block connects its two hubs, so the resulting simple graph is connected. With s = 2 there are two hubs and four blocks between them.

In a matching, at most s edges meet hubs. Every remaining edge lies inside a block, and a five-vertex block can hold at most two such edges. This gives ν ≤ s + 2(2s) = 5s. To attain equality at each i, use the edge from i to port 0 of its first outgoing block and the internal edges 12 and 34. In its second outgoing block use internal edges 02 and 13. Together these are 5s disjoint edges. The graph has 11s vertices, H = 11s/2 and ν = 5s. Its excess over the proposed inequality is (s−1)/2. The construction attains equality at s = 1 and violates the row for every s ≥ 2. The Lean parameter n is s−1.

## Provenance and smallest order

Henning and Yeo's Proposition 4 replaces each edge of a connected even-regular multigraph with a complete graph minus one edge. For s ≥ 2 the base here is the doubled cyclic sequence of s hubs. Their theorem gives precisely the order and matching ratio certified here. The two-hub base has four parallel edges. O and West later characterized extremal graphs under edge-connectivity hypotheses. The regular harmonic-index identity is standard. Bıyıkoğlu's 2026 TxGraffiti result concerns the **minimum maximal matching** and a different inequality. [Henning and Yeo, Theorem 2 and Proposition 4](https://doi.org/10.1007/s00373-007-0757-5) · [O and West](https://doi.org/10.1016/j.ejc.2010.10.005) · [Zhong on the harmonic index](https://doi.org/10.1016/j.aml.2011.09.059) · [Bıyıkoğlu on TxGraffiti](https://doi.org/10.46793/match.96-3.28425)

**The minimum counterexample order is 22, and the minimum odd counterexample order is 33.** This conclusion uses Henning and Yeo's published Theorem 2, whose graph-theoretic proof is external to this Lean package. It gives, for connected d-regular graphs of order N and even d ≥ 2,

```text
ν ≥ min( (d²+4)/(d²+d+2) · N/2, (N−1)/2 ).
```

For an even degree, (d−4)(d−6) ≥ 0, so the coefficient (d²+4)/(d²+d+2) is at least 10/11. Failure of row 595 then forces 11ν ≥ 5N and N−2ν ≥ 2. For odd N this deficit is odd and at least three. The two conclusions are N ≥ 22 and N ≥ 33, respectively. The family meets both thresholds. Lean checks this arithmetic in `henning_yeo_threshold`, where the displayed published bound is an explicit hypothesis. The family and the disproof use only their self-contained matching argument.

## Release audit

Normalized row 595 has ID `bc7d9697`, 154 normalized touches and the annotation `promising:class`. The pinned CEGIS record lists it as proposed with a null Lean proof. Its ID and statement are absent from the three refutation JSON files and the released verified Lean proofs. The shared README at `a99a6d7` had no row 595 entry. Upstream's sole public issue at inspection concerned a different ID. The release audit was performed on 27 November 2026. The 2007 result already determines the mathematical answer. [Pinned CEGIS records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Inspected shared index](https://github.com/vjdad4m/maths/blob/a99a6d721b2409656825660640b80c27c112f917/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

The four graph6 backups share one Git blob. Their 4,700 distinct encodings and the 312 from the three refutation files give 4,776 distinct encodings in total. Of these, 383 meet the row hypotheses, including 62 occurring in the refutation files. None violates the row. The audit evaluates the harmonic index as an exact fraction, cross-checks GraphCalc's floating result and runs its maximum-matching optimizer. It also runs the source predicates and invariants on the family members with s = 1, 2, 3 and 5. `SourceAudit.log` includes a graph6 encoding of the 22-vertex witness. [Archived graph6 data](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/backup_20260730T150317)

## Reuse and strict replay

`Matching.lean` excerpts the finite maximum-matching definition, attainment and bound from the repository's matching basis. `Row595.lean` uses the symmetric edge-weight definition from row 2598. `Blocks.lean` proves the order, connectedness and regularity for every family member. `Packing.lean` proves the matching bound by counting fibers and constructs an attaining matching. [Published matching basis](https://github.com/vjdad4m/maths/blob/a99a6d721b2409656825660640b80c27c112f917/autographforge-574/MatchingBasis.lean) · [Published row 2598](https://github.com/vjdad4m/maths/blob/a99a6d721b2409656825660640b80c27c112f917/autographforge-2598/DoubleBroom.lean)

With Lean 4.19.0 on PATH and a prepared Mathlib v4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run from the extracted source directory

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The replay rebuilds four modules into a fresh temporary directory, treats warnings as errors and checks the printed axioms for six theorems. The only axioms are `propext`, `Classical.choice` and `Quot.sound`. To repeat the separate numerical and source audit, install GraphCalc 2.0.0, NetworkX 3.5 and a supported MILP solver such as CBC, then run

```bash
python audit.py /absolute/path/to/pinned/AutoGraphForge
```

The Git checkout must contain the pinned graph6 backup blob. Expected outputs appear in `Replay.log` and `SourceAudit.log`.
