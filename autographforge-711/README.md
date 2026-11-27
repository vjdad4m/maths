# AutoGraphForge row 711. A sharp decrease in the forcing number

Every nontrivial Eulerian finite simple graph satisfies **F₂(G) ≤ Z(G) − 1**. The triangle attains equality with F₂ = 1 and Z = 2. Ján Pastorek’s normalized physical line 711 is CEGIS proposal `2419b925` at revision `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. The Lean theorem `ForcingDrop711.row711` states the signed integer inequality on precisely the source class. [Pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L711)

## Proof and sharpness

Let S be a successful k-forcing set in a finite nonempty graph. A first forcing vertex v has at most k white neighbors. If every vertex is already colored, any v will do. Otherwise such a vertex exists because the set must grow. When every degree is at least k+t, at least t neighbors of v are already colored. Delete t of these neighbors from S. Under the relaxed threshold k+t, the retained vertex v can recolor all the deleted vertices in one round. Every subsequent round can reproduce or overtake the original run. Taking a minimum seed gives

```text
F_(k+t)(G) + t ≤ F_k(G)     whenever k+t ≤ δ(G).
```

A connected graph on at least two vertices has positive degrees. If all the degrees are even, their minimum is at least two. Taking k=t=1 proves row 711. For every n≥1, Lean proves the known exact formula F_k(K_n) = max(1,n−k), and hence equality in the general bound for all k+t<n. Odd complete graphs of order at least three give equality in the Eulerian row. The triangle’s Eulerian hypotheses and both optimum values are also checked explicitly.

The local theorem `packed_seed_savings` allows *simultaneous* deletions. Suppose a successful k-seed contains r centers with pairwise disjoint closed neighborhoods. If each center has degree at least k+t and at most k white neighbors initially, removing t colored neighbors from each center yields a successful (k+t)-seed of size |S|−rt. The hypothesis concerns only the centers. The argument keeps every center and restores all rt vertices in one parallel round. The single-center and graph-wide statements follow from this theorem.

## Attribution and shared Lean sources

Amos, Caro, Davila and Pepper introduced this k-forcing parameter. Proposition 2.1 gives the first-move degree count, Observation 2.2 gives the complete-graph formula, and Proposition 2.3(3) gives weak monotonicity in k. Their Lemma 3.1 already uses deletion and first-round recovery at a single center. In particular, strict one-step descent below minimum degree also follows from Lemma 3.1 and monotonicity. If a minimum k-seed had the same size as a minimum (k+1)-seed, it would be minimum at both thresholds. With δ≥k+1, the lemma would require each seed vertex to have at least k+1 white neighbors, whereas a successful k-seed has an eligible first vertex. Iteration gives the displayed numerical inequality. The row is therefore a consequence of prior work. The Lean proof constructs the smaller seed and gives the disjoint-center version. Historical priority for that version is unverified. [Amos et al., *Upper bounds on the k-forcing number of a graph*, Section 2 and Lemma 3.1](https://arxiv.org/pdf/1401.6206)

The source copies the parallel step and order-bounded iteration from the public balanced-biclique forcing proof. Its unconditioned minimum is written directly, simplifying that file’s constant-true predicate. The published exact biclique formulas have a family-specific graph argument. The degree-positivity argument for a nontrivial connected Eulerian graph is adapted from row 574. The public index was checked at `ecd84e3c5174c63840147385270d864875fb4403`; it contains 574 and the distinct 1539 biclique disproof and has no entries for 711 or 6318. [BalancedForcing definitions](https://github.com/vjdad4m/maths/blob/91daf08ea8ac128fc3fac209081a72da60a6a51c/autographforge-balanced-forcing/BalancedForcing.lean#L230-L263) · [Row 574 degree argument](https://github.com/vjdad4m/maths/blob/91daf08ea8ac128fc3fac209081a72da60a6a51c/autographforge-574/Row574.lean#L129-L143) · [Inspected index](https://github.com/vjdad4m/maths/blob/ecd84e3c5174c63840147385270d864875fb4403/README.md)

## Exact source conventions and neighboring rows

GraphCalc 2.0.0 uses order ≥2 for `nontrivial`. Its `eulerian` calls NetworkX 3.5 `is_eulerian`, which requires a connected graph with every degree even in this undirected domain. Zero-forcing and two-forcing use k=1 and k=2 in the same parallel operation. A colored vertex with one to k white neighbors colors all of them. The search runs to a fixed point. Lean’s `stable` proves that the published iteration through the order of the graph has reached that point. The search for a zero-forcing set starts at minimum degree, justified by `search_start`. For k>1 the search starts at one, valid because a nonempty graph cannot grow from an empty seed. [GraphCalc classes](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Forcing operation and optimizers](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/zero_forcing.py#L107-L486) · [Public battery](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py#L125-L160)

Physical line 6318, record `379aa857`, prints “(two_forcing_number = zero_forcing_number) ⇒ ¬eulerian” without an order qualifier. The singleton is Eulerian and has F₂=Z=1. Lean’s `singleton_boundary` and the public battery both verify this boundary witness. On graphs of order at least two, 711 rules out equality in the Eulerian class. Line 740 uses total forcing on connected cographs. Line 1012 gives a factor-two equality on subcubic Eulerian graphs. The previously published line 1539 uses a different affine bound on all connected graphs. [Line 6318](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L6318)

Both 711 and 6318 have status `proposed`, empty Lean fields, and empty tightness-witness strings at the pin. For 711 the normalized touch count is 115 and CEGIS metadata reports 1000. The released verified proofs and three refutation JSON files had no matching ID or statement. The single issue visible in the upstream issue list concerns another ID. Of 4,776 distinct released graph6 encodings, 899 were nontrivial and Eulerian. All 899 passed the degree-condition check. GraphCalc also recomputed both optima for the 156 eligible encodings of order at most eight. The collection contained no single-vertex encoding. The upstream public battery returned the expected class flags and forcing values on K₁, K₂, K₃ and K₅. [Pinned results](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

## Replay

Use Lean 4.19.0 with a built Mathlib v4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the extracted directory, with that Lean on PATH, run

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

In the shared scratch workspace the exact command from this folder is

```bash
PATH="$PWD/../outer-forest/.deps/lean-4.19.0-linux/bin:$PATH" \
MATHLIB_DIR="$PWD/../../graff169-180-codex/.work/mathlib" bash replay.sh
```

The replay creates a fresh object directory, treats Lean warnings as errors, and checks all nine printed axiom lists against `propext`, `Classical.choice`, and `Quot.sound`. `Row711.lean` imports only Mathlib and Lean. `Replay.log` is the expected output. The optional source audit runs independently of Lean with GraphCalc 2.0.0, NetworkX 3.5, and the pinned upstream checkout.

```bash
python audit.py /absolute/path/to/AutoGraphForge
```
