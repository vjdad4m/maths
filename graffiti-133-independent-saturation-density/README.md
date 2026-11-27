# Graffiti.pc #133: saturation at four independent attachment ports

Let G be a finite simple graph with no ordinary four-cycle and no induced nine-vertex path. Suppose a connected dominating induced core G[D] has no induced seven-vertex path, and four distinct, pairwise nonadjacent vertices of D contain every endpoint in D of an edge from outside D.

For each exterior vertex q, let d(q) count its neighbors in D. Define E as the sum of d(q) − 1 over all exterior vertices. The Lean theorem `Graffiti133P5CliqueArms.independent_four_ports_mean_four_of_size_or_large_contact` bounds total local independence by 4|V(G)| if at least one of the following holds:

- E ≤ 3;
- |D| ≥ 16, with arbitrary exterior attachment multiplicity;
- some exterior vertex has at least three neighbors in D, at any core order.

In this setup, only core order at most 15, excess E in {4, 5, 6}, and exterior attachment counts at most two remain outside the theorem. This package does not settle the full conjecture.

## Strict replay

Use Lean **4.19.0** and the same pinned Mathlib as the prerequisite packages. Put their compiled modules and transitive dependencies on `LEAN_PATH`:

- [Independent attachment excess at most three](../graffiti-133-independent-excess-three/): `P5CliqueIndependentExcessThree133`, `P5CliqueIndependentPureAnchor133`, and the nearest-stem bridge modules.
- [Low attachment excess](../graffiti-133-independent-low-excess/) and [three-independent-port fans](../graffiti-133-three-independent/): transitive dependencies.
- [Two clean length-three stems](../graffiti-133-double-stem-six/): `P5CliqueDoubleStemSix133`.
- [Induced-seven package](../graffiti-133-induced-seven/): `HexFlattened133` and, through its dependencies, `Partial133`.

Replay in the order in [`modules.txt`](modules.txt):

```sh
mkdir -p obj
export LEAN_PATH="$PWD/obj${LEAN_PATH:+:$LEAN_PATH}"
while IFS= read -r m; do
  lean --root=src -j1 -s32768 -DElab.async=false -DwarningAsError=true \
    -o "obj/$m.olean" "src/$m.lean" || exit
done < modules.txt
```

[`sources.sha256`](sources.sha256) pins all six Lean files. [`strict.log`](strict.log) records the module checks and axiom audits.
