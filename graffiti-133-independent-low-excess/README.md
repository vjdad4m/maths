# Graffiti.pc #133: low exterior attachment excess

Let G be a finite simple graph with no ordinary four-cycle and no induced nine-vertex path. Suppose G has a connected dominating induced core G[D] with no induced seven-vertex path. Four distinct, pairwise nonadjacent vertices of D contain every endpoint in D of an edge from outside D.

For an exterior vertex q, write d(q) for its number of neighbors in D, and let E be the sum of d(q) − 1 over all exterior vertices. The theorem `Graffiti133P5CliqueArms.independent_four_ports_low_excess_ambient_mean_four` proves that the total local independence in G is at most 4|V(G)|, and hence the mean is at most four, if either:

- E ≤ 2; or
- E = 3 and some exterior vertex has at least three neighbors in D.

The result holds at every core order, without a radius, relay, or stem restriction. It is a partial result for #133: it does not settle the remaining independent-palette cases or the full conjecture. The included signed-charge and wedge modules provide the auxiliary estimates used by the final theorem.

## Strict replay

Use Lean **4.19.0** and the same pinned Mathlib as the prerequisite packages. Put their compiled objects and transitive dependencies on `LEAN_PATH` before checking these files:

- [Four independent attachment labels and mean four](../graffiti-133-independent-mean-four/), including `P5CliqueIndependentFanBudget133`. Its prerequisite chain supplies `P5CliqueOnePortAmbientBudget133` and `P5CliqueMultiPortBudget133` from the [four-palette package](../graffiti-133-four-palette/), and `P5CliqueSmallCoreLocal133` from the [sparse-palette package](../graffiti-133-sparse-palette/).
- `BicycleExactTriangleCharge133` from the [dominating-C7 radius-four package](../graffiti-133-dominating-c7-radius-four/).
- `HexFlattened133` from the [induced-seven package](../graffiti-133-induced-seven/).

From this directory, check the new modules in the order in [`modules.txt`](modules.txt):

```sh
mkdir -p obj
export LEAN_PATH="$PWD/obj:$LEAN_PATH"
while IFS= read -r m; do
  lean --root=src -j1 -DElab.async=false -DwarningAsError=true \
    -o "obj/$m.olean" "src/$m.lean" || exit
done < modules.txt
```

The exact hashes of all eight source modules are in [`sources.sha256`](sources.sha256). The main module's SHA-256 is `82594e4374dea993df0b2db9b63893edf7ffb94f6d741890615f8d2f8599c44d`. See [`strict.log`](strict.log) for the actual-import replay and axiom audits.
