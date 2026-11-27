# Graffiti.pc #133: independent four-port attachment excess at most three

Let G be a finite simple graph with no ordinary four-cycle and no induced nine-vertex path. Let G[D] be a connected dominating induced core with no induced seven-vertex path. Assume four distinct, pairwise nonadjacent vertices of D contain every endpoint in D of an edge from outside D.

For each exterior vertex q, let d(q) be its number of neighbors in D, and let E be the sum of d(q) − 1 over all exterior vertices. The Lean theorem `Graffiti133P5CliqueArms.independent_four_ports_excess_at_most_three_ambient_mean_four` proves that the total local independence in G is at most 4|V(G)| whenever E ≤ 3. This holds at every core order, with no further radius, relay, stem, or attachment multiplicity restriction. In particular, it closes the previously uncovered E = 3 case where all multivalent exterior vertices have exactly two neighbors in D.

This is a partial result for #133. It does not settle the full conjecture or all configurations with E ≥ 4.

## Strict replay

Use Lean **4.19.0** and the same pinned Mathlib as the prerequisite packages. Put their compiled modules and transitive dependencies on `LEAN_PATH`:

- [Three-independent-port fan lemmas](../graffiti-133-three-independent/), which supply `P5CliqueIndependentFanWitness133` and `P5CliqueFourPortCommonRelayFans133`.
- [Four-port palette](../graffiti-133-four-palette/), which supplies `P5CliqueOnePortAmbientBudget133`; its prerequisites supply `Partial133`.
- [Four independent attachment labels and mean four](../graffiti-133-independent-mean-four/), which supplies `P5CliqueIndependentFanBudget133`.
- [Low attachment excess](../graffiti-133-independent-low-excess/), which supplies `P5CliqueIndependentLowExcess133`.

From this directory, check the new files in the order in [`modules.txt`](modules.txt):

```sh
mkdir -p obj
export LEAN_PATH="$PWD/obj${LEAN_PATH:+:$LEAN_PATH}"
while IFS= read -r m; do
  lean --root=src -j1 -s32768 -DElab.async=false -DwarningAsError=true \
    -o "obj/$m.olean" "src/$m.lean" || exit
done < modules.txt
```

The exact hashes of all eight modules are in [`sources.sha256`](sources.sha256). See [`strict.log`](strict.log) for the normal-import replays and axiom audits.
