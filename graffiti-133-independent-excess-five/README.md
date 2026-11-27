# Graffiti.pc #133: independent four-port attachment excess exactly five

Let G be a finite simple graph with no ordinary four-cycle and no induced nine-vertex path. Let G[D] be a connected dominating induced core with no induced seven-vertex path. Assume that four distinct, pairwise nonadjacent vertices of D contain every endpoint in D of an edge from outside D.

For each exterior vertex q, let d(q) count its neighbors in D. Define E as the sum of d(q) − 1 over all exterior vertices. The Lean theorem `Graffiti133P5CliqueArms.independent_four_ports_excess_exactly_five_ambient_mean_four` proves that total local independence is at most 4|V(G)| when E = 5. This holds at all core orders, with no further attachment multiplicity restriction. The case with an exterior vertex having three or more attachments follows from the prior saturation bound. For the remaining case, four-cycle-freeness forces the five size-two attachment masks to represent five distinct port pairs. The mixed-pair capsules and the original-graph lift bound the number of these sites with local score four.

This is a partial result for #133. It closes E = 5 in this setting, not all attachment excesses and not the full conjecture.

## Strict replay

Use Lean **4.19.0** and the same pinned Mathlib as the prerequisite packages. Put their compiled modules and transitive dependencies on `LEAN_PATH`:

- [Four-port saturation density](../graffiti-133-independent-saturation-density/) supplies `P5CliqueIndependentSaturationDensity133` and `P5CliqueFourPortPacking133`.
- [Independent attachment excess at most three](../graffiti-133-independent-excess-three/) supplies `P5CliqueIndependentPureAnchor133`.
- [Low attachment excess](../graffiti-133-independent-low-excess/) supplies `P5CliqueMixedHighGeometry133`.
- [Four-port palette](../graffiti-133-four-palette/) supplies `P5CliqueOnePortAmbientBudget133`.

Replay in the order in [`modules.txt`](modules.txt):

```sh
mkdir -p obj
export LEAN_PATH="$PWD/obj${LEAN_PATH:+:$LEAN_PATH}"
while IFS= read -r m; do
  lean --root=src -j1 -s32768 -DElab.async=false -DwarningAsError=true \
    -o "obj/$m.olean" "src/$m.lean" || exit
done < modules.txt
```

[`sources.sha256`](sources.sha256) pins all twelve Lean files. [`strict.log`](strict.log) records the normal-import checks and axiom audits.
