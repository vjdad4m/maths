# Graffiti.pc #133: four independent attachment labels and mean four

Let G be a finite simple graph with no ordinary four-cycle and no induced path on nine vertices. The ambient mean bounds below assume a connected dominating induced core G[D] with no induced path on seven vertices. All edges from outside D to the core land at four distinct, pairwise nonadjacent vertices of D; each exterior vertex may attach to more than one of them.

Write λ_G(x) for the independence number of the open neighborhood of x, and E for the exterior attachment excess: sum |N_G(q) ∩ D| − 1 over all exterior vertices q. The new Lean module proves:

- **Exterior high-count bound.** The number of exterior vertices with λ_G(q) > 3 is at most eight plus the number of such vertices with at least two core neighbors. In particular, it is at most 8 + E. These two counting theorems do not require core connectivity or the induced-P7 hypothesis.
- **Joint slack criterion.** If the total local independence in G[D], plus 8 + 2E, is at most 4|D|, then the total local independence in G is at most 4|V(G)|.
- **Two unconditional ranges within this scope.** The mean is at most four if E ≤ 1 at any core order, or if |D| ≥ 20 with arbitrary allowed attachment multiplicities.

This is a partial result for #133, not a resolution of the full conjecture.

## Strict replay

Use Lean **4.19.0** with the same pinned Mathlib as the prerequisite packages. Put their compiled objects on `LEAN_PATH` before building this package:

1. Base objects, including [`CambyDomBase133`](../graffiti-133-full-four/) and [`HexFlattened133`](../graffiti-133-induced-seven/).
2. [Four-point attachment package](../graffiti-133-four-palette/): in dependency order, `P5CliqueOnePortAmbientBudget133`, `P5CliqueMultiPortBudget133`, `P5CliqueFourPortCommonRelayFans133`, then `P5CliqueFourPortCommonRelayBudget133`.
3. [Sparse four-point package](../graffiti-133-sparse-palette/): `P5CliqueFourRelayArmFans133`, `P5CliqueFourNearThreeArmFans133`, then `P5CliqueHighPureFan133`; independently `P5CliqueSmallCoreLocal133` before `P5CliqueSmallCoreSignedSlack133`.
4. [Three independent-palette fans](../graffiti-133-three-independent/) (main commit `15023dd`): `P5CliqueIndependentFanFinite133`, `P5CliqueIndependentFanWitness133`, and `P5CliqueIndependentFanLift133`, in that order. The lift also imports the common-relay fans object listed above.

Compile this package's only new module, `P5CliqueIndependentFanBudget133`, as recorded in [`modules.txt`](modules.txt). For example, from this directory with the prerequisite search path already set:

```sh
mkdir -p obj
lean --root=src -j1 -DElab.async=false -DwarningAsError=true \
  -o obj/P5CliqueIndependentFanBudget133.olean src/P5CliqueIndependentFanBudget133.lean
```

The exact Lean source SHA-256 is `094875f3818d7e4a75e1f96a5a8fdec13f2325a7d2276e42efe1b8ff2c66b80a`; see [`sources.sha256`](sources.sha256). The normal-import verification and axiom audit are recorded in [`strict.log`](strict.log).
