# Graffiti.pc #189: two five-attachment shores with shared neighbors

For a distance-two pair of cut vertices in the degree-five case, this package proves a Hamiltonian path when their deletion leaves two connected shores, exactly five vertices of each shore meet the cut, and some vertex of each shore meets both cut vertices. Any positive shared count is allowed. The graph need not remain connected after deleting a single vertex. [Whole-graph theorem](src/DegreeFiveBothFiveAll189.lean)

The stronger interface supplies a spanning path from a neighbor of either specified cut vertex to an unrestricted shore endpoint on **each** shore, and a path between distinct contacts of the two cut vertices on at least one shore. Every path uses the original graph. [Endpoint options](src/DegreeFiveBothFiveStrongMasks189.lean) · [Composition](src/WingSignature189.lean)

The proof bounds the number of vertices on the two shores using the parity budget, routes through blocks separated by common neighbors, and handles one and two shared neighbors using the actual shore graph and endpoint-preserving path extensions. The full conjecture remains open, including different attachment counts in this case.

## Replay

Use Lean and Mathlib v4.19.0, with Mathlib pinned at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Build the [degree-five route infrastructure](../graffiti-189-degree-five-cuts/), [balanced common-neighbor modules](../graffiti-189-balanced-three-three/), and [degree-four closure infrastructure](../graffiti-189-complete-degree-four/) with their documented dependencies. Keep their built objects and the pinned Mathlib environment on the Lean search path. From this folder:

```sh
set -e
sha256sum -c sources.sha256
mkdir -p build
export LEAN_PATH="$PWD/build:${LEAN_PATH:-}"
while read -r module; do
  lean -j1 -DElab.async=false -DwarningAsError=true -o "build/$module.olean" "src/$module.lean"
done < modules.txt
```

The 16 published sources match the SHA-256 hashes of the strictly checked modules. The final Lean audit reported only `propext`, `Classical.choice`, and `Quot.sound` for the whole-graph and endpoint theorems.
