# Pinned prerequisite sources

- Lean v4.19.0, commit `6caaee842e94`.
- Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, including
  `Mathlib.Tactic.Sat.FromLRAT`.
- Public prerequisite repository `vjdad4m/maths`, revision
  `18b145e65ca0d5efaf8693a87c4f438f1d56b8a9`.
- `SixLayer25Cover189` is `graph/SixLayer25Cover189.lean` inside
  `graffiti-189-degree-six-four-connected-complete/proof-sources.zip`
  (SHA-256 `e75be45a0ab8ff2de3a78663c4f0acd02382e991ea809609f308b057c90ca44e`).
- `GraphSat189` and `GraphRup189` are at the root of
  `graffiti-189-degree-three/proof-sources.zip`
  (SHA-256 `ee4710be8ffaf69f0bb1156a9e2a701df926486d323f78033bf682bedb01d242`).
- `SixOrder24BThreeExcluded189` and its closure are in the pinned
  public packages listed in README. `SixJointEqualityBase189` is in
  `graffiti-189-degree-six-order25-radius/src`.

`source-dependencies.sha256` records the actual chosen prerequisite source bytes
by module filename. It does not list this package's modules, which are in
`MANIFEST.sha256`. No precompiled objects are required in the distribution.
