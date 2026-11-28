# Graffiti.pc #189 degree-five distance-two two-component cut with exactly three ports per shore

Full profile, not a proof of general #189. No common-porter hypothesis; neither shore size nor ambient order is bounded in the statement. Hypotheses: finite graph; connected and connected after deleting any one vertex; second-smallest degree at least five in pair form; every even-distance set including its root has size at most six; two distinct actual components cover all vertices off the cut; endpoints are at graph distance exactly two; each component has exactly three vertices adjacent to at least one of the cut endpoints.

Verified strict synthetic exact-body Lean 4.19.0 / Mathlib v4.19.0 replay passed, with `-j1 -s 65536 -DElab.async=false -DwarningAsError=true`. All printed only standard axioms:
```
'Graffiti189LongestPath.CrossSaturation.FiveActualCut.FiveMissShore33.no_local_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Graffiti189LongestPath.CrossSaturation.FiveActualCut.three_three_high_cut_covers_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'Graffiti189LongestPath.CrossSaturation.FiveActualCut.traceable_of_actual_five_three_three_ports' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Compile the following sources in order after the [2+3 exclusion](../graffiti-189-two-three-cut-exclusion), [1+5](../graffiti-189-one-five-shores), [3+4](../graffiti-189-three-four-shores) and earlier actual-cut prerequisites:

- [DegreeFiveThreeThreeVisTwo189.lean](DegreeFiveThreeThreeVisTwo189.lean) `b8a80dd1dbd4079ea43942f5198ab512651f0a8eb1415f156ed79346dfa7facf`
- [DegreeFiveThreeThreeUniversalShape189.lean](DegreeFiveThreeThreeUniversalShape189.lean) `96827c2010a0ce96c91aeebab2e0c756d89ee06d447facdd4be4b1d1ed590e78`
- [DegreeFiveThreeThreeDarkOrders189.lean](DegreeFiveThreeThreeDarkOrders189.lean) `20adce56fa7f04a1434d3dca6650a08505712a3aea0ff5f76ea96eec306e2d48`
- [DegreeFiveThreeThreeDegreeHelpers189.lean](DegreeFiveThreeThreeDegreeHelpers189.lean) `5ddc97d931e77c91d389db9ff910cb9d98a4c3b7f9f7a772a76b5678223bcd85`
- [DegreeFiveThreeThreeDarkRoute189.lean](DegreeFiveThreeThreeDarkRoute189.lean) `a40b318158e6ffda55f977658637899d4070bc81bab5b609bc25eed2985ca2ce`
- [DegreeFiveThreeThreeUniversalClose189.lean](DegreeFiveThreeThreeUniversalClose189.lean) `7fb70c237643540ea42491c79c9129760ae21451d8ec73558dd31848cb2b764d`
- [FiveOfSixPorts189.lean](FiveOfSixPorts189.lean) `f92366a300e4e1603faf4b1b095ddb578cc75be655ec9c005f5a8c77143c1f59`
- [DegreeFiveThreeThreeNeitherLTwo189.lean](DegreeFiveThreeThreeNeitherLTwo189.lean) `63d4aae459636d07c95e09ac71a95718dc0cd185f87400e88df5c1e3ac0c5729`
- [DegreeFiveThreeThreeNeitherLThree189.lean](DegreeFiveThreeThreeNeitherLThree189.lean) `fac870474d01dad4e10d1da7a5627676c98569401929ab4d471bc10c27247d53`
- [DegreeFiveThreeThreeNeitherGeometry189.lean](DegreeFiveThreeThreeNeitherGeometry189.lean) `0ae70d224046e0b158a6a1ad4a12401c08b66eee6a2b2d5fc2830545f26bbca9`
- [DegreeFiveThreeThreeNeitherClose189.lean](DegreeFiveThreeThreeNeitherClose189.lean) `4c00d600b8596c9c1f3cd1f656b29baf9e5098baf437ebeea9a440d56fee6c7a`
- [DegreeFiveThreeThreeFullClose189.lean](DegreeFiveThreeThreeFullClose189.lean) `9a5b5f49e2d30d129bd7bc01540a49799db47dd5717346c176d4a0cbcb414ef6`

The final file additionally imports `DegreeFiveActualCutSwap189` (prior exclusive-shore analyses). All dependencies already appear in the earlier publication set except the six universal files, FiveOfSixPorts and five new sources listed here. For full modular replay put `obj` and previous published module paths on LEAN_PATH and invoke Lean module by module with the flags above.

Proof: a high cut vertex missing one port has five other contacts. Its missed shore has only two or three vertices at distance two; the foreign shore contains at least one. At two local vertices, layer three becomes too small for the degree condition, even allowing one depth-four vertex. At three local vertices, the foreign shore's four-vertex shape makes every local vertex high; exact layer-three adjacency and two private distance-two slots per covered contact contradict each other. Thus a high cut vertex meets all six. The verified universal-cut case gives actual-graph Hamiltonian routing using a four-vertex small shore and dense common-terminal large shore. No finite graph enumeration or additional axioms.
