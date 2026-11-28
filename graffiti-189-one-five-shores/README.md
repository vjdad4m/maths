# Graffiti.pc #189, degree-five distance-two (1,5): complete profile

Exact theorem: Graffiti189LongestPath.CrossSaturation.FiveActualCut.traceable_of_actual_five_one_five_ports. It provides a spanning path in the original finite connected simple graph whose cut endpoints a,b are at distance two and whose deletion components C,D cover every off-cut vertex. Graph stays connected after each single deletion. Each even-distance set, counting the center, has at most six vertices, and among every pair of distinct vertices at least one has degree≥5. Exactly one vertex in C touches the cut, and exactly five in D do. There is no common-porter assumption or explicit order restriction. This is a partial result for general #189, not a claimed solution of that conjecture.

Compile the following files in order after the earlier #189 actual-cut/Ore infrastructure and the [1+4](../graffiti-189-one-four-shores) and [2+4](../graffiti-189-two-four-shores) releases:

- [DegreeFiveOneFiveGeometry189.lean](DegreeFiveOneFiveGeometry189.lean) `3424c780b1b3f4ce5fb1639ce65d0ca568036079c3c3c9ff5aff1ae09a85a4b7`
- [Graffiti189TraceableOre189.lean](Graffiti189TraceableOre189.lean) `4cfb3959062eacafb5a6a9c2b8fdfadd2798acb83789c5ef122f412ef7acd413`
- [CapSplitRoute189.lean](CapSplitRoute189.lean) `484f4fb9a0532c7483472816c29c11bb8e9a9ddb740d3c1a511e9b6d131222a4`
- [FiveCapUniversal189.lean](FiveCapUniversal189.lean) `36c42954a4ba202b64603f35bfc56a0fdbc926f9185ec06b773870fcd1ed6353`
- [CapOreFill189.lean](CapOreFill189.lean) `0a5c3308742b1c6b66437fac833f7b3b971b9768a7c47728aa9598bfebf13b8a`
- [SmallFiveCap189.lean](SmallFiveCap189.lean) `e7581dc725cf788dcdf9a5fac5ff8cbbfdabff421069e89edaecd439c9a0bfe3`
- [DegreeFiveOneFiveCapGlue189.lean](DegreeFiveOneFiveCapGlue189.lean) `50b2473b4ad5844f35e268317c2747530211e321c2df7d8ff1bca1eadb2b0432`
- [DegreeFiveOneFiveNear189.lean](DegreeFiveOneFiveNear189.lean) `1f053e8e4fb441815bcf2f3bbe652b2f22c4bcdacdf1c24773d2277860fcfc97`
- [DegreeFiveOneFiveFarProfile189.lean](DegreeFiveOneFiveFarProfile189.lean) `a0b00cee8c10764381aff096bab7da21db5da4c34cca94f315a52eaa9b605650`
- [DegreeFiveOneFiveFarCounts189.lean](DegreeFiveOneFiveFarCounts189.lean) `cd6dfc7c4dda710e01a5a2ddf9ccaa2edbf3ceabb824881cdbdc47f89b4501d9`
- [DegreeFiveOneFiveFarRoutesBase189.lean](DegreeFiveOneFiveFarRoutesBase189.lean) `2e4ea490477e93e424cc5117278e5247d1be44ff8eb25e1d5b01e6afb5df25bd`
- [SixSpecialRoute189.lean](SixSpecialRoute189.lean) `9b08738f86dd79685cb22c374b83432e87fae0aaaee66681794605cf401f907b`
- [LowProtectedRoot189.lean](LowProtectedRoot189.lean) `3882ed174e3d210e28528a06f0e1fd6c72cee50440cd2da00aaf4995229c3d98`
- [SmallDenseRoute189.lean](SmallDenseRoute189.lean) `4ca806d272a2ec9acfc07b9e2ac43376119939f8b601ab0f33b7141edd8921dd`
- [DegreeFiveOneFiveFarGlue189.lean](DegreeFiveOneFiveFarGlue189.lean) `92e57aab64676139d113f76c5b4056d44663e363cc502381025729331a8e28cc`
- [DegreeFiveOneFiveFarUnmixed189.lean](DegreeFiveOneFiveFarUnmixed189.lean) `d1e3e231b6706fbd5b506dece7334fdf07f8b7031460a110ff800a85829a052a`
- [DegreeFiveOneFiveFarMixed189.lean](DegreeFiveOneFiveFarMixed189.lean) `869acd8a4a7ec3ba6e34ff15ee29f479ba1b299f117965d66e611b0daa67609c`
- [DegreeFiveOneFiveFarSeven189.lean](DegreeFiveOneFiveFarSeven189.lean) `75f96b3b79525a6425e80b94a8a24ac0dfbb0a17caf4a3017ddd2b886e76808a`

Verified all together by Lean/mathlib 4.19.0 with a successful replay, with -j1 -s 65536 -DElab.async=false -DwarningAsError=true. All printed exactly [propext, Classical.choice, Quot.sound], in particular the near result, both ambient order-11 shore routes, the ambient order-12 shore route, and the final theorem. The combined source audit used the exact proof bodies and proper full declaration names; standalone frozen files retain imports and explicit open-private directives for modular replay. No sorry, native_decide, custom axioms, or graph enumeration.

Proof: the one-port shore is a singleton touching both cut vertices. Parity saturation at it dominates the other shore's interior via the five ports. For opposite order ≤10, a cap vertex realizes the two disjoint rooted pieces needed even when that shore itself is nontraceable; unrooted Ore and then the cap split transfer preserve actual-graph paths. For larger shore order, simultaneous saturation of the endpoint shells leaves exactly single-/double-charged nonport profiles (3,3,0), (2,2,2), and (3,3,1). The six-nonport cases use a shared-triple route plus an exclusive-to-exclusive route; the few missing edges are controlled analytically. The seven-nonport case uses protected-pair rooted Ore after the common clique. Order ≥13 is excluded by the parity/degree geometry. Original distances are never evaluated on the auxiliary completed graphs.
