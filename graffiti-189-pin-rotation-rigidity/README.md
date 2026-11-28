# Graffiti.pc #189: locked pin edges

**Strict Lean partial, no upper-order restriction.** In the normalized separated-double-pin case, neither endpoint has a chord to either of the omitted vertex's pins. In particular, every support-preserving endpoint rotation retains both path edges incident to each pin. When all pins are interior, saturation identifies the whole flank pool and excludes a new endpoint flank. When an endpoint is already a fringe of the other pin, rotation would create the prohibited gap-two pair.

In the singleton branch, let B be the omitted-star boundary and F the vertices at distance two outside B. Then k≤|B|≤k+1, |F|≥2, and |B|+|F|+|N₄(x)|≤k+3. If N₄(x) is nonempty, B is an exact k-cut and F consists of the two fixed flanks. If |B|=k+1, N₄(x) is empty and F again consists of the two flanks. The first-endpoint pin chord is ruled out in both tight cases. The remaining one-slack leaves at most one spare flank vertex beyond the two required. These are structural reductions, not a proof of #189.

Lean and Mathlib 4.19.0. Build the earlier HighDichotomy189, Normalize189 and MultiPinRotation189 prerequisites and put their object directories on LEAN_PATH. Run replay.sh for fresh warnings-as-errors compilation.
