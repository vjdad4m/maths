# Erdős #324: even quartics, coefficients through 256 and their square multiples

The [earlier Lean package](../erdos-324-even-quartic-collisions/) rules out
coefficients 1–32. This extension certifies collisions for every
`x^4 + c*x^2` with `1 ≤ c ≤ 256`, and by dilation for every
`x^4 + (c*k^2)*x^2` with those base coefficients and all positive integers `k`.
The original existence problem is open.

`quartic-witnesses-256.txt` records the five columns `c a b u v` of the
certificates. The search limit 1200 yielded 255 witnesses; the remaining
base coefficient 57 has a collision at pairs `(37,1635)`, `(1097,1545)`.
The proof checks concrete identities, without assuming search completeness.

To replay with Lean 4.19.0, no Mathlib, first compile the earlier
`QuarticCollisions.lean` to `QuarticCollisions.olean` and put its directory
on `LEAN_PATH`. Then run
`lean -j1 -DElab.async=false -DwarningAsError=true QuarticCollisions256.lean`.
The theorem uses only standard axioms `propext` and `Quot.sound`.
