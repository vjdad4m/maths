# Exact-cut single attachment closed, including the fourth shell

Put d = k+2. Under the #189 degree/parity hypotheses and connectedness
after deleting fewer than k vertices, a normalized high omitted root
cannot have exactly one path pin, boundary size k and eccentricity at
most four when d≥11. The proof allows arbitrary high root degree.
The shell budget has two alternatives: pay with unused distance-two
slots at the pin, or use finite Hall to find two distinct non-pin
gateways whose distance-two budgets already include both flanks.

Together with the separated-double result, this proves at d≥12 that
a counterexample in the k-connected regime must have a normalized
high omitted root with exactly one pin and boundary size k+1.
Its fourth shell is empty and its distance-two vertices outside this
boundary are exactly the two flanks of its path pin.
The oversized-cut case and lower connectivity remain unresolved here.

Replay using Lean/Mathlib 4.19 and prior #189 theorem objects, including
the one-low circumference stage, on LEAN_PATH.
