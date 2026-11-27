# Kelmans F2: every exterior omission in the exact theta case

In the exact seven-vertex theta with five exterior wires, take a
finite simple cubic graph of order four modulo six under the stated
cyclic-five cut hypothesis. After deleting the theta root, every
genuine specified exterior edge omission reduces to a strictly
smaller instance:

- If either original opposite contact edge exists, use smaller
  cyclic-four F2 on a cap six vertices smaller. This includes
  omitting the sole opposite edge itself.
- Otherwise, use simultaneous two-edge avoidance on a cyclic-four
  graph of order zero modulo six, four vertices smaller. The two
  designated omissions are the required exterior edge and the
  now-unused midpoint wire.

These are conditional reduction premises, not theorems established
by this package. Internal or wire omissions and other host
configurations are outside the result. The exact theorem is
`ThetaExteriorReduction.every_exterior_omission`.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
From the repository root, run `bash kelmans-theta-all-exterior/replay.sh`.
