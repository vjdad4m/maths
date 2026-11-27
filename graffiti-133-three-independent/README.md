# Graffiti.pc #133: three-fan obstruction at four independent ports

This is a partial result, not a proof of #133. In the four-port setup of the earlier [four-palette result](../graffiti-133-four-palette/), if the attachment ports are independent, a single label cannot support three pure clean fans in a four-cycle-free graph with no induced nine-vertex path. The theorem is `Graffiti133P5CliqueArms.independent_palette_at_most_two_fans`. There is no separate shared-relay or stem hypothesis.

The proof encodes the possible cross-edges between the three fans, checks the resulting finite possibilities in Lean, and lifts the result to the actual graph. Kinds of fan and the exact hypotheses are defined by `PortFanFamily` in the earlier package and in the theorem statement.

Replay with the compiled dependencies of the four-palette result on the Lean search path (Lean 4.19.0), then compile the three sources in order: Finite, Witness, Lift. The original strict replay log is included; the final theorem uses only the standard axioms.
