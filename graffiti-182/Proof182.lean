import Proof183
import Bridge182

namespace Graffiti182
open SimpleGraph

/-- The exact Written on the Wall II conjecture 182. -/
theorem conjecture182 {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) : Claim182 G :=
  claim_of_183 G hc (Graffiti183.Exceptional.conjecture183 G hc)

#print axioms conjecture182
end Graffiti182
