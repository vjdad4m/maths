import SixSingletonFiveShallowRoute189
import SixWeightedSideRoute189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private finish_by_balance d8 k3 from SixSingletonFiveShallowRoute189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Two balanced vertices of dark degree at least four do not obstruct
the passage through an eight-vertex dark block. The last dark vertex
is a balanced one, so it absorbs the only possible Ore deficit. -/
theorem traceable_five_dense_two_balances (W : Finset V) {l c t : V}
    (wD : W⊆D) (w2 : W.card=2) (lm : l∈D\W)
    (dense : ∀ z∈D,4≤(inside G D z).card)
    (core : ∀ z∈D\W,5≤(inside G D z).card)
    (border : RouteOn G K c t) (attach : ∃ z∈W,G.Adj z c)
    (sa : G.Adj s a) (ax : G.Adj a x) (xl : G.Adj x l)
    (tb : G.Adj t b) (by' : G.Adj b y) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨z,zw,zc⟩ := attach
  obtain ⟨p,q,neq,w⟩ := card_eq_two.mp w2
  have hit : ∀ {i j}, i∈W → j∈W → i≠j → i=z ∨ j=z := by
    intro i j iw jw ij
    rw [w] at iw jw zw
    simp only [mem_insert,mem_singleton] at iw jw zw
    rcases iw with e|e <;> rcases jw with f|f <;> rcases zw with g|g
    all_goals first | exact (ij (e.trans f.symm)).elim | exact .inl (e.trans g.symm) | exact .inr (f.trans g.symm)
  have path : RouteOn G D l z := by
    apply weighted_side_route D (mem_sdiff.mp lm).1 (wD zw) (fun h=>(mem_sdiff.mp lm).2 (h.symm ▸ zw))
    intro i iD j jD ij _
    have di := dense i iD
    have dj := dense j jD
    rw [d8]
    by_cases iW : i∈W
    · by_cases jW : j∈W
      · rw [if_pos (hit iW jW ij)]
        omega
      · have h := core j (mem_sdiff.mpr ⟨jD,jW⟩)
        omega
    · have h := core i (mem_sdiff.mpr ⟨iD,iW⟩)
      omega
  exact finish_by_balance path border sa ax xl zc tb by'

#print axioms traceable_five_dense_two_balances
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
