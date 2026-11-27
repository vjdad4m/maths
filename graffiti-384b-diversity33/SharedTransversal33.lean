import CliqueCubicCover33

namespace Graffiti384b.ForcedCubics
open Finset SimpleGraph RootCut HighEar CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Two common neighbors of the score-two and score-three cubics
meet every five-clique in a tight core. -/
theorem shared_transversal {e a c u v p q : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c) (pos : ∀ w,0<trianglesAt H w)
    (inj : Function.Injective (trianglesAt H)) (du : H.degree u=3) (us : trianglesAt H u=2)
    (dv : H.degree v=3) (vs : trianglesAt H v=3) (pq : p≠q)
    (up : H.Adj u p) (uq : H.Adj u q) (vp : H.Adj v p) (vq : H.Adj v q)
    {R : Finset V} (tight : Tight H R) {C : Finset V} (cl : H.IsNClique 5 C) : p∈C ∨ q∈C := by
  classical
  apply Classical.byContradiction; intro outside
  have off : p∉C ∧ q∉C := not_or.mp outside
  let P : Finset V := {p,q}
  let A := H.neighborFinset u
  let B := H.neighborFinset v
  have pa : P⊆A := insert_subset ((H.mem_neighborFinset ..).mpr up) (singleton_subset_iff.mpr ((H.mem_neighborFinset ..).mpr uq))
  have pb : P⊆B := insert_subset ((H.mem_neighborFinset ..).mpr vp) (singleton_subset_iff.mpr ((H.mem_neighborFinset ..).mpr vq))
  have ca : (A\P).card=1 := by rw [card_sdiff pa]; simp [A,P,du,pq]
  have cb : (B\P).card=1 := by rw [card_sdiff pb]; simp [B,P,dv,pq]
  let M := C\(A∪B)
  have safe : ∀ x∈M,Safe H R x := by
    intro x xm w dw _ ed
    have wn := (H.mem_neighborFinset ..).mpr ed
    rcases cubic_scores H de dw pos inj with eq|eq
    · have same := inj (eq.trans us.symm)
      subst w
      exact (mem_sdiff.mp xm).2 (mem_union_left _ wn)
    · have same := inj (eq.trans vs.symm)
      subst w
      exact (mem_sdiff.mp xm).2 (mem_union_right _ wn)
  have low := safe_cap H de ea ec ac pos inj tight cl (show M⊆C from sdiff_subset) safe
  have sub : C∩(A∪B)⊆(A\P)∪(B\P) := by
    intro w wm
    obtain ⟨wc,wn⟩ := mem_inter.mp wm
    have wp : w∉P := by
      intro h; rcases (show w=p ∨ w=q by simpa [P] using h) with rfl|rfl
      · exact off.1 wc
      · exact off.2 wc
    exact (mem_union.mp wn).elim (fun t => mem_union_left _ (mem_sdiff.mpr ⟨t,wp⟩))
      (fun t => mem_union_right _ (mem_sdiff.mpr ⟨t,wp⟩))
  have cap := (card_le_card sub).trans (card_union_le (A\P) (B\P))
  have all : M.card+(C∩(A∪B)).card=5 := (card_sdiff_add_card_inter ..).trans cl.2
  omega

end Graffiti384b.ForcedCubics
#print axioms Graffiti384b.ForcedCubics.shared_transversal
