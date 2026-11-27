import ClawMatching

namespace Chain5169
open Finset SimpleGraph Graffiti326 BullCover1125 TriangleMatching1078

variable {W : Type*} [Fintype W] {G : SimpleGraph W}

/-- Keep the matching edges and add an incident edge for each unmatched
vertex. This is the upper-bound direction of Gallai's edge-cover identity. -/
theorem cover_from_matching (iso : IsolateFree G) :
    edgeCoverNumber G + matchingNumber G ≤ Fintype.card W := by
  classical
  let k := matchingNumber G
  obtain ⟨f,ok⟩ := matchingNumber_attained G
  let matched (i : Fin k) : G.edgeSet := ⟨s(f (i,false),f (i,true)),ok i⟩
  choose neighbor joins using iso
  let extra (v : W) : G.edgeSet := ⟨s(v,neighbor v),joins v⟩
  let U := univ \ Graffiti326.support f
  let C := univ.image matched ∪ U.image extra
  have good : Covers G C := by
    intro v
    by_cases mem : v ∈ Graffiti326.support f
    · obtain ⟨i,b,rfl⟩ := (Graffiti326.mem_support f).mp mem
      exact ⟨matched i,mem_union_left _ (mem_image_of_mem _ (mem_univ _)),by cases b <;> simp [matched]⟩
    · exact ⟨extra v,mem_union_right _ (mem_image_of_mem _ (mem_sdiff.mpr ⟨mem_univ _,mem⟩)),
        Sym2.mem_iff.mpr (Or.inl rfl)⟩
  have covered : edgeCoverNumber G ≤ C.card := Nat.sInf_le ⟨C,rfl,good⟩
  have cost : C.card ≤ k+U.card := (card_union_le _ _).trans
    (Nat.add_le_add (card_image_le.trans_eq (by simp)) card_image_le)
  have sum := card_sdiff_add_card_eq_card (subset_univ (Graffiti326.support f))
  have count : (Graffiti326.support f).card = 2*k := by simp [Graffiti326.support,k,Nat.mul_comm]
  change U.card + (Graffiti326.support f).card = (univ : Finset W).card at sum
  rw [count,card_univ] at sum
  change edgeCoverNumber G+k ≤ _
  omega

theorem connected_cover (conn : G.Connected) (cl : Free G claw) (iso : IsolateFree G) :
    edgeCoverNumber G = (Fintype.card W+1)/2 := by
  have small := cover_from_matching iso
  have paired := near_perfect conn cl
  have large := vertices_le_twice_cover iso
  omega

theorem connected_minimal_order (conn : G.Connected) (cl : Free G claw)
    {r : ℕ} (num : edgeCoverValue G = some r)
    (viol : (lineDomination G : ℚ) < (3/5 : ℚ)*r + -1) : 13 ≤ Fintype.card W := by
  classical
  have iso : IsolateFree G := by
    by_contra h
    simp [edgeCoverValue,h] at num
  have eq : edgeCoverNumber G = r := by simpa [edgeCoverValue,iso] using num
  have cover := connected_cover conn cl iso
  exact minimal_order G cl num (by omega) (by linarith)

/-- The lower bound on connected counterexamples is attained. -/
theorem smallest_connected :
    Fintype.card (V 3) = 13 ∧ (chain 3).Connected ∧ Free (chain 3) claw ∧
    edgeCoverValue (chain 3) = some 7 ∧ lineDomination (chain 3) = 3 ∧
    (lineDomination (chain 3) : ℚ) < (3/5 : ℚ)*7 + -1 := by
  obtain ⟨conn,cl,num,dom,_,viol⟩ := family 3 (by decide)
  exact ⟨by decide,conn,cl,num,dom,by norm_num at viol ⊢; exact viol⟩

#print axioms subcubic
#print axioms near_perfect
#print axioms cover_from_matching
#print axioms connected_cover
#print axioms connected_minimal_order
#print axioms smallest_connected
end Chain5169
