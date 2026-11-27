import SeamBudget180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem seam_loss {Q : Finset V} (w : ↥Q) (X : Finset ↥Q) (F : Finset V)
    (bad : ∀ v∈X, v=w ∧ w.val∈F) : X.card≤weight w.val F := by
  classical
  by_cases h : w.val∈F
  · have inc : X⊆{w} := fun v hv => mem_singleton.mpr (bad v hv).1
    simpa [weight,h] using card_le_card inc
  · have empty : X=∅ := eq_empty_iff_forall_not_mem.mpr (fun v hv => h (bad v hv).2)
    simp [empty,weight,h]

/-- At a tight split, if each smaller rooted instance meets its own
bound with the indicated marks, both meet it exactly. The seam gives
the full possible eligible-leaf increase on each side. -/
theorem tight_wings {J : SimpleGraph V} (jc : J.Connected) {x y w : V} {S T : Finset V}
    (s : Split J w S T) (xs : x∈S) (ys : y∉S) (xy : x≠y)
    (drop : bipartiteNum (J⊔edge x y)<bipartiteNum J) (r : ↥S) (A P : Finset V) :
    let L (B : Finset V) := pull (fun v : ↥S => v.val) B
    let R (B : Finset V) := pull (fun v : ↥T => v.val) B
    let U := eligible A P r.val
    let E := eligible (L A) (L P) r
    let F := eligible (R A) (R P) ⟨w,s.both.2⟩
    let k := weightedLeaves (side J S) E
    let m := weightedLeaves (side J T) F
    let t := 1+(L A).card+(L P).card
    let u := 1+(R A).card+(R P).card
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card →
    t≤k+bipartiteNum (side J S) → u≤m+bipartiteNum (side J T) →
    t=k+bipartiteNum (side J S) ∧ u=m+bipartiteNum (side J T) ∧
      k=weightedLeaves (side J S) (L (U.erase w))+weight w (A∪P) ∧
      m=weightedLeaves (side J T) (R (U.erase w))+weight w (A∩P) := by
  classical
  intro L R U E F k m t u tight lb rb
  let l : ↥S := ⟨w,s.both.1⟩
  let z : ↥T := ⟨w,s.both.2⟩
  have left (v : ↥S) (ve : v∈E) : v.val∈U := by
    obtain ⟨mark,h⟩ := eligible_iff.mp ve
    exact eligible_iff.mpr ⟨mark.imp mem_pull.mp mem_pull.mp,
      h.imp (fun ne eq => ne (Subtype.ext eq)) (fun a => ⟨mem_pull.mp a.1,mem_pull.mp a.2⟩)⟩
  have near := seam_loss l (E\L (U.erase w)) (A∪P) (by
    intro v hv
    obtain ⟨ve,no⟩ := mem_sdiff.mp hv
    have vu := left v ve
    have eq : v.val=w := Classical.byContradiction (fun ne => no (mem_pull.mpr (mem_erase.mpr ⟨ne,vu⟩)))
    refine ⟨Subtype.ext eq,?_⟩
    change w∈A∪P
    rw [←eq]
    exact mem_union.mpr (eligible_iff.mp vu).1)
  have far := seam_loss z (F\R (U.erase w)) (A∩P) (by
    intro v hv
    obtain ⟨vf,no⟩ := mem_sdiff.mp hv
    have info := eligible_iff.mp vf
    have eq : v.val=w := by
      apply Classical.byContradiction
      intro ne
      have vr : v.val≠r.val := fun h => ne (s.common (h.symm ▸ r.property) v.property)
      exact no (mem_pull.mpr (mem_erase.mpr ⟨ne,eligible_iff.mpr ⟨info.1.imp mem_pull.mp mem_pull.mp,Or.inl vr⟩⟩))
    have equal : v=z := Subtype.ext eq
    obtain ⟨a,p⟩ := info.2.resolve_left (not_not.mpr equal)
    exact ⟨equal,mem_inter.mpr ⟨mem_pull.mp a,mem_pull.mp p⟩⟩)
  have dl := restrict_leaves (side J S) E (L (U.erase w))
  have dr := restrict_leaves (side J T) F (R (U.erase w))
  have sum := (seam_tight_iff jc s xs ys xy drop A P U).mp tight
  have tally : weight w (A∪P)+weight w (A∩P)=weight w A+weight w P := by
    by_cases a : w∈A <;> by_cases p : w∈P <;> simp [weight,a,p]
  change (E\L (U.erase w)).card≤weight w (A∪P) at near
  change (F\R (U.erase w)).card≤weight w (A∩P) at far
  change k≤_ at dl
  change m≤_ at dr
  change weightedLeaves (side J S) (L (U.erase w))+bipartiteNum (side J S)+
    (weightedLeaves (side J T) (R (U.erase w))+bipartiteNum (side J T))+
    weight w A+weight w P=t+u at sum
  omega

#print axioms tight_wings
end Minimal180.OddBlock
