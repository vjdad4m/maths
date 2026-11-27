import Sharp

namespace Chain5169
open SimpleGraph Finset Graffiti326 AutoGraphForge378 TriangleMatching1078 BullCover1125 Packing2560

/-- Two disjoint induced bulls require ten vertices. -/
private theorem packing_small {W : Type*} [Fintype W] (G : SimpleGraph W)
    (small : Fintype.card W < 10) : bullPacking G ≤ 1 := by
  classical
  apply Finset.sup_le
  intro k hk
  obtain ⟨f,sep⟩ := (mem_filter.mp hk).2
  let pick (q : Fin k × Fin 5) := f q.1 q.2
  have inj : Function.Injective pick := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    have ij : i=j := Classical.byContradiction (fun ne => sep i j ne a b h)
    subst j
    exact Prod.ext rfl ((f i).injective h)
  have order := Fintype.card_le_of_injective pick inj
  simp only [Fintype.card_prod,Fintype.card_fin] at order
  change k ≤ 1
  omega

theorem unrestricted_minimal_order {W : Type*} [Fintype W] (G : SimpleGraph W) (cl : Free G claw)
    {r : ℕ} (num : edgeCoverValue G = some r)
    (viol : (lineDomination G : ℚ) < (3/5 : ℚ)*r + -1) : 10 ≤ Fintype.card W := by
  classical
  by_contra! small
  have iso : IsolateFree G := by
    by_contra h
    simp [edgeCoverValue,h] at num
  have eq : edgeCoverNumber G = r := by simpa [edgeCoverValue,iso] using num
  have cover := cover_from_matching iso
  have refinedBound := Packing2560.refined iso cl
  have pack := packing_small G small
  obtain ⟨f,ok⟩ := matchingNumber_attained G
  have maxM : HasMaximalMatching G (matchingNumber G) := by
    refine ⟨f,ok,fun x hx y hy adj => ?_⟩
    have h := matchingNumber_upper (matching_extend ok hx hy adj)
    omega
  have dom := lineDomination_le_of_maximal G maxM
  have q : (5:ℚ)*lineDomination G+5 < 3*r := by linarith
  have integral : 5*lineDomination G+5 < 3*r := by exact_mod_cast q
  by_cases low : lineDomination G ≤ 2 <;> omega

/-- Two vertex-disjoint copies of the bull, with no edges between them. -/
abbrev twoBulls := listed (n:=10) [(0,1),(0,2),(1,3),(0,4),(1,4),
                                   (5,6),(5,7),(6,8),(5,9),(6,9)]

private def physical {a b : Fin 10} (ab : twoBulls.Adj a b) : twoBulls.edgeSet := ⟨s(a,b),ab⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem no_claw : Free twoBulls claw := by
  have localCheck : ∀ x a b c : Fin 10, twoBulls.Adj x a → twoBulls.Adj x b → twoBulls.Adj x c →
      a ≠ b → a ≠ c → b ≠ c → twoBulls.Adj a b ∨ twoBulls.Adj a c ∨ twoBulls.Adj b c := by
    intro x a b c hx ha hc ab ac bc
    revert ab ac bc hc ha hx
    revert a b c
    fin_cases x <;> decide
  rintro ⟨f⟩
  have sp (i : Fin 4) (h : claw.Adj 0 i) : twoBulls.Adj (f 0) (f i) := f.map_rel_iff.mpr h
  have ne (i j : Fin 4) (h : i ≠ j) : f i ≠ f j := fun e => h (f.injective e)
  rcases localCheck _ _ _ _ (sp 1 (by decide)) (sp 2 (by decide)) (sp 3 (by decide))
    (ne 1 2 (by decide)) (ne 1 3 (by decide)) (ne 2 3 (by decide)) with h|h|h
  all_goals exact (by decide : ¬claw.Adj _ _) (f.map_rel_iff.mp h)

private theorem covers_six : edgeCoverNumber twoBulls = 6 := by
  let P : Finset twoBulls.edgeSet := {physical (a:=0) (b:=2) (by decide),physical (a:=1) (b:=3) (by decide),
    physical (a:=0) (b:=4) (by decide),physical (a:=5) (b:=7) (by decide),
    physical (a:=6) (b:=8) (by decide),physical (a:=5) (b:=9) (by decide)}
  have good : Covers twoBulls P := by decide
  have cost : P.card = 6 := by decide
  have upper : edgeCoverNumber twoBulls ≤ 6 := Nat.sInf_le ⟨P,cost,good⟩
  let S : Finset (Fin 10) := {2,3,4,7,8,9}
  have independent : ∀ a ∈ S, ∀ b ∈ S, ¬twoBulls.Adj a b := by decide
  have size : S.card = 6 := by decide
  have lower (C : Finset twoBulls.edgeSet) (cov : Covers twoBulls C) : 6 ≤ C.card := by
    classical
    choose owner used incident using cov
    let pick (a : ↥S) : ↥C := ⟨owner a.val,used a.val⟩
    have inj : Function.Injective pick := by
      intro a b eq
      apply Subtype.ext
      apply Classical.byContradiction
      intro ne
      have same : owner a.val = owner b.val := congrArg Subtype.val eq
      have both := (Sym2.mem_and_mem_iff ne).mp ⟨incident a.val,same ▸ incident b.val⟩
      exact independent a.val a.property b.val b.property
        (show s(a.val,b.val) ∈ twoBulls.edgeSet from both ▸ (owner a.val).property)
    simpa [size] using Fintype.card_le_of_injective pick inj
  obtain ⟨C,n,h⟩ := Nat.sInf_mem (s:={k | ∃ C : Finset twoBulls.edgeSet, C.card=k ∧ Covers twoBulls C})
    ⟨_,P,rfl,good⟩
  exact le_antisymm upper ((lower C h).trans_eq n)

theorem smallest_unrestricted : Fintype.card (Fin 10) = 10 ∧ Free twoBulls claw ∧
    edgeCoverValue twoBulls = some 6 ∧ lineDomination twoBulls = 2 ∧
    (lineDomination twoBulls : ℚ) < (3/5 : ℚ)*6 + -1 := by
  have iso : IsolateFree twoBulls := by unfold IsolateFree; decide
  let f : Fin 2 × Bool ↪ Fin 10 := ⟨fun p => if p.1=0 then (if p.2 then 1 else 0)
    else (if p.2 then 6 else 5),by unfold Function.Injective; decide⟩
  have maxM : HasMaximalMatching twoBulls 2 := ⟨f,by decide,by decide⟩
  have lo := five_per_edge twoBulls iso no_claw
  rw [Fintype.card_fin] at lo
  have hi := lineDomination_le_of_maximal twoBulls maxM
  have eq : lineDomination twoBulls = 2 := by omega
  exact ⟨Fintype.card_fin _,no_claw,by simp [edgeCoverValue,iso,covers_six],eq,by rw [eq]; norm_num⟩

#print axioms unrestricted_minimal_order
#print axioms smallest_unrestricted
end Chain5169
