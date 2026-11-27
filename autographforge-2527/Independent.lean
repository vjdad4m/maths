import Theta

namespace ThetaIndependent2527
open Finset SimpleGraph TriangleMatching1078 AutoGraphForge378

variable {U : Type*} [Fintype U] (G : SimpleGraph U)

/-- GraphCalc minimizes the size of a vertex set that is independent and
dominates every closed neighborhood. -/
noncomputable def independentDomination : ℕ := sInf {s : ℕ | ∃ S : Finset U,
  S.card = s ∧ G.IsIndepSet S ∧ Dominates G S}

/-- A maximum independent set is dominating, so the feasible sizes are nonempty. -/
theorem attained : ∃ S : Finset U, S.card = independentDomination G ∧
    G.IsIndepSet S ∧ Dominates G S := by
  classical
  obtain ⟨S,hS⟩ := maximumIndepSet_exists (G := G)
  have dom : Dominates G S := by
    intro v
    by_contra! missed
    have outside : v ∉ S := missed.1
    have nonadj (u : U) (hu : u ∈ S) : ¬G.Adj v u := missed.2 u hu
    have larger : G.IsIndepSet (↑(insert v S : Finset U) : Set U) := by
      intro a ha b hb ne ab
      rcases mem_insert.mp ha with rfl|aS <;> rcases mem_insert.mp hb with rfl|bS
      · exact ne rfl
      · exact nonadj b bS ab
      · exact nonadj a aS ab.symm
      · exact hS.isIndepSet aS bS ne ab
    have bound := hS.maximum _ larger
    rw [card_insert_of_not_mem outside] at bound
    omega
  exact Nat.sInf_mem (s := {s : ℕ | ∃ T : Finset U, T.card = s ∧ G.IsIndepSet T ∧ Dominates G T})
    ⟨S.card,S,rfl,hS.isIndepSet,dom⟩

theorem universal_of_one (one : independentDomination G = 1) :
    ∃ c, ∀ v, v ≠ c → G.Adj v c := by
  obtain ⟨S,hs,_,dom⟩ := attained G
  obtain ⟨c,rfl⟩ := card_eq_one.mp (hs.trans one)
  refine ⟨c,fun v ne => ?_⟩
  rcases dom v with h|⟨u,hu,vu⟩
  · exact (ne (mem_singleton.mp h)).elim
  · rwa [mem_singleton.mp hu] at vu

/-- A triangle-free graph with independent domination one is exactly a star
about its universal vertex (allowing a single vertex). -/
theorem star_of_one (tri : TriangleFree G) (one : independentDomination G = 1) :
    ∃ c, ∀ u v, G.Adj u v ↔ u ≠ v ∧ (u=c ∨ v=c) := by
  obtain ⟨c,hc⟩ := universal_of_one G one
  refine ⟨c,fun u v => ⟨fun uv => ⟨uv.ne,?_⟩,?_⟩⟩
  · by_contra! neither
    exact tri u v c uv (hc v neither.2) (hc u neither.1).symm
  · rintro ⟨ne,rfl|rfl⟩
    · exact (hc v ne.symm).symm
    · exact hc u ne

/-- At independent domination one the only possible edge optimum is one
on nontrivial triangle-free graphs. -/
theorem one_boundary [DecidableRel G.Adj] (order : 2 ≤ Fintype.card U)
    (tri : TriangleFree G) (one : independentDomination G = 1) :
    lineDomination G = 1 ∧ minMaximalMatching G = 1 := by
  classical
  letI : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp order
  obtain ⟨c,star⟩ := star_of_one G tri one
  obtain ⟨w,ne⟩ := exists_ne c
  have cw : G.Adj c w := (star c w).mpr ⟨ne.symm,Or.inl rfl⟩
  let m : Fin 1 × Bool ↪ U := ⟨fun p => if p.2 then w else c,by
    rintro ⟨i,a⟩ ⟨j,b⟩ eq
    have ij := Subsingleton.elim i j
    cases a <;> cases b <;> simp_all⟩
  have mat : HasMaximalMatching G 1 := by
    refine ⟨m,fun _ => cw,?_⟩
    have mem : c ∈ Graffiti326.support m := (Graffiti326.mem_support m).mpr ⟨0,false,rfl⟩
    intro u hu v hv uv
    rcases ((star u v).mp uv).2 with rfl|rfl
    · exact hu mem
    · exact hv mem
  have hi : minMaximalMatching G ≤ 1 := Nat.sInf_le mat
  have compare := lineDomination_le_matching G
  obtain ⟨D,sz,dom⟩ := EulerDom574.line_attained G
  obtain ⟨e,he,_⟩ := (dominates_iff G D).mp dom ⟨s(c,w),cw⟩
  have pos := card_pos.mpr (show D.Nonempty from ⟨e,he⟩)
  omega

theorem bipartite_one [DecidableRel G.Adj] (order : 2 ≤ Fintype.card U)
    (bip : G.Colorable 2) (one : independentDomination G = 1) :
    lineDomination G = 1 ∧ minMaximalMatching G = 1 := by
  obtain ⟨color⟩ := bip
  apply one_boundary G order _ one
  intro u v w uv vw wu
  exact (by decide : ∀ x y z : Fin 2, x≠y → y≠z → ¬z≠x) _ _ _
    (color.valid uv) (color.valid vw) (color.valid wu)

#print axioms bipartite_one
#print axioms star_of_one
#print axioms one_boundary
end ThetaIndependent2527
