import Distances180

set_option warningAsError true
namespace Converse180
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def violates {X : Type*} [Fintype X] [DecidableEq X] (H : SimpleGraph X) : Prop :=
  maxLeaves H + bipartiteNum H < 1 + independence H + maxEven H

theorem weighted_all : weightedLeaves G univ = maxLeaves G := by
  classical
  simp [weightedLeaves,maxLeaves]

omit [DecidableEq V] in
theorem even_equiv (r : V) : evenCount G r = (parity G r false).card := by
  classical
  unfold evenCount parity
  congr 1
  ext v
  simp [dist_comm (u:=r)]

omit [DecidableEq V] in
theorem even_max (r : V) : evenCount G r ≤ maxEven G := le_sup (mem_univ r)

theorem twin_counter (hc : G.Connected) (hn : 1 < Fintype.card V) (r : V) (odd : Bool)
    (A : Finset V) (ai : Indep G A) (root : odd=false → r ∉ A)
    (bad : weightedLeaves G (univ.erase r) + bipartiteNum G ≤ A.card + (parity G r odd).card) :
    violates (twin G r) := by
  classical
  have leaf := twin_leaves G r hn
  have bip := twin_bip G r
  have indep := indep_card_le (twin G r) (twin_indep G r A ai (!odd)
    (fun h => root (by cases odd <;> simp_all)))
  rw [twinSet_card] at indep
  have ev := even_max (twin G r) (twinRoot r odd)
  rw [twin_even G hc r odd] at ev
  unfold violates
  cases odd <;> simp only [Bool.not_true,Bool.not_false,Bool.toNat_false,Bool.toNat_true] at * <;> omega

/-- A finite simple connected counterexample to the unrestricted conjecture,
with an explicit upper bound on its order. -/
def counterexampleAtMost (cap : ℕ) : Prop :=
  ∃ (W : Type u) (f : Fintype W) (dec : DecidableEq W), letI := f; letI := dec
    ∃ H : SimpleGraph W, H.Connected ∧ 1 < Fintype.card W ∧
      Fintype.card W ≤ cap ∧ violates H

/-- The exact converse. The graph may be any connected piece, including a
biconnected block. One pendant-decorated copy, or two such copies linked
through a common new vertex, witnesses failure of the original inequality. -/
theorem realize (hc : G.Connected) (hn : 1 < Fintype.card V) (r : V) (odd : Bool)
    (A : Finset V) (ai : Indep G A)
    (bad : weightedLeaves G (eligible A (parity G r odd) r) + bipartiteNum G <
      1+A.card+(parity G r odd).card) :
    counterexampleAtMost.{u} (4*Fintype.card V-1) := by
  classical
  let P := parity G r odd
  let D := (univ \ (A ∪ P)).erase r
  let H := decorate G D
  let x : Deco D := .inl r
  let B := if r ∈ A ∧ r ∈ P then univ else (univ : Finset V).erase r
  let I : Finset (Deco D) := A.disjSum univ
  have da : Disjoint A D := disjoint_left.mpr (fun v va vd =>
    (mem_sdiff.mp (mem_of_mem_erase vd)).2 (mem_union_left _ va))
  have dp : Disjoint P D := disjoint_left.mpr (fun v vp vd =>
    (mem_sdiff.mp (mem_of_mem_erase vd)).2 (mem_union_right _ vp))
  have mask : B \ D = eligible A P r := by
    ext v
    by_cases h : r ∈ A ∧ r ∈ P
    · have ru : r ∈ A ∪ P := mem_union_left _ h.1
      by_cases e : v = r
      · subst v; simp [B,D,eligible,h,ru]
      · simp [B,D,eligible,h,e]
    · by_cases e : v = r
      · subst v; simp [B,D,eligible,h]
      · simp [B,D,eligible,h,e]; tauto
  have dl := deco_leaves G hn D B
  rw [mask] at dl
  have db := deco_bip G D
  have ind : Indep H I := deco_indep G D A ai da
  have sizeI : I.card = A.card + D.card := by simp [I]
  have sizeP : (parity H x odd).card = P.card + D.card := by
    rw [show parity H x odd = P.disjSum (univ : Finset ↥D) from deco_parity G hc r odd D dp]
    simp
  have score : weightedLeaves H (B.disjSum (univ : Finset ↥D)) + bipartiteNum H ≤
      I.card+(parity H x odd).card := by
    change weightedLeaves G (eligible A P r)+bipartiteNum G < 1+A.card+P.card at bad
    change weightedLeaves H _ ≤ _ at dl
    change bipartiteNum H ≤ _ at db
    omega
  have con : H.Connected := (deco_layers G hc r D).1
  have dsub : D ⊆ (univ : Finset V).erase r := fun _ v =>
    mem_erase.mpr ⟨(mem_erase.mp v).1,mem_univ _⟩
  have dsmall := card_le_card dsub
  rw [card_erase_of_mem (mem_univ r),card_univ] at dsmall
  have sz : Fintype.card (Deco D) = Fintype.card V + D.card := by simp [Deco]
  have non : 1 < Fintype.card (Deco D) := by omega
  by_cases both : r ∈ A ∧ r ∈ P
  · have po : odd=false := by
      have er := (mem_parity G r r odd).mp both.2
      rw [dist_self] at er
      cases odd <;> simp_all
    subst odd
    have un : B.disjSum (univ : Finset ↥D) = univ := by
      ext v; rcases v with v|v <;> simp [B,both]
    rw [un,weighted_all] at score
    have le := indep_card_le H ind
    have ee := even_max H x
    rw [even_equiv] at ee
    refine ⟨Deco D,inferInstance,inferInstance,H,con,non,by omega,?_⟩
    unfold violates
    omega
  · have er : B.disjSum (univ : Finset ↥D) = (univ : Finset (Deco D)).erase x := by
      ext v; rcases v with v|v <;> simp [B,both,x]
    rw [er] at score
    have root : odd=false → x ∉ I := by
      intro e h
      have ar : r ∈ A := inl_mem_disjSum.mp h
      apply both
      exact ⟨ar,(mem_parity G r r odd).mpr (by simp [e,dist_self])⟩
    have nn : Fintype.card (Twin (Deco D)) = 2*Fintype.card (Deco D)+1 := by
      simp only [Twin,Fintype.card_sum,Fintype.card_unit]; omega
    exact ⟨Twin (Deco D),inferInstance,inferInstance,twin H x,(twin_layers H con x odd).1,by omega,
      by omega,twin_counter H con non x odd I ind root score⟩

/-- Failure of the original rooted predicate supplies its violating independent
set, with no separately supplied graph or numerical transfer hypotheses. -/
theorem of_failed_local (hc : G.Connected) (hn : 1 < Fintype.card V) (r : V) (odd : Bool)
    (fail : ¬ localBound G r (parity G r odd)) :
    counterexampleAtMost.{u} (4*Fintype.card V-1) := by
  classical
  unfold localBound at fail
  push_neg at fail
  obtain ⟨A,ai,bad⟩ := fail
  exact realize G hc hn r odd A ai bad

#print axioms of_failed_local
#print axioms twin_counter
#print axioms realize
end Converse180
