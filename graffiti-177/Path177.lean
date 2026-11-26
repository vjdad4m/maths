import TreeEquality
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-! # The equality paths for Graffiti.pc 177 -/
open Finset SimpleGraph
open scoped BigOperators

namespace Graffiti177.Path

noncomputable local instance pathDec (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  Classical.decRel _

/-- The only degree-one vertices are the two endpoints. -/
private lemma degree (k : ℕ) (v : Fin (k+3)) :
    (pathGraph (k+3)).degree v = if v.val = 0 ∨ v.val = k+2 then 1 else 2 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hv := v.isLt
  by_cases hzero : v.val = 0
  · let next : Fin (k+3) := ⟨1,by omega⟩
    have hs : (pathGraph (k+3)).neighborFinset v = {next} := by
      ext w
      simp only [mem_neighborFinset, pathGraph_adj, mem_singleton, Fin.ext_iff]
      change v.val + 1 = w.val ∨ w.val + 1 = v.val ↔ w.val = 1
      omega
    simp [hs, hzero]
  by_cases hend : v.val = k+2
  · let prev : Fin (k+3) := ⟨k+1,by omega⟩
    have hs : (pathGraph (k+3)).neighborFinset v = {prev} := by
      ext w
      simp only [mem_neighborFinset, pathGraph_adj, mem_singleton, Fin.ext_iff]
      have hw := w.isLt
      change v.val + 1 = w.val ∨ w.val + 1 = v.val ↔ w.val = k+1
      omega
    simp [hs, hend]
  · let prev : Fin (k+3) := ⟨v.val-1,by omega⟩
    let next : Fin (k+3) := ⟨v.val+1,by omega⟩
    have hne : prev ≠ next := by simp [prev,next,Fin.ext_iff]
    have hs : (pathGraph (k+3)).neighborFinset v = {prev,next} := by
      ext w
      simp only [mem_neighborFinset, pathGraph_adj, mem_insert, mem_singleton, Fin.ext_iff]
      change v.val + 1 = w.val ∨ w.val + 1 = v.val ↔ w.val = v.val-1 ∨ w.val = v.val+1
      omega
    simp [hs, hne, hzero, hend]

private lemma tree (k : ℕ) : (pathGraph (k+3)).IsTree := by
  classical
  let l : Fin (k+3) := ⟨0,by omega⟩
  let r : Fin (k+3) := ⟨k+2,by omega⟩
  have hne : l ≠ r := by simp [l,r,Fin.ext_iff]
  have point (v : Fin (k+3)) :
      (pathGraph (k+3)).degree v + (if v ∈ ({l,r} : Finset _) then 1 else 0) = 2 := by
    rw [degree]
    simp only [mem_insert, mem_singleton, Fin.ext_iff, l, r]
    split_ifs <;> decide
  have hs := sum_congr (show (univ : Finset (Fin (k+3))) = univ from rfl) (fun v _ => point v)
  rw [sum_add_distrib, SimpleGraph.sum_degrees_eq_twice_card_edges] at hs
  have count (S : Finset (Fin (k+3))) : (∑ v, if v ∈ S then 1 else 0 : ℕ) = S.card := by simp
  have ends : (∑ v : Fin (k+3), if v ∈ ({l,r} : Finset _) then 1 else 0 : ℕ) = 2 :=
    (count _).trans (card_pair hne)
  rw [ends] at hs
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hs
  apply isTree_iff_connected_and_card.mpr
  refine ⟨pathGraph_connected _, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-- On Mathlib's path on k+3 vertices, equality holds precisely when its
order is odd. -/
theorem equality_iff_odd (k : ℕ) :
    maxLeaves (pathGraph (k+3)) + bipartiteNum (pathGraph (k+3)) =
      2 * independence (pathGraph (k+3)) + secondDegree (pathGraph (k+3)) ↔
      (k+3) % 2 = 1 := by
  classical
  rw [TreeEquality.equality_iff _ (tree k) (by simp)]
  constructor
  · rintro ⟨A, ha, hb, hl, _⟩
    have toggle {x y : Fin (k+3)} (h : (pathGraph _).Adj x y) : y ∈ A ↔ x ∉ A := by
      constructor
      · exact fun hy hx => ha x hx y hy h.ne h
      · intro hx
        by_contra hy
        exact hb x (mem_sdiff.mpr ⟨mem_univ _,hx⟩) y (mem_sdiff.mpr ⟨mem_univ _,hy⟩) h.ne h
    have alt (i : ℕ) (hi : i < k+3) : (⟨i,hi⟩ : Fin (k+3)) ∈ A ↔ i % 2 = 0 := by
      induction i with
      | zero =>
        have hz := hl (⟨0,hi⟩ : Fin (k+3)) (by simp [degree])
        exact ⟨fun _ => rfl, fun _ => hz⟩
      | succ i ih =>
        have hprev : i < k+3 := by omega
        have adj : (pathGraph _).Adj (⟨i,hprev⟩ : Fin (k+3)) ⟨i+1,hi⟩ :=
          pathGraph_adj.mpr (Or.inl rfl)
        rw [toggle adj, ih hprev]
        omega
    have hlast := hl (⟨k+2,by omega⟩ : Fin (k+3)) (by simp [degree])
    have h := (alt (k+2) (by omega)).mp hlast
    omega
  · intro odd
    let A := univ.filter (fun v : Fin (k+3) => v.val % 2 = 0)
    refine ⟨A, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy _ h
      have h₁ := (mem_filter.mp hx).2
      have h₂ := (mem_filter.mp hy).2
      rcases pathGraph_adj.mp h with h | h <;> omega
    · intro x hx y hy _ h
      have h₁ : x.val % 2 ≠ 0 := fun he => (mem_sdiff.mp hx).2 (by simp [A,he])
      have h₂ : y.val % 2 ≠ 0 := fun he => (mem_sdiff.mp hy).2 (by simp [A,he])
      rcases pathGraph_adj.mp h with h | h <;> omega
    · intro v hv
      rw [degree] at hv
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      split_ifs at hv with h
      · rcases h with h | h <;> omega
      · omega
    · intro v hv
      rw [degree] at hv
      split_ifs at hv <;> omega

#print axioms equality_iff_odd
end Graffiti177.Path
