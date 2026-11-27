import Row1900
import Boundary

namespace OuterStar1900
namespace Sharp
open Finset SimpleGraph AutoGraphForge370 CubicBridges1160 HallRainbow1121

local instance (a b : ℕ) : DecidableRel (biclique a b).Adj := fun x y => by
  change Decidable (x.isLeft ∧ y.isRight ∨ x.isRight ∧ y.isLeft)
  infer_instance

abbrev G (m : ℕ) := biclique 2 (m+2)
abbrev V (m : ℕ) := Fin 2 ⊕ Fin (m+2)

private theorem connected (m : ℕ) : (G m).Connected := by
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl 0,?_⟩
  rintro (i|j)
  · have h : (G m).Adj (Sum.inl 0) (Sum.inr 0) := by simp [G,biclique,completeBipartiteGraph]
    have h' : (G m).Adj (Sum.inr 0) (Sum.inl i) := by simp [G,biclique,completeBipartiteGraph]
    exact h.reachable.trans h'.reachable
  · exact (show (G m).Adj (Sum.inl 0) (Sum.inr j) by simp [G,biclique,completeBipartiteGraph]).reachable

private theorem triangle (m : ℕ) : TriangleFree (G m) := by
  rintro (i|a) (j|b) (l|c) <;> simp [G,biclique,completeBipartiteGraph]

private theorem no_singleton (m : ℕ) (D : Finset (V m)) (hd : OuterDominating (G m) D) :
    2 ≤ D.card := by
  classical
  have other (u : V m) : ∃ v, v ≠ u ∧ ¬ (G m).Adj v u := by
    cases u with
    | inl i =>
      obtain ⟨j,hj⟩ := exists_ne i
      exact ⟨.inl j,fun eq => hj (Sum.inl.inj eq), by simp [G,biclique,completeBipartiteGraph]⟩
    | inr i =>
      obtain ⟨j,hj⟩ := exists_ne i
      exact ⟨.inr j,fun eq => hj (Sum.inr.inj eq), by simp [G,biclique,completeBipartiteGraph]⟩
  obtain ⟨a⟩ := hd.2.nonempty
  obtain ⟨u,hu,_⟩ := hd.1 a.val a.property
  obtain ⟨v,ne,no⟩ := other u
  by_contra! small
  have unique : ∀ x ∈ D, x=u := fun x hx => card_le_one.mp (by omega) x hx u hu
  obtain ⟨w,hw,edge⟩ := hd.1 v (fun hv => ne (unique v hv))
  exact no (unique w hw ▸ edge)

/-- K_{2,m+2} attains the maximum-degree bound at every degree m+2.
The known bipartite outer domination and clique-cover formulas are recovered. -/
theorem biclique_sharp (m : ℕ) :
    (G m).Connected ∧ TriangleFree (G m) ∧ (∀ v, 2 ≤ (G m).degree v) ∧
    (G m).maxDegree = m+2 ∧ Fintype.card (V m) = m+4 ∧
    outerNumber (G m) = some 2 ∧ cliqueCover (G m) = m+2 := by
  classical
  obtain ⟨left,right⟩ := biclique_degrees 2 (m+2)
  have bounds (v : V m) : 2 ≤ (G m).degree v ∧ (G m).degree v ≤ m+2 := by
    cases v with
    | inl a => rw [show (G m).degree (.inl a) = m+2 from left a]; omega
    | inr b => rw [show (G m).degree (.inr b) = 2 from right b]; omega
  have minTwo := fun v => (bounds v).1
  obtain ⟨v,d⟩ := (G m).exists_maximal_degree_vertex
  have big := (G m).degree_le_maxDegree (.inl 0)
  rw [show (G m).degree (.inl 0) = m+2 from left 0] at big
  have md : (G m).maxDegree = m+2 := le_antisymm (d ▸ (bounds v).2) big
  have n : Fintype.card (V m) = m+4 := by simp [V]; omega
  obtain ⟨o,ho,cap⟩ := max_degree_bound (G m) (triangle m) minTwo
  have lower : 2 ≤ o := by
    unfold outerNumber at ho
    split at ho
    · rename_i ex
      cases ho
      obtain ⟨D,hd,sz⟩ := Nat.find_spec ex
      exact sz ▸ no_singleton m D hd
    · contradiction
  change o + (G m).maxDegree ≤ Fintype.card (V m) at cap
  rw [md,n] at cap
  have eq : o = 2 := by omega
  exact ⟨connected m,triangle m,minTwo,md,n,eq ▸ ho,biclique_cover (by omega)⟩

/-- K₂,₂ is an equality example for the original Eulerian catalogue statement. -/
theorem square :
    2 ≤ Fintype.card (V 0) ∧ (G 0).Connected ∧ (∀ v, Even ((G 0).degree v)) ∧
      TriangleFree (G 0) ∧ outerNumber (G 0) = some 2 ∧ cliqueCover (G 0) = 2 := by
  obtain ⟨hc,ht,_,_,n,o,c⟩ := biclique_sharp 0
  refine ⟨by omega,hc,?_,ht,o,c⟩
  rintro (i|j)
  · exact ⟨1,(biclique_degrees 2 2).1 i⟩
  · exact ⟨1,(biclique_degrees 2 2).2 j⟩

#print axioms biclique_sharp
#print axioms square
end Sharp
end OuterStar1900
