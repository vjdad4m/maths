import ForeignPorts189
open Finset SimpleGraph Graffiti189LongestPath
open Graffiti189LongestPath.ForeignPorts
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
set_option warningAsError true
namespace Graffiti189LongestPath.OneDefectHall
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
theorem defective_hall (k : Nat) (A B S : Finset V)
    (conn : ∀ T : Finset V, T.card < k → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (dis : Disjoint A B) (exactB : B.card≤k+1) (ss : S⊆B)
    {z : V} (za : z∉A) (zb : z∉B)
    (boundary : ∀ x∈A,∀ y∉A,G.Adj x y → y∈B) :
    min A.card (S.card-1) ≤ (shoreNeighbors G A S).card := by
  classical
  let N := shoreNeighbors G A S
  apply Nat.le_of_not_gt
  intro h
  have hA : N.card < A.card := h.trans_le (min_le_left _ _)
  have hS : N.card < S.card-1 := h.trans_le (min_le_right _ _)
  have sub : N⊆A := filter_subset _ _
  have nl : (A\N).Nonempty := card_pos.mp (by have c := card_sdiff_add_card_eq_card sub; omega)
  obtain ⟨u,hu⟩ := nl
  let B' := (B\S)∪N
  have vd : z∉A\N := fun h => za (mem_sdiff.mp h).1
  have vb : z∉B' := fun h => (mem_union.mp h).elim (fun h => zb (mem_sdiff.mp h).1)
    (fun h => za (sub h))
  have d : Disjoint (A\N) B' := disjoint_left.mpr (by
    intro a ha hb
    exact (mem_union.mp hb).elim
      (fun h => disjoint_left.mp dis (mem_sdiff.mp ha).1 (mem_sdiff.mp h).1)
      (mem_sdiff.mp ha).2)
  have bound : ∀ a∈A\N,∀ b∉A\N,G.Adj a b → b∈B' := by
    intro a ha b hb e
    by_cases ba : b∈A
    · exact mem_union.mpr (Or.inr (Classical.byContradiction (fun h => hb (mem_sdiff.mpr ⟨ba,h⟩))))
    have bb := boundary a (mem_sdiff.mp ha).1 b ba e
    have bs : b∉S := fun h => (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1,b,h,e.symm⟩)
    exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨bb,bs⟩))
  have lo := Graffiti189LongestPath.boundary_card_of_connectivity k conn hu vd vb d bound
  have hi := card_union_le (B\S) N
  have sz := card_sdiff_add_card_eq_card ss
  change k≤((B\S)∪N).card at lo
  omega


#print axioms defective_hall
end Graffiti189LongestPath.OneDefectHall
