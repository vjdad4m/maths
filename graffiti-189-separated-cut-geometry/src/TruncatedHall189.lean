import ForeignPorts189
open Finset SimpleGraph Graffiti189LongestPath
open Graffiti189LongestPath.ForeignPorts
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
set_option warningAsError true
namespace Graffiti189LongestPath.TruncatedHall
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] in
theorem truncated_hall (k : Nat) (A B S : Finset V)
    (conn : ∀ T : Finset V, T.card < k → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (dis : Disjoint A B) (exactB : B.card=k) (ss : S⊆B)
    {z : V} (za : z∉A) (zb : z∉B)
    (boundary : ∀ x∈A,∀ y∉A,G.Adj x y → y∈B) :
    min A.card S.card ≤ (shoreNeighbors G A S).card := by
  classical
  let N := shoreNeighbors G A S
  apply Nat.le_of_not_gt
  intro h
  have hA : N.card < A.card := h.trans_le (min_le_left _ _)
  have hS : N.card < S.card := h.trans_le (min_le_right _ _)
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

/-- A vertex with more than half the parity budget in exact-cut neighbors
forces any other cut-separated shore to be small, even without connectivity
or a minimum order assumption on that shore. -/
theorem across_two_shores_budget (hc : G.Connected) (d k : Nat) (A R B : Finset V)
    (conn : ∀ T : Finset V, T.card < k → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (ab : Disjoint A B) (rb : Disjoint R B) (ar : Disjoint A R) (exactB : B.card=k)
    (large : k≤A.card) {z : V} (za : z∉A) (zr : z∉R) (zb : z∉B)
    (edgeA : ∀ x∈A,∀ y∉A,G.Adj x y → y∈B)
    (edgeR : ∀ x∈R,∀ y∉R,G.Adj x y → y∈B)
    (cap : (EvenFrom G z).card≤d+1)
    (many : d<2*(B.filter (G.Adj z)).card) :
    R.card+(B.filter (G.Adj z)).card≤d := by
  classical
  let S := B.filter (G.Adj z)
  let P := shoreNeighbors G A S
  let Q := shoreNeighbors G R S
  have loA := truncated_hall k A B S conn ab exactB (filter_subset _ _) za zb edgeA
  have loR := truncated_hall k R B S conn rb exactB (filter_subset _ _) zr zb edgeR
  have s := card_filter_le B (G.Adj z)
  change S.card≤B.card at s
  have ss : S.card≤A.card := by omega
  rw [min_eq_right ss] at loA
  change S.card≤P.card at loA
  change min R.card S.card≤Q.card at loR
  have spend (C : Finset V) (zc : z∉C)
      (edge : ∀ x∈C,∀ y∉C,G.Adj x y → y∈B) :
      shoreNeighbors G C S ⊆ DistanceTwo G z := by
    intro u hu
    obtain ⟨uc,p,ps,pu⟩ := mem_filter.mp hu
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc (fun e => zc (e.symm ▸ uc))
        (fun ed => zb (edge u uc z zc ed.symm)) (mem_filter.mp ps).2 pu)
  have dis : Disjoint P Q := disjoint_left.mpr (by
    intro u up uq
    exact disjoint_left.mp ar (mem_filter.mp up).1 (mem_filter.mp uq).1)
  have c := card_le_card (union_subset (spend A za edgeA) (spend R zr edgeR))
  rw [card_union_of_disjoint dis] at c
  have ca := distanceTwo_le_of_even d z cap
  change d<2*S.card at many
  change R.card+S.card≤d
  by_cases h : S.card≤R.card
  · rw [min_eq_right h] at loR
    omega
  · rw [min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h))] at loR
    omega
#print axioms truncated_hall
#print axioms across_two_shores_budget
end Graffiti189LongestPath.TruncatedHall
