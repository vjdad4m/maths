import OneDefectHall189
import TwoShoreTight189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.OneDefectHall Graffiti189LongestPath.TruncatedHall Graffiti189LongestPath.ForeignPorts
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two from SmallSeparator189
set_option warningAsError true
set_option maxHeartbeats 2000000
namespace Graffiti189LongestPath.DefectiveCharge
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- All distance-two cut vertices are charged explicitly alongside
the internal nonneighbors and opposite-shore Hall destinations. -/
theorem defective_universal_shore_charge (hc : G.Connected) (d k : Nat) (A U B : Finset V)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (exactB : B.card≤k+1) (ab : Disjoint A B) (ub : Disjoint U B)
    (au : Disjoint A U)
    (large : k≤U.card)
    (closedA : ∀ x∈A,∀ y∉A,G.Adj x y → y∈B)
    (closedU : ∀ x∈U,∀ y∉U,G.Adj x y → y∈B)
    (cap : ∀ v, (DistanceTwo G v).card≤d)
    {r : V} (root : ∀ v∈A, v=r ∨ G.Adj r v)
    (a : ↥(A : Set V)) :
    A.card+G.degree a.val+((DistanceTwo G a.val)∩B).card ≤
      2*(G.induce (A : Set V)).degree a+d+2 := by
  classical
  let J := G.induce (A : Set V)
  let S := B.filter (G.Adj a.val)
  let T := A.filter (fun b => b≠a.val ∧ ¬G.Adj a.val b)
  let NU := shoreNeighbors G U S
  have aB : a.val∉B := fun e => disjoint_left.mp ab a.property e
  have aU : a.val∉U := fun e => disjoint_left.mp au a.property e
  have haveU := defective_hall k U B S conn ub exactB (filter_subset _ _) aU aB closedU
  change min U.card (S.card-1)≤NU.card at haveU
  have spend (C : Finset V) (na : a.val∉C)
      (closed : ∀ x∈C,∀ y∉C,G.Adj x y → y∈B) :
      shoreNeighbors G C S ⊆ DistanceTwo G a.val := by
    intro z hz
    obtain ⟨zc,s,ss,sz⟩ := mem_filter.mp hz
    have ne : a.val≠z := fun e => na (e.symm ▸ zc)
    have no : ¬G.Adj a.val z := fun e => aB (closed z zc a.val na e.symm)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc ne no (mem_filter.mp ss).2 sz)
  have spendT : T ⊆ DistanceTwo G a.val := by
    intro z hz
    obtain ⟨za,zne,no⟩ := mem_filter.mp hz
    rcases root a.val a.property with h|h
    · rcases root z za with eq|e
      · exact (zne (eq.trans h.symm)).elim
      · exact (no (h.symm ▸ e)).elim
    · rcases root z za with eq|e
      · exact (no (eq.symm ▸ h.symm)).elim
      · exact Graffiti189LongestPath.mem_distanceTwo.mpr
          (Graffiti189LongestPath.dist_two hc zne.symm no h.symm e)
  have dst : Disjoint NU T := disjoint_left.mpr (fun _ u t =>
    disjoint_left.mp au (mem_filter.mp t).1 (mem_filter.mp u).1)
  let R := (DistanceTwo G a.val)∩B
  have bn : Disjoint (NU∪T) R := disjoint_left.mpr (by
    intro z h hz
    have zb := (mem_inter.mp hz).2
    exact (mem_union.mp h).elim
      (fun hu => disjoint_left.mp ub (mem_filter.mp hu).1 zb)
      (fun ht => disjoint_left.mp ab (mem_filter.mp ht).1 zb))
  have sub : (NU∪T)∪R ⊆ DistanceTwo G a.val :=
    union_subset (union_subset (spend U aU closedU) spendT) inter_subset_left
  have spent := card_le_card sub
  rw [card_union_of_disjoint bn,card_union_of_disjoint dst] at spent
  have cc := cap a.val
  have sz := card_filter_le B (G.Adj a.val)
  change S.card≤B.card at sz
  rw [min_eq_right (by omega : S.card-1≤U.card)] at haveU
  let N := A.filter (G.Adj a.val)
  have ncard : N.card=J.degree a := by
    rw [← J.card_neighborFinset_eq_degree]
    refine card_bij' (fun v hv => (⟨v,(mem_filter.mp hv).1⟩ : ↥(A : Set V)))
      (fun v _ => v.val) ?_ ?_ ?_ ?_
    · intro v hv
      exact (J.mem_neighborFinset a _).mpr (mem_filter.mp hv).2
    · intro v hv
      exact mem_filter.mpr ⟨v.property,(J.mem_neighborFinset a v).mp hv⟩
    · intro v hv; rfl
    · intro v hv; exact Subtype.ext rfl
  have outside : G.degree a.val≤J.degree a+S.card := by
    have cover : G.neighborFinset a.val ⊆ N∪S := by
      intro z hz
      have ed := (G.mem_neighborFinset a.val z).mp hz
      by_cases az : z∈A
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨az,ed⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨closedA a.val a.property z az ed,ed⟩))
    have c := card_le_card cover
    rw [G.card_neighborFinset_eq_degree] at c
    have b := card_union_le N S
    omega
  have inside : A.card≤J.degree a+T.card+1 := by
    have cover : A⊆insert a.val (N∪T) := by
      intro z hz
      by_cases e : z=a.val
      · exact mem_insert.mpr (Or.inl e)
      by_cases ed : G.Adj a.val z
      · exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inl (mem_filter.mpr ⟨hz,ed⟩))))
      · exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inr (mem_filter.mpr ⟨hz,e,ed⟩))))
    have c := card_le_card cover
    have b := card_insert_le a.val (N∪T)
    have q := card_union_le N T
    omega
  change A.card+G.degree a.val+R.card≤2*J.degree a+d+2
  have cc' : (DistanceTwo G a.val).card≤d := cc
  omega

#print axioms defective_universal_shore_charge
end Graffiti189LongestPath.DefectiveCharge
