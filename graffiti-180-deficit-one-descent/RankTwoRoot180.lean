import BalancedBridge180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A failed rooted inequality at bipartization deficit at most two forces
a singly marked root. -/
theorem FailedTwo.root_disagreement {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) :
    let P := parity G r odd
    r∈(A∪P)\(A∩P) := by
  classical
  intro P
  let U := eligible A P r
  let D := (A∪P)\(A∩P)
  apply Classical.byContradiction
  intro root
  change r∉D at root
  obtain ⟨t,w,sp,tw,free⟩ := h.balanced_spine root
  change Spine G r D t at sp
  have cover : U=A∪P := by
    ext i
    constructor
    · intro v; exact mem_union.mpr (eligible_iff.mp v).1
    · intro v
      apply eligible_iff.mpr
      refine ⟨mem_union.mp v,?_⟩
      by_cases ir : i=r
      · subst i
        exact Or.inr (mem_inter.mp (Classical.byContradiction (fun no => root (mem_sdiff.mpr ⟨v,no⟩))))
      · exact Or.inl ir
  obtain ⟨s,sd,ts⟩ := sp.first_step
  have broken := h.bridge sp sd ts
  have color := spine_color G h.connected r odd A h.independent t s sp sd ts broken (h.free_independent sp tw free cover)
  have size := card_erase_add_one (mem_univ t)
  rw [card_univ] at size
  have bound := size_bip G color
  have two := block_neighbors G h.connected h.order h.block r
  have pos : 1<Fintype.card V := by have := h.order; omega
  have solved := rank_one_rooted G h.connected pos r two (by omega) odd A h.independent
  have bad := h.bad
  change weightedLeaves G U+bipartiteNum G<1+A.card+P.card at bad
  change 1+A.card+P.card≤weightedLeaves G U+bipartiteNum G at solved
  omega

/-- A possible deficit-two failure also forces the root to have exactly
two neighbors. -/
theorem FailedTwo.root_degree {G : SimpleGraph V} [DecidableRel G.Adj] {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) : G.degree r=2 := by
  classical
  let P := parity G r odd
  let H := alternating G P
  obtain ⟨hc,star⟩ := alternating_parity G h.connected r odd
  obtain ⟨T,th,tree⟩ := hc.exists_isTree_le
  obtain ⟨M,mh,mt,all,_⟩ := full_star_exchange H T th tree (by have := h.order; omega) r
  have mg : M≤G := fun _ _ e => (mh e).1
  have same : M.neighborFinset r=G.neighborFinset r := by
    ext v
    simp only [mem_neighborFinset]
    exact ⟨fun e => mg e,fun e => all v (star v e)⟩
  obtain ⟨i,j,ri,rj,ij⟩ := block_neighbors G h.connected h.order h.block r
  have rt : r∉leaves M := fun l => ij (leaf_unique M l (all i (star i ri)) (all j (star j rj)))
  have cap := (h.rigid M mt mg rt fun e => (mh e).2).1 r (mem_sdiff.mp h.root_disagreement).1
  have ge := card_le_card (show ({i,j}:Finset V)⊆G.neighborFinset r from insert_subset
    ((G.mem_neighborFinset ..).mpr ri) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr rj)))
  rw [card_pair ij,card_neighborFinset_eq_degree] at ge
  have eq := congrArg card same
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at eq
  omega

/-- The rooted inequality for all independent marks whose memberships
at the root agree, or for arbitrary marks if the root has degree at least
three. There is no sparsity or chord assumption. -/
theorem rank_two_root (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected) (block : NoCut G)
    (order : 2<Fintype.card V) (rank : Fintype.card V≤bipartiteNum G+2)
    (r : V) (odd : Bool) (A : Finset V) (ind : Indep G A) :
    let P := parity G r odd
    (3≤G.degree r ∨ (r∈A ↔ r∈P)) →
      1+A.card+P.card≤weightedLeaves G (eligible A P r)+bipartiteNum G := by
  intro P ok
  by_contra! bad
  have h : FailedTwo G r odd A := ⟨gc,block,order,rank,ind,bad⟩
  have deg := h.root_degree
  have root := h.root_disagreement
  change r∈(A∪P)\(A∩P) at root
  simp only [mem_sdiff,mem_union,mem_inter] at root
  rcases ok with high|balanced
  · omega
  · tauto

#print axioms FailedTwo.root_disagreement
#print axioms FailedTwo.root_degree
#print axioms rank_two_root
end Minimal180.DescentOne
