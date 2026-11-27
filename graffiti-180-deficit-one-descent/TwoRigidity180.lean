import Spine180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A possible failure at upper bipartization deficit at most two.
No horizontal edge, sparseness condition or lower graph is specified. -/
structure FailedTwo (G : SimpleGraph V) (r : V) (odd : Bool) (A : Finset V) : Prop where
  connected : G.Connected
  block : NoCut G
  order : 2<Fintype.card V
  rank : Fintype.card V≤bipartiteNum G+2
  independent : Indep G A
  bad : let P := parity G r odd
        weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card

namespace FailedTwo
variable {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V} (h : FailedTwo G r odd A)
include h

theorem not_confined : ¬A⊆parity G r odd := by
  classical
  let P := parity G r odd
  intro inc
  have b := confined_parity G h.connected (by have := h.order; omega) r odd.toNat A h.independent inc
  change 1+A.card+P.card≤weightedLeaves G (eligible A P r)+markedBip G (A∩P) at b
  have cap : markedBip G (A∩P)≤bipartiteNum G := by
    apply Finset.sup_le
    exact fun _ k => size_bip G (mem_filter.mp k).2.2
  have bad := h.bad
  change weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card at bad
  omega

theorem rigid (M : SimpleGraph V) [DecidableRel M.Adj] (tree : M.IsTree)
    (mg : M≤G) (root : r∉leaves M)
    (cross : ∀ {i j},M.Adj i j → (i∈parity G r odd ↔ j∉parity G r odd)) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    (∀ i∈A∪P,M.degree i≤2) ∧ (M.edgeFinset∩D.sym2).card+1=D.card := by
  classical
  intro P D
  obtain ⟨v,va,vp⟩ := Finset.not_subset.mp h.not_confined
  have pos : D.Nonempty := ⟨v,mem_sdiff.mpr ⟨mem_union_left _ va,fun e => vp (mem_inter.mp e).2⟩⟩
  have f := forest_strict M tree D pos
  have id := tree_defect M tree (by have := h.order; omega) r root A P
    (fun i ia j ja n e => h.independent i ia j ja n (mg e)) cross
  change Fintype.card V+_+(M.edgeFinset∩D.sym2).card=1+A.card+P.card+D.card+_ at id
  have bound : (eligible A P r∩leaves M).card≤weightedLeaves G (eligible A P r) :=
    le_sup (f:=fun K => (eligible A P r∩leaves K).card) (mem_filter.mpr ⟨mem_univ _,mg,tree⟩)
  have bad := h.bad
  change weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card at bad
  have rk := h.rank
  refine ⟨?_,by omega⟩
  intro i im
  have term := single_le_sum (s:=A∪P) (f:=fun v => M.degree v-2) (fun _ _ => Nat.zero_le _) im
  change M.degree i-2≤∑ v∈A∪P,(M.degree v-2) at term
  omega

/-- In a possible deficit-two failure a marked nonroot vertex has at
most one outward neighbor in the original graph. -/
theorem outward {v i j : V} (mark : v∈A∪parity G r odd) (vr : v≠r)
    (vi : G.Adj v i) (vj : G.Adj v j)
    (di : G.dist i r=G.dist v r+1) (dj : G.dist j r=G.dist v r+1) : i=j := by
  classical
  apply Classical.byContradiction
  intro ij
  have two := block_neighbors G h.connected h.order h.block r
  obtain ⟨M,mg,tr,rt,mi,mj,⟨z,mz,zi,zj⟩,cross⟩ :=
    branching_layer_tree h.connected vi.symm vj di dj two (fun eq => (vr eq).elim) odd
  have cap := (h.rigid M tr mg rt cross).1 v mark
  have inc : ({z,i,j}:Finset V)⊆M.neighborFinset v := insert_subset ((M.mem_neighborFinset ..).mpr mz)
    (insert_subset ((M.mem_neighborFinset ..).mpr mi.symm) (singleton_subset_iff.mpr ((M.mem_neighborFinset ..).mpr mj.symm)))
  have c := card_le_card inc
  rw [card_insert_of_not_mem (by simp [zi,zj]),card_pair (show i≠j from ij),card_neighborFinset_eq_degree] at c
  omega

end FailedTwo
#print axioms FailedTwo.rigid
#print axioms FailedTwo.outward
end Minimal180.DescentOne
