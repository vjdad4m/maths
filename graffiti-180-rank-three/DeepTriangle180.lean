import DeepFork180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The three-pair alternative is impossible at a deep layer outside
the parity mark. Its three centers would have one common predecessor
inside the mark, and that predecessor would have three children. -/
theorem deep_triangle_bound (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (two : ∃ s t,G.Adj r s ∧ G.Adj r t ∧ s≠t)
    (odd : Bool) (A : Finset V) (ai : Indep G A) (rk : Fintype.card V≤bipartiteNum G+3)
    (u v w a b c : V) (uv : u≠v) (uw : u≠w) (vw : v≠w) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (au : Pred G r a u) (bu : Pred G r b u) (bv : Pred G r b v) (cv : Pred G r c v)
    (aw : Pred G r a w) (cw : Pred G r c w) (deep : 3≤G.dist u r) :
    let P := parity G r odd
    u∉P → u∈A∪P → v∈A∪P → w∈A∪P →
      1+A.card+P.card≤weightedLeaves G (eligible A P r)+bipartiteNum G := by
  classical
  intro P outside um vm wm
  by_contra! bad
  have eqV : G.dist v r=G.dist u r := by have := bu.2; have := bv.2; omega
  have eqW : G.dist w r=G.dist u r := by have := au.2; have := aw.2; omega
  have self : G.dist r r=0 := dist_self
  have ur : u≠r := by intro e; rw [e] at deep; omega
  have vr : v≠r := by intro e; rw [e] at eqV; omega
  have wr : w≠r := by intro e; rw [e] at eqW; omega
  obtain ⟨y,uy,dy⟩ := Graffiti169.exists_predecessor G gc r u ur
  obtain ⟨z,vz,dz⟩ := Graffiti169.exists_predecessor G gc r v vr
  obtain ⟨k,wk,dk⟩ := Graffiti169.exists_predecessor G gc r w wr
  have yy := deep_fork_parents G gc hn r two odd A ai rk u v b a c y z uv ab bc.symm ac
    bu bv au cv ⟨uy,dy⟩ ⟨vz,dz⟩ deep um vm bad
  have yk := deep_fork_parents G gc hn r two odd A ai rk u w a b c y k uw ab.symm ac.symm bc
    au aw bu cw ⟨uy,dy⟩ ⟨wk,dk⟩ deep um wm bad
  subst z
  subst k
  have py : Pred G r u y := ⟨uy,dy⟩
  have yp : y∈P := by
    by_contra no
    exact outside ((pred_vertical G r odd py).2.mpr no)
  have yr : y≠r := by intro e; rw [e,self] at dy; omega
  have ym : y∈(A∪P).erase r := mem_erase.mpr ⟨yr,mem_union_right _ yp⟩
  have cap := (rank_three_forks G gc hn r two odd A ai rk bad).1 y ym
  change (outward G r {y}).card≤2 at cap
  have all : ({u,v,w}:Finset V)⊆outward G r {y} :=
    insert_subset ((mem_outward_single G r u y).mpr py)
      (insert_subset ((mem_outward_single G r v y).mpr ⟨vz,dz⟩)
        (singleton_subset_iff.mpr ((mem_outward_single G r w y).mpr ⟨wk,dk⟩)))
  have large := card_le_card all
  rw [card_insert_of_not_mem (by simp [uv,uw]),card_pair vw] at large
  omega

#print axioms deep_triangle_bound
end Minimal180.HigherRank
