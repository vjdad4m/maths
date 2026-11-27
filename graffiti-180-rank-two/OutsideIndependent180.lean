import BothArmTree180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In any failed deficit-two block the vertices outside both marks are
independent, including in the residual case of two marked root neighbors. -/
theorem outside_independent {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) :
    let P := parity G r odd
    Indep G (univ\(A∪P)) := by
  classical
  intro P
  let D := (A∪P)\(A∩P)
  let U := eligible A P r
  obtain ⟨t,td,w,tw,nw⟩ := free_attachment h
  let I := A∩P
  have impossible (a b : V) (aa : a∉A∪P) (bb : b∉A∪P) (aw : a≠w) (ab : G.Adj a b) : False := by
    have noD {i : V} (out : i∉A∪P) : i∉D := fun m => out (mem_sdiff.mp m).1
    have noI {i : V} (out : i∉A∪P) : i∉I := fun m => out (mem_union_left _ (mem_inter.mp m).1)
    obtain ⟨M,mg,tree,root,edge,⟨v,vd,vl⟩,p,d,step⟩ := both_arm_tree h td (noD nw) tw (noD aa) (noD bb) aw ab
    have same : ((A∪P)∩leaves M)=(U∩leaves M) := by
      ext z
      constructor
      · intro m
        obtain ⟨k,l⟩ := mem_inter.mp m
        exact mem_inter.mpr ⟨eligible_iff.mpr ⟨mem_union.mp k,Or.inl (fun eq => root (eq ▸ l))⟩,l⟩
      · intro m
        obtain ⟨k,l⟩ := mem_inter.mp m
        exact mem_inter.mpr ⟨mem_union.mpr (eligible_iff.mp k).1,l⟩
    have iu : I⊆A∪P := inter_subset_left.trans subset_union_left
    have du : D⊆A∪P := sdiff_subset
    have dis : Disjoint I D := disjoint_left.mpr fun _ a b => (mem_sdiff.mp b).2 a
    have ind : Indep M I := fun i im j jm ne e => h.independent i (mem_inter.mp im).1 j (mem_inter.mp jm).1 ne (mg e)
    have lower := count_spine M tree (by have := h.order; omega) I D (A∪P) ind iu du dis
      (noI aa) (noI bb) (noD aa) (noD bb) (noI nw) edge ⟨v,vd,vl⟩ p d step
    rw [same] at lower
    have upper : (U∩leaves M).card≤weightedLeaves G U := le_sup (f:=fun K => (U∩leaves K).card)
      (mem_filter.mpr ⟨mem_univ _,mg,tree⟩)
    have bad := h.bad
    change weightedLeaves G U+bipartiteNum G<1+A.card+P.card at bad
    have rk := h.rank
    have ci := card_union_add_card_inter A P
    have ii : I⊆A∪P := inter_subset_left.trans subset_union_left
    have cd := card_sdiff_add_card_eq_card ii
    change D.card+I.card=(A∪P).card at cd
    change (A∪P).card+I.card=A.card+P.card at ci
    omega
  intro i im j jm ne e
  by_cases iw : i=w
  · exact impossible j i (mem_sdiff.mp jm).2 (mem_sdiff.mp im).2 (by intro eq; exact ne (iw.trans eq.symm)) e.symm
  · exact impossible i j (mem_sdiff.mp im).2 (mem_sdiff.mp jm).2 iw e


#print axioms outside_independent
end Minimal180.RootEar
