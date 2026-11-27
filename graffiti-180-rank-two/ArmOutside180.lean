import ArmTree180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A failed single-arm marking makes the set missed by both marks independent.
Both edges at the root survive the exchange even though the root is in D. -/
theorem arm_outside {G : SimpleGraph V} {r w : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) (rw : G.Adj r w) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    w∉D → Indep G (univ\(A∪P)) := by
  classical
  intro P D wd
  let U := eligible A P r
  obtain ⟨nw,t,rt,sp⟩ := single_arm h rw wd
  change Spine G r (D.erase r) t at sp
  have ⟨tr,td⟩ := mem_erase.mp sp.tip
  have rd : r∈D := h.root_disagreement
  have rtArc : Arc G r r t := by
    have dt := dist_eq_one_iff_adj.mpr rt.symm
    refine ⟨rt,by rw [dist_self,zero_add,dt],fun z _ dz => h.connected.dist_eq_zero_iff.mp (by omega)⟩
  have prior (i : V) (id : i∈D) (ir : i≠r) : ∃ q∈D, Arc G r q i := by
    by_cases it : i=t
    · exact ⟨r,rd,it ▸ rtArc⟩
    · obtain ⟨q,qm,qi⟩ := sp.prior i (mem_erase.mpr ⟨ir,id⟩) it
      exact ⟨q,mem_of_mem_erase qm,qi⟩
  obtain ⟨lastV,lm,_,maximal⟩ := sp.last_step
  obtain ⟨endR,endD⟩ := mem_erase.mp lm
  have last (i : V) (id : i∈D) : G.dist i r≤G.dist lastV r := by
    by_cases ir : i=r
    · rw [ir,dist_self]; exact Nat.zero_le _
    · exact maximal i (mem_erase.mpr ⟨ir,id⟩)
  let I := A∩P
  have impossible (a b : V) (aa : a∉A∪P) (bb : b∉A∪P) (aw : a≠w) (ab : G.Adj a b) : False := by
    have noD {i : V} (out : i∉A∪P) : i∉D := fun m => out (mem_sdiff.mp m).1
    have noI {i : V} (out : i∉A∪P) : i∉I := fun m => out (mem_union_left _ (mem_inter.mp m).1)
    obtain ⟨M,mg,tree,mrw,keep,edge,⟨v,vd,_,vl⟩,p,d,step⟩ := arm_tree h.block (by have := h.order; omega)
      rd prior endD endR last (noD nw) rw (noD aa) (noD bb) aw ab
    have root : r∉leaves M := fun l => (noD nw) ((leaf_unique M l mrw (keep t td tr r rtArc).symm).symm ▸ td)
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


#print axioms arm_outside
end Minimal180.RootEar
