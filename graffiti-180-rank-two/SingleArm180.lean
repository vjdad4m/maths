import PortLayers180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a failure with a parity-only root, more vertices carry the parity
mark than carry the independent mark. -/
theorem parity_surplus {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) (rp : r∈parity G r odd) : A.card<(parity G r odd).card := by
  classical
  let P := parity G r odd
  have ra : r∉A := fun a => (mem_sdiff.mp h.root_disagreement).2 (mem_inter.mpr ⟨a,rp⟩)
  have au : A⊆eligible A P r := fun i ia =>
    eligible_iff.mpr ⟨Or.inl ia,Or.inl (fun eq => ra (eq ▸ ia))⟩
  have bound := weighted177 G h.connected (by have := h.order; omega) _ A h.independent au
  have bad := h.bad
  change weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card at bad
  change A.card<P.card
  omega

/-- If a root neighbor lies outside the disagreement, the other neighbor
starts a unique descending spine. Its first edge from the root is followed
by at least one more edge. -/
theorem single_arm {G : SimpleGraph V} {r w : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) (rw : G.Adj r w) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    w∉D → w∉A∪P ∧ ∃ t, G.Adj r t ∧ Spine G r (D.erase r) t := by
  classical
  intro P D out
  have rd : r∈D := h.root_disagreement
  have flip := (vertical_adj (r:=r) rw (by rw [dist_self,zero_add,dist_eq_one_iff_adj.mpr rw.symm]) odd).2
  change r∈P ↔ w∉P at flip
  have same : w∈A ↔ w∈P := by
    change w∉(A∪P)\(A∩P) at out
    simp only [mem_sdiff,mem_union,mem_inter] at out
    tauto
  have root : r∈P := by
    by_contra nr
    have ra := (mem_union.mp (mem_sdiff.mp rd).1).resolve_right nr
    have wp : w∈P := Classical.byContradiction (fun nw => nr (flip.mpr nw))
    exact h.independent r ra w (same.mpr wp) rw.ne rw
  have free : w∉A∪P := by have absent := flip.mp root; simp only [mem_union]; tauto
  have ra : r∉A := fun a => (mem_sdiff.mp rd).2 (mem_inter.mpr ⟨a,root⟩)
  let L (k : ℕ) := D.filter (fun v => G.dist v r=k)
  have wo : w∉L 1 := fun m => out (mem_filter.mp m).1
  have ins : insert w (L 1)⊆G.neighborFinset r := by
    apply insert_subset ((G.mem_neighborFinset ..).mpr rw)
    intro z m; exact (G.mem_neighborFinset ..).mpr (dist_eq_one_iff_adj.mp (mem_filter.mp m).2).symm
  have ct := card_le_card ins
  rw [card_insert_of_not_mem wo,card_neighborFinset_eq_degree,h.root_degree] at ct
  have uniq {i j : V} (id : i∈D) (jd : j∈D) (eq : G.dist i r=G.dist j r) : i=j := by
    cases layer : G.dist i r with
    | zero =>
      exact ((h.connected.dist_eq_zero_iff).mp layer).trans ((h.connected.dist_eq_zero_iff).mp (eq.symm.trans layer)).symm
    | succ k =>
      have cap := (width h).2.1 k
      change (L (k+1)).card≤(L 1).card at cap
      exact card_le_one_iff.mp (show (L (k+1)).card≤1 by omega)
        (mem_filter.mpr ⟨id,layer⟩) (mem_filter.mpr ⟨jd,eq.symm.trans layer⟩)
  obtain ⟨a,aa,ap⟩ := Finset.not_subset.mp h.not_confined
  change a∉P at ap
  have ar : a≠r := fun eq => ap (eq ▸ root)
  have ade : a∈D.erase r := mem_erase.mpr ⟨ar,mem_sdiff.mpr ⟨mem_union_left _ aa,fun m => ap (mem_inter.mp m).2⟩⟩
  obtain ⟨t,tm,least⟩ := exists_min_image (D.erase r) (fun v => G.dist v r) ⟨a,ade⟩
  obtain ⟨tr,td⟩ := mem_erase.mp tm
  obtain ⟨q,tq,step⟩ := Graffiti169.exists_predecessor G h.connected r t tr
  have qr : q=r := by
    apply Classical.byContradiction
    intro no
    have low := least q (mem_erase.mpr ⟨no,predecessor_closed h td tq step⟩)
    omega
  have rt : G.Adj r t := qr ▸ tq.symm
  have dt : G.dist t r=1 := dist_eq_one_iff_adj.mpr rt.symm
  have tp : t∉P := (vertical_adj (r:=r) rt (by simpa only [dist_self,zero_add] using dt) odd).2.mp root
  have ta : t∈A := (mem_union.mp (mem_sdiff.mp td).1).resolve_right tp
  have more : ((D.erase r).erase t).Nonempty := by
    apply Classical.byContradiction
    intro noMore
    have inc : P.erase r⊆A.erase t := by
      intro i m
      obtain ⟨ir,ip⟩ := mem_erase.mp m
      refine mem_erase.mpr ⟨fun it => tp (it ▸ ip),?_⟩
      apply Classical.byContradiction
      intro ia
      have im : i∈D := mem_sdiff.mpr ⟨mem_union_right _ ip,fun z => ia (mem_inter.mp z).1⟩
      exact noMore ⟨i,mem_erase.mpr ⟨fun it => tp (it ▸ ip),mem_erase.mpr ⟨ir,im⟩⟩⟩
    have cap := card_le_card inc
    have ca := card_erase_add_one ta
    have cp := card_erase_add_one root
    have gt := parity_surplus h root
    change A.card<P.card at gt
    omega
  refine ⟨free,t,rt,(by simp),tm,least,fun i im j jm eq => uniq (mem_of_mem_erase im) (mem_of_mem_erase jm) eq,?_,?_,more⟩
  · intro i im it
    obtain ⟨ir,id⟩ := mem_erase.mp im
    obtain ⟨p,ip,step⟩ := Graffiti169.exists_predecessor G h.connected r i ir
    have pd := predecessor_closed h id ip step
    have pr : p≠r := by intro eq; rw [eq,dist_self,zero_add] at step; exact it (uniq id td (step.trans dt.symm))
    refine ⟨p,mem_erase.mpr ⟨pr,pd⟩,ip.symm,step,?_⟩
    intro z zi dz
    exact uniq (predecessor_closed h id zi.symm dz) pd (by omega)
  · intro v m i j vi vj di dj
    exact h.outward (mem_sdiff.mp (mem_of_mem_erase m)).1 (mem_erase.mp m).1 vi vj di dj

#print axioms parity_surplus
#print axioms single_arm
end Minimal180.RootEar
