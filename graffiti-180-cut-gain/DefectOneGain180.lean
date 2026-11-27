import BranchLayer180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- One fully specified tight, rooted-sparse horizontal triangle transition
whose lower graph has a proper seam, with the root on the named near side. -/
structure TightCut (J : SimpleGraph V) (S T : Finset V) (x y w : V) (r : ↥S)
    (odd : Bool) (A : Finset V) : Prop where
  connected : J.Connected
  order : 3<Fintype.card V
  split : Split J w S T
  nearTip : x∈S
  outsideFar : x∉T
  farTip : y∈T
  outsideNear : y∉S
  distinct : x≠y
  absent : ¬J.Adj x y
  leftSpoke : J.Adj x w
  rightSpoke : J.Adj w y
  block : NoCut (J⊔edge x y)
  sparse : SparseAt (J⊔edge x y) r.val
  horizontal : (J⊔edge x y).dist x r.val=(J⊔edge x y).dist y r.val
  independent : Indep (J⊔edge x y) A
  rank : bipartiteNum J=bipartiteNum (J⊔edge x y)+1
  tight : let P := parity (J⊔edge x y) r.val odd
          weightedLeaves J (eligible A P r.val)+bipartiteNum J=1+A.card+P.card

namespace TightCut
variable {J : SimpleGraph V} {S T : Finset V} {x y w : V} {r : ↥S} {odd : Bool} {A : Finset V}
variable (h : TightCut J S T x y w r odd A)
open Classical
include h

theorem layers_eq : parity J r.val odd=(parity (J⊔edge x y) r.val odd) := by
  have d := (seam_layers h.connected h.split h.farTip h.rightSpoke h.absent r h.horizontal).1
  ext i
  simp only [mem_parity,d]

theorem confined_gain (inc : A⊆(parity (J⊔edge x y) r.val odd)) : weightedLeaves J (eligible A (parity (J⊔edge x y) r.val odd) r.val)<weightedLeaves (J⊔edge x y) (eligible A (parity (J⊔edge x y) r.val odd) r.val) := by
  classical
  have bound := confined_parity (J⊔edge x y) (h.connected.mono le_sup_left) (by have := h.order; omega) r.val odd.toNat
    A h.independent inc
  have cap : markedBip (J⊔edge x y) (A∩(parity (J⊔edge x y) r.val odd))≤bipartiteNum (J⊔edge x y) := by
    apply Finset.sup_le
    exact fun _ k => size_bip (J⊔edge x y) (mem_filter.mp k).2.2
  change 1+A.card+((parity (J⊔edge x y) r.val odd)).card≤weightedLeaves (J⊔edge x y) (eligible A (parity (J⊔edge x y) r.val odd) r.val)+markedBip (J⊔edge x y) (A∩(parity (J⊔edge x y) r.val odd)) at bound
  have b := h.rank
  have t := h.tight
  change weightedLeaves J (eligible A (parity (J⊔edge x y) r.val odd) r.val)+bipartiteNum J=1+A.card+((parity (J⊔edge x y) r.val odd)).card at t
  omega

/-- For unequal marks and one lower bipartization deletion the whole
symmetric difference induces a tree in a branching layer tree. In
particular the seam is completely unmarked. -/
theorem defect_one_forest (rank1 : bipartiteNum J+1=Fintype.card V) (ne : A≠(parity (J⊔edge x y) r.val odd)) :
    w∉A∪(parity (J⊔edge x y) r.val odd) ∧ ∃ M≤J, M.IsTree ∧ M.Adj x w ∧ M.Adj y w ∧
      let D := (A∪(parity (J⊔edge x y) r.val odd))\(A∩(parity (J⊔edge x y) r.val odd))
      (M.edgeFinset∩D.sym2).card+1=D.card := by
  classical
  obtain ⟨M,mj,tr,root,mx,my,⟨z,mz,zx,zy⟩,cross⟩ :=
    cut_layer_tree h.connected h.order h.split h.nearTip h.outsideFar h.farTip h.outsideNear
      h.absent h.leftSpoke h.rightSpoke r h.block h.sparse h.horizontal odd
  have op {i j : V} (e : M.Adj i j) : i∈(parity (J⊔edge x y) r.val odd) ↔ j∉(parity (J⊔edge x y) r.val odd) := h.layers_eq ▸ cross e
  have ai : Indep J A := fun a ha b hb ab e => h.independent a ha b hb ab (Or.inl e)
  obtain ⟨_,degree,forest⟩ := one_defect_rigid J M tr mj (by have := h.order; omega) r.val root A (parity (J⊔edge x y) r.val odd) ai ne op rank1 h.tight
  refine ⟨?_,M,mj,tr,mx,my,forest⟩
  intro wm
  have inc : ({z,x,y}:Finset V)⊆M.neighborFinset w := by
    apply insert_subset ((M.mem_neighborFinset ..).mpr mz)
    exact insert_subset ((M.mem_neighborFinset ..).mpr mx.symm) (singleton_subset_iff.mpr ((M.mem_neighborFinset ..).mpr my.symm))
  have c := card_le_card inc
  rw [card_insert_of_not_mem (by simp [zx,zy]),card_pair h.distinct,card_neighborFinset_eq_degree] at c
  have small := degree w wm
  omega

/-- Exact decision at lower deficit one under the full cut hypotheses.
A single mark on the seam cannot occur at this equality. -/
theorem defect_one_gain_iff (rank1 : bipartiteNum J+1=Fintype.card V) :
    (weightedLeaves J (eligible A (parity (J⊔edge x y) r.val odd) r.val)<weightedLeaves (J⊔edge x y) (eligible A (parity (J⊔edge x y) r.val odd) r.val) ↔ w∈A∪(parity (J⊔edge x y) r.val odd)) ∧
    (w∈A∪(parity (J⊔edge x y) r.val odd) → A=(parity (J⊔edge x y) r.val odd)) := by
  have collapse (wm : w∈A∪(parity (J⊔edge x y) r.val odd)) : A=(parity (J⊔edge x y) r.val odd) := Classical.byContradiction (fun ne => (h.defect_one_forest rank1 ne).1 wm)
  refine ⟨⟨?_,fun wm => h.confined_gain (collapse wm).le⟩,collapse⟩
  intro gain
  have wu := (gain_preserves_pruned h.connected (by have := h.order; omega) h.distinct h.absent
    h.leftSpoke h.rightSpoke (eligible A (parity (J⊔edge x y) r.val odd) r.val) gain).1
  exact mem_union.mpr (eligible_iff.mp wu).1

/-- A real tight cut with an unmarked seam, at any deficit, would
give an ordinary connected counterexample within the existing lift bound. -/
theorem unmarked_counterexample (no : w∉A∪(parity (J⊔edge x y) r.val odd)) :
    counterexampleAtMost.{u} (4*Fintype.card V-1) := by
  have ng (g : weightedLeaves J (eligible A (parity (J⊔edge x y) r.val odd) r.val) < weightedLeaves (J⊔edge x y) (eligible A (parity (J⊔edge x y) r.val odd) r.val)) : False := by
    have wu := (gain_preserves_pruned h.connected (by have := h.order; omega) h.distinct h.absent
      h.leftSpoke h.rightSpoke (eligible A (parity (J⊔edge x y) r.val odd) r.val) g).1
    exact no (mem_union.mpr (eligible_iff.mp wu).1)
  apply of_failed_local (J⊔edge x y) (h.connected.mono le_sup_left) (by have := h.order; omega) r.val odd
  intro good
  have ok := good A h.independent
  have eq := h.tight
  have b := h.rank
  apply ng
  change 1+A.card+((parity (J⊔edge x y) r.val odd)).card≤weightedLeaves (J⊔edge x y) (eligible A (parity (J⊔edge x y) r.val odd) r.val)+bipartiteNum (J⊔edge x y) at ok
  change weightedLeaves J (eligible A (parity (J⊔edge x y) r.val odd) r.val)+bipartiteNum J=1+A.card+((parity (J⊔edge x y) r.val odd)).card at eq
  omega

#print axioms confined_gain
#print axioms defect_one_forest
#print axioms defect_one_gain_iff
#print axioms unmarked_counterexample
end TightCut
end Minimal180.CutGain
