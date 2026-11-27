import SpineColor180
import Unmarked180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every tight horizontal cut-triangle transition whose lower
bipartization deficit is one gains an eligible leaf, at all chord depths
and for every actual marking. -/
theorem deficit_one_cut_gain {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (h : TightCut J S T x y w r odd A)
    (one : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let U := eligible A (parity G r.val odd) r.val
    weightedLeaves J U<weightedLeaves G U := by
  classical
  intro G U
  apply Classical.byContradiction
  intro ng
  let P := parity G r.val odd
  let D := (A∪P)\(A∩P)
  obtain ⟨_,_,t,ends,_,_,sp⟩ := failed_spine h one ng
  change Spine J r.val D t at sp
  obtain ⟨s,sd,ts⟩ := sp.first_step
  have broken := spine_bridge h one t s sp sd ts
  have free := unmarked_independent h one ng
  have op : parity J r.val odd=P := h.layers_eq
  have ai : Indep J A := fun i ia j ja ne e => h.independent i ia j ja ne (Or.inl e)
  have paint := spine_color J h.connected r.val odd A ai t s
  rw [op] at paint
  have col := paint sp sd ts broken (fun i im j jm ne e => free i im j jm ne (Or.inl e))
  have size := card_erase_add_one (mem_univ t)
  rw [card_univ] at size
  have rk : bipartiteNum J=bipartiteNum G+1 := h.rank
  have top : MaxSet J (univ.erase t) := ⟨col,by omega⟩
  have pins := locked_seam h.split h.nearTip h.outsideNear h.distinct (by change bipartiteNum G<bipartiteNum J; omega) top
  have either : t=x ∨ t=y := by simpa only [mem_insert,mem_singleton] using ends
  rcases either with rfl|rfl
  · exact (mem_erase.mp pins.1).1 rfl
  · exact (mem_erase.mp pins.2.2).1 rfl

#print axioms deficit_one_cut_gain
end Minimal180.DescentOne
