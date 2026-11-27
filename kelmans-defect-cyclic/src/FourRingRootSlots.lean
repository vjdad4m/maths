import FourRingReplicaCubic

open Finset SimpleGraph
namespace KelmansCactus.FourRingReplica
open FourRingBudget
noncomputable section
variable {U : Type*} [Fintype U] [DecidableEq U]
variable (A : SimpleGraph U) [DecidableRel A.Adj] (r : Bool→U)

private def remaining_neighbors (b : Bool) : Finset U :=
  (A.neighborFinset (r b)).erase (r (!b))

private theorem remaining_mem {u : U} {b : Bool} :
    u∈remaining_neighbors A r b ↔ u≠r (!b) ∧ A.Adj (r b) u := by
  rw [remaining_neighbors,mem_erase,mem_neighborFinset]

private theorem remaining_card (deg : ∀ v,A.degree v=3) (ab : A.Adj (r false) (r true))
    (b : Bool) : (remaining_neighbors A r b).card=2 := by
  have em : r (!b)∈A.neighborFinset (r b) := by
    rw [mem_neighborFinset]
    cases b
    · exact ab
    · exact ab.symm
  rw [remaining_neighbors,card_erase_of_mem em,card_neighborFinset_eq_degree,deg]

private theorem remaining_survives (b : Bool) (v : ↥(remaining_neighbors A r b)) :
    v.val≠r false ∧ v.val≠r true := by
  have m := (remaining_mem A r).mp v.property
  cases b
  · exact ⟨m.2.ne.symm,m.1⟩
  · exact ⟨m.1,m.2.ne.symm⟩

/-- Any edge whose two ends have no common neighbor provides the
required four distinct ports in a cubic graph. This includes
every edge in a triangle-free cubic graph. -/
def from_triangle_free_edge (deg : ∀ v,A.degree v=3) (ab : A.Adj (r false) (r true))
    (noCommon : ∀ u,A.Adj (r false) u → A.Adj (r true) u → False) : Layout A r := by
  classical
  let en (b : Bool) : Bool ≃ ↥(remaining_neighbors A r b) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_bool,Fintype.card_coe,remaining_card A r deg ab b])
  let P : Slot→Piece r := fun s=>⟨(en s.1 s.2).val,remaining_survives A r s.1 (en s.1 s.2)⟩
  have edge (s : Slot) : A.Adj (r s.1) (P s).val :=
    ((remaining_mem A r).mp (en s.1 s.2).property).2
  have inject : Function.Injective P := by
    rintro ⟨a,i⟩ ⟨b,j⟩ e
    have v : (P (a,i)).val=(P (b,j)).val := congrArg (fun v : Piece r=>v.val) e
    by_cases se : a=b
    · subst b
      exact Prod.ext rfl ((en a).injective (Subtype.ext v))
    · cases a <;> cases b
      · exact (se rfl).elim
      · exact (noCommon _ (edge (false,i)) (v.symm ▸ edge (true,j))).elim
      · exact (noCommon _ (edge (false,j)) (v ▸ edge (true,i))).elim
      · exact (se rfl).elim
  refine ⟨ab,⟨P,inject⟩,edge,?_⟩
  intro b v hv
  have outside : v.val≠r (!b) := by
    cases b
    · exact v.property.2
    · exact v.property.1
  let inN : ↥(remaining_neighbors A r b) := ⟨v.val,(remaining_mem A r).mpr ⟨outside,hv⟩⟩
  obtain ⟨j,e⟩ := (en b).surjective inN
  exact ⟨j,Subtype.ext (congrArg (fun u : ↥(remaining_neighbors A r b)=>u.val) e)⟩

#print axioms from_triangle_free_edge
end
end KelmansCactus.FourRingReplica
