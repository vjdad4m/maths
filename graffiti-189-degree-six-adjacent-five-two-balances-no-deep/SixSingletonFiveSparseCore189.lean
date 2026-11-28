import SixSingletonFiveOneLow189
import SixRootedSideRoute189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 p5 from SixSingletonFiveShallowRoute189
open private erase_internal_deg from SixSingletonDarkOre189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem shape_two {L R S : Finset V} (F : ProfileTwo G L R S)
    {z w : V} (zm : z∈D\S) (wm : w∈D\S) (zw : z≠w) :
    D\S={z,w} ∧ S=(D.erase z).erase w := by
  have h : ({z,w}:Finset V)⊆D\S := insert_subset zm (singleton_subset_iff.mpr wm)
  have shape := (eq_of_subset_of_card_le h (by rw [F.balance,card_insert_of_not_mem (by simpa using zw),card_singleton])).symm
  refine ⟨shape,?_⟩
  ext i
  simp only [mem_erase]
  constructor
  · intro im
    exact ⟨fun e=>(mem_sdiff.mp wm).2 (e ▸ im),fun e=>(mem_sdiff.mp zm).2 (e ▸ im),F.core_sub im⟩
  · rintro ⟨iw,iz,id⟩
    by_contra ns
    have mm : i∈D\S := mem_sdiff.mpr ⟨id,ns⟩
    rw [shape,mem_insert,mem_singleton] at mm
    exact mm.elim iz iw

private theorem strict_cover {L R S : Finset V} (F : ProfileTwo G L R S) :
    S.card=6 ∧ L∪R=S := by
  have h := card_sdiff F.core_sub
  have k := card_le_card F.core_sub
  rw [F.balance,d8] at h
  rw [d8] at k
  have s6 : S.card=6 := by omega
  refine ⟨s6,eq_of_subset_of_card_le (union_subset F.left_sub F.right_sub) ?_⟩
  rw [s6]
  exact F.strict6

private theorem every_balance_dark_hit {L R S : Finset V} (F : ProfileTwo G L R S)
    {z : V} (zd : z∈D) : ∃ t∈D,G.Adj t z := by
  by_contra no
  have sub : G.neighborFinset z⊆P := by
    intro t tm
    have j := (mem_neighborFinset _ _ _).mp tm
    exact (mem_union.mp (F.darkBounds z zd t j)).resolve_left (fun d=>no ⟨t,d,j.symm⟩)
  have h := card_le_card sub
  rw [card_neighborFinset_eq_degree,p5] at h
  have k := F.darkHigh z zd
  omega

theorem root_through_strict_core {L R S : Finset V} (F : ProfileTwo G L R S)
    {z w t : V} (zm : z∈D\S) (wm : w∈D\S) (zw : z≠w) (tm : t∈S) :
    ∃ h∈L∪R,RouteOn G S h t := by
  have ⟨s6,full⟩ := strict_cover F
  rw [full]
  apply rooted_side_route S tm
  have eq := (shape_two F zm wm zw).2
  have d (u : V) (um : u∈S) : 3≤(inside G S u).card := by
    have q := F.dark5 u um
    have p := erase_internal_deg (G:=G) D z u
    have r := erase_internal_deg (G:=G) (D.erase z) w u
    change S=(D.erase z).erase w at eq
    rw [←eq] at r
    omega
  intro u um v vm _ _
  have ku := d u um
  have kv := d v vm
  omega

#print axioms root_through_strict_core
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
