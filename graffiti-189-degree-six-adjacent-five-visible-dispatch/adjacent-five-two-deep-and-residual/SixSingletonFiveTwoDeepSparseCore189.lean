import SixSingletonFiveTwoDeepOneLow189
import SixRootAvoid189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 p5 from SixSingletonFiveShallowRoute189
open private erase_internal_deg from SixSingletonDarkOre189
open FiveAdjacent (terminal_route_on_of_local_ore)
open private dark_core_six from SixSingletonFiveTwoDeepBase189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem deep_shape_two {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
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

private theorem deep_strict_cover {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T) :
    S=insert T (L∪R) := by
  have n : T∉L∪R := fun h=>(mem_union.mp h).elim F.deepL F.deepR
  have sub : insert T (L∪R)⊆S := insert_subset F.deepS (union_subset F.left_sub F.right_sub)
  apply (eq_of_subset_of_card_le sub ?_).symm
  rw [dark_core_six F,card_insert_of_not_mem n,F.strict5]

private theorem deep_every_balance_dark_hit {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
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

theorem deep_root_through_strict_core {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
    {z w t : V} (zm : z∈D\S) (wm : w∈D\S) (zw : z≠w) (tm : t∈S) :
    ∃ h∈L∪R,RouteOn G S h t := by
  have s6 := dark_core_six F
  have full := deep_strict_cover F
  have eq := (deep_shape_two F zm wm zw).2
  have d (u : V) (um : u∈S) : 3≤(inside G S u).card := by
    have q := F.dark5 u um
    have p := erase_internal_deg (G:=G) D z u
    have r := erase_internal_deg (G:=G) (D.erase z) w u
    change S=(D.erase z).erase w at eq
    rw [←eq] at r
    omega
  obtain ⟨u,um,p⟩ := rooted_side_route (G:=G) S tm (fun v vm w wm _ _=>by
    have kv := d v vm
    have kw := d w wm
    omega)
  have U := um
  rw [full,mem_insert] at U
  rcases U with ue|uc
  · subst u
    obtain ⟨v,vm,ne,q⟩ := route_avoid_free_end S p.reverse (by have z := d T um; omega)
    rw [full,mem_insert] at vm
    exact ⟨v,vm.resolve_left ne,q.reverse⟩
  exact ⟨_,uc,p⟩

#print axioms deep_root_through_strict_core
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
