import SmallOrderFour189
import Batteries.Tactic.OpenPrivate

namespace Graffiti189LongestPath.OmittedSaturation
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

open private pin_data pin_pos pin_of_neighbor_mem cardinal_flankVertices from SmallOrderFour189
open private boundary_except_pins_two from OneSlack189
open private mem_omittedStar mem_external from Rigidity189

/-- If the path flanks exhaust a vertex's distance-two neighborhood, its
closed omitted neighborhood has no external neighbors other than its own pins. -/
theorem boundary_subset_pins_of_saturated_flanks
    (hc : G.Connected) {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (sat : DistanceTwo G x⊆FlankVertices p x) :
    External G (OmittedStar p x)⊆PinVertices p x := by
  intro z hz
  by_contra no
  have zd := boundary_except_pins_two hc hp xo (mem_sdiff.mpr ⟨hz,no⟩)
  exact (mem_sdiff.mp (flanks_outside_boundary hc hp xo (sat zd))).2 hz

/-- Saturation by flank vertices forces universality in the omitted component.
Every path contact of that component is a pin of the saturated vertex. -/
theorem universal_and_contacts_of_saturated_flanks
    (hc : G.Connected) {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (hx : x∈H.vertices)
    (sat : DistanceTwo G x⊆FlankVertices p x) :
    (∀ z∈H.vertices,z≠x → G.Adj x z) ∧
    (∀ z∈H.vertices,Pins p z⊆Pins p x) := by
  have xo := H.off x hx
  have control := boundary_subset_pins_of_saturated_flanks hc hp xo sat
  have starClosed {u v : V} (q : G.Walk u v)
      (vend : v∈OmittedStar p x) (off : ∀ z∈q.support,z∉p.support) :
      u∈OmittedStar p x := by
    induction q with
    | nil => exact vend
    | @cons u w v uw q ih =>
      have wm := ih vend (fun z hz => off z (by simp [hz]))
      by_cases um : u∈OmittedStar p x
      · exact um
      have ub : u∈External G (OmittedStar p x) :=
        mem_external.mpr ⟨um,w,wm,uw.symm⟩
      obtain ⟨i,_,rfl⟩ := mem_image.mp (control ub)
      exact (off _ (by simp) (p.getVert_mem_support i)).elim
  have allStar (z : V) (zh : z∈H.vertices) : z∈OmittedStar p x := by
    obtain ⟨q,_,inside⟩ := H.joined z zh x hx
    exact starClosed q (mem_omittedStar.mpr ⟨xo,.inl rfl⟩)
      (fun y hy => H.off y (inside y hy))
  refine ⟨fun z zh ne => (mem_omittedStar.mp (allStar z zh)).2.resolve_left ne,?_⟩
  intro z zh k hk
  have outside : p.getVert k∉OmittedStar p x :=
    fun h => (mem_omittedStar.mp h).1 (p.getVert_mem_support k)
  have kb := mem_external.mpr ⟨outside,z,allStar z zh,(pin_data hk).2⟩
  obtain ⟨i,hi,eq⟩ := mem_image.mp (control kb)
  have same := hp.1.getVert_injOn (pin_data hi).1.le (pin_data hk).1.le eq
  exact same ▸ hi

/-- In the saturation case the omitted component is exactly the omitted star,
and its path contacts are exactly the pin vertices of the center. -/
theorem component_eq_star_and_contact_eq_of_saturated_flanks
    (hc : G.Connected) {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (hx : x∈H.vertices)
    (sat : DistanceTwo G x⊆FlankVertices p x) :
    H.vertices=OmittedStar p x ∧ componentPins H=PinVertices p x := by
  obtain ⟨allAdj,allPins⟩ := universal_and_contacts_of_saturated_flanks hc hp H hx sat
  constructor
  · ext z
    constructor
    · intro hz
      refine mem_omittedStar.mpr ⟨H.off z hz,?_⟩
      by_cases he : z=x
      · exact .inl he
      · exact .inr (allAdj z hz he)
    · intro hz
      obtain ⟨off,he|adj⟩ := mem_omittedStar.mp hz
      · exact he.symm ▸ hx
      · by_contra no
        exact off (H.closed x hx z no adj)
  · ext z
    constructor
    · intro hz
      obtain ⟨on,w,hw,adj⟩ := mem_filter.mp hz
      obtain ⟨k,hk,eq⟩ := pin_of_neighbor_mem hp (H.off w hw) (List.mem_toFinset.mp on) adj
      exact mem_image.mpr ⟨k,allPins w hw hk,eq⟩
    · intro hz
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
      exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support k),x,hx,(pin_data hk).2⟩

/-- Exact two-pin form, with no path length or component order restriction.
Note that the separation and the local distance-two cap are hypotheses. -/
theorem universal_and_two_contacts
    (hc : G.Connected) {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (hx : x∈H.vertices)
    {i j : ℕ} (pins : Pins p x=({i,j}:Finset ℕ)) (gap : i+3≤j)
    (cap : (DistanceTwo G x).card≤4) :
    (∀ z∈H.vertices,z≠x → G.Adj x z) ∧
    (∀ z∈H.vertices,Pins p z⊆({i,j}:Finset ℕ)) := by
  have xo := H.off x hx
  have hi : i∈Pins p x := by rw [pins]; simp
  have ip := pin_pos hp xo hi
  have eq : FlankIndices p x=({i-1,i+1,j-1,j+1}:Finset ℕ) := by
    ext k
    simp [FlankIndices,pins,or_assoc,or_left_comm,or_comm]
  have q1 : i-1∉({i+1,j-1,j+1}:Finset ℕ) := by
    simp only [mem_insert,mem_singleton]
    omega
  have q2 : i+1∉({j-1,j+1}:Finset ℕ) := by
    simp only [mem_insert,mem_singleton]
    omega
  have q3 : j-1∉({j+1}:Finset ℕ) := by
    simp only [mem_singleton]
    omega
  have four : (FlankVertices p x).card=4 := by
    rw [cardinal_flankVertices hp,eq,card_insert_of_not_mem q1,
      card_insert_of_not_mem q2,card_insert_of_not_mem q3,card_singleton]
  have sub : FlankVertices p x⊆DistanceTwo G x :=
    fun z hz => (mem_sdiff.mp (flanks_outside_boundary hc hp xo hz)).1
  have eqd := eq_of_subset_of_card_le sub (by rw [four]; exact cap)
  have sat : DistanceTwo G x⊆FlankVertices p x := by rw [eqd]
  simpa only [pins] using universal_and_contacts_of_saturated_flanks hc hp H hx sat

#print axioms boundary_subset_pins_of_saturated_flanks
#print axioms universal_and_contacts_of_saturated_flanks
#print axioms component_eq_star_and_contact_eq_of_saturated_flanks
#print axioms universal_and_two_contacts
end Graffiti189LongestPath.OmittedSaturation
