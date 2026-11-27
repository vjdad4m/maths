import PairedOff189
import PairedOnClose189

namespace Graffiti189LongestPath.OneSlack
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option maxHeartbeats 1800000

omit [Fintype V] in
private theorem pins_card_same {a b x : V} {p : G.Walk a b} (hp : IsLongest p) :
    (PinVertices p x).card=(Pins p x).card := by
  apply card_image_iff.mpr
  intro i hi j hj e
  exact hp.1.getVert_injOn (mem_range.mp (mem_filter.mp hi).1).le
    (mem_range.mp (mem_filter.mp hj).1).le e

private theorem pins_boundary_subset {a b x : V} {p : G.Walk a b} (hx : x∉p.support) :
    PinVertices p x ⊆ External G (OmittedStar p x) := by
  intro y hy
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
  have xA : x∈OmittedStar p x := by simp [OmittedStar,hx]
  have m : p.getVert i ∉ OmittedStar p x := by simp [OmittedStar,p.getVert_mem_support]
  exact mem_filter.mpr ⟨mem_univ _,m,x,xA,(mem_filter.mp hi).2⟩

/-- At d=4, on an edge-optimal longest path with high endpoint degrees,
no omitted vertex has a pair of pins at gap two. -/
theorem no_paired_pins_at_four (hc : G.Connected)
    (bound : ∀ v, (EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (a4 : 4≤G.degree a) (b4 : 4≤G.degree b)
    {x : V} (hx : x∉p.support) : PairedPins p x=∅ := by
  classical
  have cap (v : V) : (DistanceTwo G v).card≤2+2 := distanceTwo_le_of_even 4 v (bound v)
  apply eq_empty_iff_forall_not_mem.mpr
  intro j hj
  have offNbr : ∃ u∉p.support, G.Adj x u := by
    by_contra h
    have isolated (u : V) (e : G.Adj x u) : u∈p.support := by
      by_contra no
      exact h ⟨u,no,e⟩
    have empty := singleton_has_no_gap_two_pairs hc 4 cap degree hp hx isolated
    rw [empty] at hj
    exact not_mem_empty _ hj
  obtain ⟨u,hu,xu⟩ := offNbr
  obtain ⟨m,hm,hm₂⟩ : ∃ m, m∈Pins p x ∧ m+2∈Pins p x := by
    obtain ⟨h,l,hl,eq|eq⟩ := mem_filter.mp hj
    · exact ⟨l,hl,eq.symm ▸ h⟩
    · exact ⟨j,h,eq.symm ▸ hl⟩
  have size : (Pins p x).card=2 := by
    have small := at_most_two_pins_with_omitted_neighbor hc 2 hp.1 hx (cap x) conn hu xu
    have sub : ({m,m+2}:Finset ℕ) ⊆ Pins p x := by
      intro q h
      rcases mem_insert.mp h with rfl|h
      · exact hm
      · exact (mem_singleton.mp h).symm ▸ hm₂
    have big := card_le_card sub
    have ne : m≠m+2 := by omega
    simp [ne] at big
    omega
  have bi : m∈PairedPins p x := mem_filter.mpr ⟨hm,m+2,hm₂,Or.inr rfl⟩
  have sat := double_porter_saturated_one_slack hc 2 hp.1 hx size (bound x) conn hu xu
  let B := External G (OmittedStar p x)
  let F := PinVertices p x
  have bcard : B.card=3 := by
    rcases sat.2.2 with eq|eq
    · rw [eq.1] at bi
      exact (not_mem_empty _ bi).elim
    · exact eq.2
  have fcard : F.card=2 := (pins_card_same hp.1).trans size
  have c := card_sdiff_add_card_eq_card (pins_boundary_subset hx)
  change (B \ F).card + F.card=B.card at c
  obtain ⟨t,ht⟩ := card_pos.mp (show 0<(B \ F).card by omega)
  obtain ⟨tb,tf⟩ := mem_sdiff.mp ht
  by_cases tp : t∈p.support
  · exact paired_on_impossible hc bound conn hp.1 a4 b4 hx hm hm₂ size hu xu tp tb tf
  · have tc := (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hp tp).1
    have upper := PairedOff.path_order_le_ten hc bound conn hp.1 hx hm hm₂ size hu xu tp tb tc
    have lower := MultiRotation.path_order_ge_eleven hc hp.1 a4 b4 hx hm hm₂ size (cap x) (by omega : 3≤B.card)
    omega

#print axioms no_paired_pins_at_four

/-- If no spanning path exists, an edge-optimal longest path may be
chosen with both endpoints above the designated degree threshold. -/
theorem exists_edge_optimal_with_high_ends (hc : G.Connected) (k d : ℕ) (k₂ : 2≤k)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u≠v → d≤G.degree u ∨ d≤G.degree v)
    (fail : ¬ ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v,v∈p.support) :
    ∃ (a b : V) (p : G.Walk a b), EdgeOptimal p ∧ d≤G.degree a ∧ d≤G.degree b := by
  classical
  obtain ⟨a,b,p,hp⟩ := exists_edgeOptimal hc
  obtain ⟨x,hx⟩ : ∃ x, x∉p.support := not_forall.mp (fun h => fail ⟨a,b,p,hp.1.1,h⟩)
  obtain ⟨u,v,q,hq,same,hu,hv⟩ := MultiRotation.rotate_to_two_high_endpoints_general hc k k₂ d
    conn degree hp.1 hx
  have eq : OmittedEdges p = OmittedEdges q := by
    ext yz
    simp only [OmittedEdges,mem_filter,mem_univ,true_and,same yz.1,same yz.2]
  refine ⟨u,v,q,⟨hq,?_⟩,hu,hv⟩
  intro s t r hr
  rw [←eq]
  exact hp.2 s t r hr

/-- After choosing the tie breaker and high endpoints, any two distinct
pins of an omitted component are separated by at least three steps. -/
theorem component_pins_spaced_four (hc : G.Connected)
    (bound : ∀ v, (EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (a4 : 4≤G.degree a) (b4 : 4≤G.degree b)
    (H : OmittedComponent p) {x y : V} (hx : x∈H.vertices) (hy : y∈H.vertices)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p y) (ij : i<j) :
    i+3≤j := by
  by_cases e : x=y
  · subst y
    by_contra! small
    have alt : j=i+1 ∨ j=i+2 := by omega
    rcases alt with eq|eq
    · have h : p.getVert j∈FlankVertices p x := by
        apply mem_image.mpr
        refine ⟨j,mem_union.mpr (Or.inr (mem_image.mpr ⟨i,hi,eq.symm⟩)),rfl⟩
      have fl := flanks_outside_boundary hc hp.1 (H.off x hx) h
      exact (mem_sdiff.mp fl).2
        (pins_boundary_subset (H.off x hx) (mem_image.mpr ⟨j,hj,rfl⟩))
    · have h : i∈PairedPins p x := mem_filter.mpr ⟨hi,j,hj,Or.inr eq.symm⟩
      rw [no_paired_pins_at_four hc bound conn degree hp a4 b4 (H.off x hx)] at h
      exact not_mem_empty _ h
  · obtain ⟨q,hq,hqs⟩ := H.joined x hx y hy
    have pos : 0<q.length := by cases q with
      | nil => exact (e rfl).elim
      | cons e q => simp
    exact gap_three_of_linked_pins hp.1 hi hj ij q hq pos (fun z hz => H.off z (hqs z hz))

#print axioms exists_edge_optimal_with_high_ends
#print axioms component_pins_spaced_four
end Graffiti189LongestPath.OneSlack
