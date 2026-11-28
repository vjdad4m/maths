import SixThree19Extreme189

namespace Graffiti189LongestPath.SixThreeNineteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree length_ge_twelve)
open Graffiti189LongestPath.SixThreeEighteen
  (Omit mem_Omit omit_add_length high_filter_card not_length_twelve_of_three_active)
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem degree_covered_by_pins_and_omitted {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) : G.degree x≤(Pins p x).card+((Omit p).card-1) := by
  classical
  have sub : G.neighborFinset x⊆PinVertices p x∪(Omit p).erase x := by
    intro y ym
    have adj := (mem_neighborFinset _ _ _).mp ym
    by_cases on : y∈p.support
    · obtain ⟨i,hi,he⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx on adj
      exact mem_union_left _ (mem_image.mpr ⟨i,hi,he⟩)
    exact mem_union_right _ (mem_erase.mpr ⟨adj.ne.symm,mem_Omit.mpr on⟩)
  have ca := card_le_card sub
  have cb := card_union_le (PinVertices p x) ((Omit p).erase x)
  rw [card_neighborFinset_eq_degree] at ca
  rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,card_erase_of_mem (mem_Omit.mpr hx)] at cb
  omega

theorem nonspanning_short_at_nineteen_impossible (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=19) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length≤13) {x : V} (hx : x∉p.support) : False := by
  classical
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp hx
  have xq : x∉q.support := fun h=>hx ((same x).mpr h)
  have lq := (hp.2 u v q hq.1).trans len
  have qmin := length_ge_twelve hc conn degree hq xq
  have d := omit_add_length hq
  let A := (Omit q).filter (fun y=>6≤G.degree y)
  have Asize : 3≤A.card := by
    have c := high_filter_card degree (Omit q)
    change (Omit q).card≤A.card+1 at c
    omega
  by_cases e : q.length=12
  · apply not_length_twelve_of_three_active hc cap degree hq e du dv A Asize
    intro y ym
    obtain ⟨yo,dy⟩ := mem_filter.mp ym
    have off := mem_Omit.mp yo
    have b := degree_covered_by_pins_and_omitted hq off
    exact ⟨off,card_pos.mp (by omega)⟩
  apply not_length_le_thirteen_of_three_double_active hc cap degree hq lq du dv A Asize
  intro y ym
  obtain ⟨yo,dy⟩ := mem_filter.mp ym
  have off := mem_Omit.mp yo
  have b := degree_covered_by_pins_and_omitted hq off
  exact ⟨off,by omega⟩

theorem traceable_six_at_three_connectivity_order_nineteen
    (hc : G.Connected) (conn : ConnThree G) (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤19) :
    ∃ (a b : V) (p : G.Walk a b),p.IsPath ∧ ∀ v,v∈p.support := by
  classical
  by_cases small : Fintype.card V≤18
  · exact Graffiti189LongestPath.SixThreeEighteen.traceable_six_at_three_connectivity_order_eighteen
      hc conn cap degree small
  obtain ⟨a,b,p,hp⟩ := Graffiti189LongestPath.Rigidity.exists_longest hc
  by_cases out : ∃ x,x∉p.support
  swap
  · refine ⟨a,b,p,hp.1,?_⟩
    intro x
    apply Classical.byContradiction
    intro h
    exact out ⟨x,h⟩
  obtain ⟨x,hx⟩ := out
  exfalso
  by_cases e : p.length≤13
  · exact nonspanning_short_at_nineteen_impossible hc conn cap degree (by omega) hp e hx
  exact nonspanning_long_impossible hc conn cap degree ord hp (by omega) hx

#print axioms traceable_six_at_three_connectivity_order_nineteen
end Graffiti189LongestPath.SixThreeNineteen
