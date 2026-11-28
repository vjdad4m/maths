import PinRunSeparator189
import MultiPinRotation189

namespace Graffiti189LongestPath.SixThreeSixteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints
  Graffiti189LongestPath.outside_edge from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.LeftMarks Graffiti189LongestPath.Rigidity.RightMarks
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def ConnThree (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V,S.card<3 → (G.induce ((↑S : Set V)ᶜ)).Connected

theorem length_ge_twelve (hc : G.Connected) (conn : ConnThree G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) {x : V} (hx : x∉p.support) :
    12≤p.length := by
  classical
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp hx
  obtain ⟨w,hw,s,hs,ws⟩ := Graffiti189LongestPath.outside_edge q hc
    ⟨x,fun h=>hx ((same x).mpr h)⟩
  let L := Graffiti189LongestPath.Rigidity.LeftMarks q
  let R := Graffiti189LongestPath.Rigidity.RightMarks q
  have dis : Disjoint L R := disjoint_left.mpr (fun i li ri=>
    not_adj_both_end_marks hq hw hs ws (mem_range.mp (mem_filter.mp li).1)
      (mem_filter.mp li).2 (mem_filter.mp ri).2)
  have n : (L∪R).card≤(range q.length).card :=
    card_le_card (union_subset (filter_subset ..) (filter_subset ..))
  rw [card_union_of_disjoint dis,card_range] at n
  change (Graffiti189LongestPath.Rigidity.LeftMarks q).card+
    (Graffiti189LongestPath.Rigidity.RightMarks q).card≤q.length at n
  rw [Graffiti189LongestPath.Rigidity.card_leftMarks hq,
    Graffiti189LongestPath.Rigidity.card_rightMarks hq] at n
  have le := hp.2 u v q hq.1
  omega

theorem all_omitted_low (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤16)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) {x : V} (hx : x∉p.support) :
    G.degree x<6 := by
  classical
  by_contra! dx
  have length := length_ge_twelve hc conn degree hp hx
  let O := (univ : Finset V) \ p.support.toFinset
  have hO : O.card≤3 := by
    have d := card_sdiff_add_card_eq_card (subset_univ p.support.toFinset)
    change O.card+p.support.toFinset.card=Fintype.card V at d
    rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at d
    omega
  have xo : x∈O := mem_sdiff.mpr ⟨mem_univ _,fun h=>hx (List.mem_toFinset.mp h)⟩
  have few : (Pins p x).card≤3 := by
    by_cases h : (Pins p x).Nonempty
    · obtain ⟨i,hi⟩ := h
      have hb := PinRun.high_omitted_pin_budget hc 6 3 cap conn hp hx (Graffiti189LongestPath.pin_data hi).2 dx
      omega
    rw [not_nonempty_iff_eq_empty.mp h,card_empty]
    decide
  have sub : G.neighborFinset x ⊆ PinVertices p x ∪ O.erase x := by
    intro y ym
    have adj := (mem_neighborFinset _ _ _).mp ym
    by_cases on : y∈p.support
    · obtain ⟨i,hi,he⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx on adj
      exact mem_union_left _ (mem_image.mpr ⟨i,hi,he⟩)
    exact mem_union_right _ (mem_erase.mpr ⟨adj.ne.symm,mem_sdiff.mpr ⟨mem_univ _,
      fun m=>on (List.mem_toFinset.mp m)⟩⟩)
  have ca := card_le_card sub
  have cb := card_union_le (PinVertices p x) (O.erase x)
  rw [card_neighborFinset_eq_degree] at ca
  rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,card_erase_of_mem xo] at cb
  omega

#print axioms all_omitted_low
end Graffiti189LongestPath.SixThreeSixteen
