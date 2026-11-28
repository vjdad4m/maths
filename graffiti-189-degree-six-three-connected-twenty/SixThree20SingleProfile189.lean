import SixThree20Candidates189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit high_filter_card)
open Graffiti189LongestPath.SixThreeNineteen (degree_covered_by_pins_and_omitted)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem Graffiti189LongestPath.OneSlack.card_pinVertices
  Graffiti189LongestPath.OneSlack.mem_omittedStar Graffiti189LongestPath.OneSlack.mem_external
  Graffiti189LongestPath.OneSlack.boundary_lower from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem high_omitted_universal_when_exact_degree_room {a b : V} {p : G.Walk a b}
    (hp : IsLongest p) {x : V} (xm : x∈HighOmit p)
    (room : (Pins p x).card+((Omit p).card-1)≤6) :
    ∀ y,y∉p.support → x≠y → G.Adj x y := by
  classical
  have ⟨xo,dx⟩ := highOmit_data xm
  let O := Omit p
  let C := (O.erase x).filter (G.Adj x)
  have xO : x∈O := mem_Omit.mpr xo
  have sub : G.neighborFinset x ⊆ PinVertices p x∪C := by
    intro y ym
    have adj := (mem_neighborFinset _ _ _).mp ym
    by_cases on : y∈p.support
    · obtain ⟨i,ip,he⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp xo on adj
      exact mem_union_left _ (mem_image.mpr ⟨i,ip,he⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨mem_erase.mpr ⟨adj.ne.symm,mem_Omit.mpr on⟩,adj⟩)
  have n := card_le_card sub
  have m := card_union_le (PinVertices p x) C
  rw [card_neighborFinset_eq_degree] at n
  rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp] at m
  have eq : C=O.erase x := by
    apply eq_of_subset_of_card_le (filter_subset _ _)
    rw [card_erase_of_mem xO]
    change (Pins p x).card+(O.card-1)≤6 at room
    have op : 0 < O.card := card_pos.mpr ⟨x,xO⟩
    change (O.card-1) ≤ C.card
    omega
  intro y yo xy
  have yc : y∈C := eq.symm ▸ mem_erase.mpr ⟨xy.symm,mem_Omit.mpr yo⟩
  exact (mem_filter.mp yc).2

theorem low_omitted_no_pins_at_six {a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (size : (Omit p).card=6)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (all : ∀ y∈HighOmit p,(Pins p y).card=1)
    {x : V} (xo : x∉p.support) (dx : ¬6≤G.degree x) : ¬(Pins p x).Nonempty := by
  classical
  rintro ⟨i,ip⟩
  let O := (Omit p).erase x
  have xO : x∈Omit p := mem_Omit.mpr xo
  have Osize : O.card=5 := by change ((Omit p).erase x).card=5; rw [card_erase_of_mem xO,size]
  have into : O⊆G.neighborFinset x := by
    intro y ym
    obtain ⟨yx,yO⟩ := mem_erase.mp ym
    have high := (degree y x yx).resolve_right dx
    have yh : y∈HighOmit p := mem_filter.mpr ⟨yO,high⟩
    have room : (Pins p y).card+((Omit p).card-1)≤6 := by rw [all y yh,size]
    exact (mem_neighborFinset _ _ _).mpr
      (high_omitted_universal_when_exact_degree_room hp yh room x xo yx).symm
  have off : p.getVert i∉O := fun h=>(mem_Omit.mp (mem_erase.mp h).2) (p.getVert_mem_support i)
  have sub : insert (p.getVert i) O⊆G.neighborFinset x := by
    intro y ym
    exact (mem_insert.mp ym).elim (fun e=>e.symm ▸
      (mem_neighborFinset _ _ _).mpr (Graffiti189LongestPath.pin_data ip).2) (fun h=>into h)
  have n := card_le_card sub
  rw [card_insert_of_not_mem off,Osize,card_neighborFinset_eq_degree] at n
  exact dx n

theorem high_sites_at_least_three_of_universal_and_no_low_ports (conn : ConnThree G)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (xm : x∈HighOmit p)
    (univ : ∀ y,y∉p.support → x≠y → G.Adj x y)
    (low : ∀ y,y∉p.support → ¬6≤G.degree y → ¬(Pins p y).Nonempty) :
    3≤(Sites p (HighOmit p)).card := by
  classical
  have xo := (highOmit_data xm).1
  let B := (Sites p (HighOmit p)).image p.getVert
  have sub : External G (OmittedStar p x)⊆B := by
    intro z zm
    obtain ⟨off,y,ym,yz⟩ := Graffiti189LongestPath.OneSlack.mem_external.mp zm
    have yo := (Graffiti189LongestPath.OneSlack.mem_omittedStar.mp ym).1
    have zon : z∈p.support := by
      by_contra zo
      by_cases zx : z=x
      · exact off (Graffiti189LongestPath.OneSlack.mem_omittedStar.mpr ⟨zo,.inl zx⟩)
      exact off (Graffiti189LongestPath.OneSlack.mem_omittedStar.mpr ⟨zo,.inr (univ z zo (fun h=>zx h.symm))⟩)
    obtain ⟨i,ip,ie⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp yo zon yz
    have dy : 6≤G.degree y := Classical.byContradiction (fun h=>low y yo h ⟨i,ip⟩)
    have yH : y∈HighOmit p := mem_filter.mpr ⟨mem_Omit.mpr yo,dy⟩
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨(mem_filter.mp ip).1,y,yH,(Graffiti189LongestPath.pin_data ip).2⟩,ie⟩
  have d := Graffiti189LongestPath.OneSlack.boundary_lower 3 hp xo conn
  have e := card_le_card sub
  have f : B.card≤(Sites p (HighOmit p)).card := card_image_le
  omega

#print axioms low_omitted_no_pins_at_six
#print axioms high_sites_at_least_three_of_universal_and_no_low_ports
end Graffiti189LongestPath.SixThreeTwenty
