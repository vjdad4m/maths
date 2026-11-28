import SixThree21ThirteenDouble189
import TwoTerminalOre189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit high_filter_card)
open Graffiti189LongestPath.SixThreeTwenty (HighOmit highOmit_data)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem omitted_inside_degree_lower {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (xo : x∉p.support) :
    G.degree x≤(Pins p x).card+(G.neighborFinset x∩Omit p).card := by
  classical
  have sub : G.neighborFinset x⊆PinVertices p x∪(G.neighborFinset x∩Omit p) := by
    intro y ym
    by_cases on : y∈p.support
    · obtain ⟨i,im,he⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp xo on
        ((mem_neighborFinset _ _ _).mp ym)
      exact mem_union_left _ (mem_image.mpr ⟨i,im,he⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨ym,mem_Omit.mpr on⟩)
  have e := card_le_card sub
  have f := card_union_le (PinVertices p x) (G.neighborFinset x∩Omit p)
  rw [card_neighborFinset_eq_degree] at e
  rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp] at f
  omega

theorem induced_degree_by_filter (K : Finset V) (x : ↑(↑K : Set V)) :
    (K.filter (G.Adj x.val)).card=(G.induce (↑K : Set V)).degree x := by
  classical
  rw [←card_neighborSet_eq_degree,←Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun z=>⟨⟨z.val,(mem_filter.mp z.property).1⟩,(mem_filter.mp z.property).2⟩
    invFun := fun z=>⟨z.val.val,mem_filter.mpr ⟨z.val.property,z.property⟩⟩
    left_inv := fun z=>rfl
    right_inv := fun z=>rfl }

theorem high_omitted_long_route_of_single_pins
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (sz : (Omit p).card=7)
    (single : ∀ z∉p.support,(Pins p z).card≤1)
    {x y : V} (xh : x∈HighOmit p) (yh : y∈HighOmit p) (xy : x≠y) :
    ∃ q : G.Walk x y,q.IsPath ∧ 5≤q.length ∧ ∀ z∈q.support,z∈HighOmit p := by
  classical
  let K := HighOmit p
  let W : Set V := (↑K : Set V)
  let J := G.induce W
  letI : DecidableRel J.Adj := inferInstanceAs (DecidableRel (G.induce (↑K : Set V)).Adj)
  have upper : K.card≤7 := (card_le_card (filter_subset _ _)).trans (by omega)
  have lower : 6≤K.card := by
    have n := high_filter_card degree (Omit p)
    change (Omit p).card≤K.card+1 at n
    omega
  have hiDeg (x : W) : 4≤J.degree x := by
    have xm : x.val∈HighOmit p := x.property
    have ⟨xo,dx⟩ := highOmit_data xm
    have pa := single x.val xo
    have ob := omitted_inside_degree_lower hp xo
    let A := G.neighborFinset x.val∩Omit p
    have e := high_filter_card degree A
    have eq : A.filter (fun v=>6≤G.degree v)=K.filter (G.Adj x.val) := by
      ext v
      simp [A,K,HighOmit,mem_neighborFinset,and_assoc,and_left_comm,and_comm]
    rw [eq] at e
    rw [induced_degree_by_filter K x] at e
    change A.card≤J.degree x+1 at e
    change G.degree x.val≤(Pins p x.val).card+A.card at ob
    omega
  have wCard : Fintype.card W=K.card := Fintype.card_coe _
  let xx : W := ⟨x,xh⟩
  let yy : W := ⟨y,yh⟩
  have ne : xx≠yy := fun h=>xy (congrArg Subtype.val h)
  obtain ⟨r,rp,all⟩ := Graffiti189LongestPath.CrossSaturation.hamilton_connected_of_ore
    (G:=J) (fun u v _ _=>by have d:=hiDeg u; have e:=hiDeg v; omega) ne
  let into : J→g G := ⟨Subtype.val,fun e=>e⟩
  let q := r.map into
  have qp : q.IsPath := by
    apply IsPath.mk'
    rw [show q.support=r.support.map Subtype.val from support_map _ _]
    exact rp.support_nodup.map Subtype.val_injective
  have long : 5≤q.length := by
    have e : r.support.toFinset=univ := eq_univ_of_forall (fun v=>List.mem_toFinset.mpr (all v))
    have f := congrArg Finset.card e
    rw [List.toFinset_card_of_nodup rp.support_nodup,length_support,card_univ,wCard] at f
    change 5≤(r.map into).length
    rw [length_map]
    omega
  refine ⟨q,qp,long,?_⟩
  intro v vm
  change v∈(r.map into).support at vm
  rw [support_map] at vm
  obtain ⟨w,_,eq⟩ := List.mem_map.mp vm
  exact eq ▸ w.property

#print axioms high_omitted_long_route_of_single_pins
end Graffiti189LongestPath.SixThreeTwentyOne
