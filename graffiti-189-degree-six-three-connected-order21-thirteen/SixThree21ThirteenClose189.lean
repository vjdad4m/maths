import SixThree21LinkedGap189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit omit_add_length)
open Graffiti189LongestPath.SixThreeTwenty (Sites PortSet)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_nonspanning_length_thirteen_at_twenty_one (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=13) {x : V} (xo : x∉p.support) : False := by
  classical
  have sz : (Omit p).card=7 := by have h:=omit_add_length hp; omega
  have single : ∀ y∉p.support,(Pins p y).card≤1 := fun y yo=>
    no_double_pins_at_length_thirteen_twenty_one hc conn cap degree ord hp len yo
  have ports := three_port_sites_of_nonempty_omitted conn hp ⟨x,mem_Omit.mpr xo⟩
  have size : 3≤(Sites p (Omit p)).card :=
    ports.trans (show (PortSet p (Omit p)).card≤(Sites p (Omit p)).card from card_image_le)
  have gap {i j : ℕ} (im : i∈Sites p (Omit p)) (jm : j∈Sites p (Omit p)) (ij : i<j) :
      i+7≤j := by
    obtain ⟨ir,u,um,ui⟩ := mem_filter.mp im
    obtain ⟨jr,v,vm,vj⟩ := mem_filter.mp jm
    have uo := mem_Omit.mp um
    have vo := mem_Omit.mp vm
    have iu : i∈Pins p u := mem_filter.mpr ⟨ir,ui⟩
    have jv : j∈Pins p v := mem_filter.mpr ⟨jr,vj⟩
    have ne : u≠v := by
      intro e
      subst v
      exact (Nat.ne_of_lt ij) (card_le_one.mp (single u uo) i iu j jv)
    obtain ⟨q,qp,ql,off⟩ := omitted_long_route_of_single_pins conn degree hp sz single uo vo ne
    have n := linked_pins_gap_at_least_route hp iu jv ij q qp off
    omega
  obtain ⟨i,im,j,jm,k,km,ij,jk,_,_⟩ := two_consecutive_intervals_of_three (Sites p (Omit p)) size
  have l := gap im jm ij
  have r := gap jm km jk
  have upper := mem_range.mp (mem_filter.mp km).1
  omega

theorem longest_shape_at_twenty_one_reduced
    (hc : G.Connected) (conn : ConnThree G) (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (xo : x∉p.support) : p.length=14 ∨ p.length=15 := by
  rcases longest_shape_at_twenty_one hc conn cap degree ord hp xo with h|h
  · exact (no_nonspanning_length_thirteen_at_twenty_one hc conn cap degree ord hp h xo).elim
  exact h

#print axioms no_nonspanning_length_thirteen_at_twenty_one
#print axioms longest_shape_at_twenty_one_reduced
end Graffiti189LongestPath.SixThreeTwentyOne
