import SixThree18Saturation189

namespace Graffiti189LongestPath.SixThreeEighteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem all_omitted_low_long (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤18) {a b : V} {p : G.Walk a b} (hp : IsLongest p) (long : 13≤p.length)
    {x : V} (hx : x∉p.support) : G.degree x<6 := by
  classical
  by_contra! dx
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp hx
  have xq : x∉q.support := fun h=>hx ((same x).mpr h)
  have longq := long.trans (hq.2 a b p hp.1)
  obtain ⟨len,_,pc,_⟩ := high_pin_shape_long hc conn cap degree ord hq longq xq dx
  let I := (Pins q x).erase 1
  let T := I.image (·-1)
  have iSize : 2≤I.card := by
    by_cases h : 1∈Pins q x
    · change 2≤((Pins q x).erase 1).card
      rw [card_erase_of_mem h,pc]
    change 2≤((Pins q x).erase 1).card
    rw [erase_eq_of_not_mem h,pc]
    decide
  have tSize : 2≤T.card := by
    have eq : T.card=I.card := card_image_iff.mpr (fun j jm k km e=>by
      have j0 := Graffiti189LongestPath.Rigidity.pin_pos hq xq (mem_erase.mp jm).2
      have k0 := Graffiti189LongestPath.Rigidity.pin_pos hq xq (mem_erase.mp km).2
      change j-1=k-1 at e
      omega)
    rw [eq]
    exact iSize
  have data (j : ℕ) (jm : j∈T) : j<q.length ∧ j∉LM q ∧ j∉RM q := by
    obtain ⟨i,im,rfl⟩ := mem_image.mp jm
    obtain ⟨i1,ip⟩ := mem_erase.mp im
    have i0 := Graffiti189LongestPath.Rigidity.pin_pos hq xq ip
    have il := (Graffiti189LongestPath.pin_data ip).1
    refine ⟨by omega,?_,?_⟩
    · intro h
      have e := (mem_filter.mp h).2
      rw [show i-1+1=i by omega] at e
      exact high_pin_no_start_chord hc conn cap degree ord hq longq xq dx ip (by omega) e
    · intro h
      exact end_not_adj_pin_predecessor hq xq ip (mem_filter.mp h).2
  obtain ⟨i,ip⟩ : (Pins q x).Nonempty := card_pos.mp (by omega)
  have lr := left_right_disjoint hq xq ip
  have dt : Disjoint (LM q∪RM q) T := disjoint_left.mpr (fun j lm tm=>
    (mem_union.mp lm).elim (data j tm).2.1 (data j tm).2.2)
  have sub : (LM q∪RM q)∪T⊆range q.length := by
    refine union_subset (union_subset (filter_subset ..) (filter_subset ..)) ?_
    intro j jm
    exact mem_range.mpr (data j jm).1
  have count := card_le_card sub
  rw [card_union_of_disjoint dt,card_union_of_disjoint lr,
    Graffiti189LongestPath.Rigidity.card_leftMarks hq,
    Graffiti189LongestPath.Rigidity.card_rightMarks hq,card_range,len] at count
  omega

#print axioms all_omitted_low_long
end Graffiti189LongestPath.SixThreeEighteen
