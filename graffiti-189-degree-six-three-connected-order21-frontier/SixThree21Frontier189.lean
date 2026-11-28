import SixThree21Interval189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree length_ge_twelve)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit omit_add_length not_length_twelve_of_three_active)
open Graffiti189LongestPath.SixThreeTwenty (three_active_of_three_omitted)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem two_consecutive_intervals_of_three (I : Finset ℕ) (three : 3≤I.card) :
    ∃ i∈I,∃ j∈I,∃ k∈I,i<j ∧ j<k ∧
      (∀ t∈I,¬(i<t ∧ t<j)) ∧ (∀ t∈I,¬(j<t ∧ t<k)) := by
  classical
  have hI : I.Nonempty := card_pos.mp (by omega)
  let i := I.min' hI
  have im : i∈I := min'_mem I hI
  let J := I.erase i
  have jc : J.card=I.card-1 := card_erase_of_mem im
  have hJ : J.Nonempty := card_pos.mp (by omega)
  let j := J.min' hJ
  have jm : j∈J := min'_mem J hJ
  obtain ⟨ji,jI⟩ := mem_erase.mp jm
  have ij : i<j := by
    have h := min'_le I j jI
    change i≤j at h
    omega
  let K := J.erase j
  have kc : K.card=J.card-1 := card_erase_of_mem jm
  have hK : K.Nonempty := card_pos.mp (by omega)
  let k := K.min' hK
  have km : k∈K := min'_mem K hK
  obtain ⟨kj,kJ⟩ := mem_erase.mp km
  have jk : j<k := by
    have h := min'_le J k kJ
    change j≤k at h
    omega
  refine ⟨i,im,j,jI,k,(mem_erase.mp kJ).2,ij,jk,?_,?_⟩
  · intro t tm tt
    have tj : t∈J := mem_erase.mpr ⟨by omega,tm⟩
    have h := min'_le J t tj
    change j≤t at h
    omega
  · intro t tm tt
    have tk : t∈K := mem_erase.mpr ⟨by omega,mem_erase.mpr ⟨by omega,tm⟩⟩
    have h := min'_le K t tk
    change k≤t at h
    omega

theorem no_nonspanning_length_nineteen_at_twenty_one
    (hc : G.Connected) (conn : ConnThree G) (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=19) {x : V} (hx : x∉p.support) : False := by
  classical
  have long : 16≤p.length := by omega
  have pc := (saturated_flanks hc conn cap degree ord hp long hx).1
  obtain ⟨i,im,j,jm,k,km,ij,jk,mid1,mid2⟩ := two_consecutive_intervals_of_three (Pins p x) (by omega)
  obtain ⟨s,sm,is,sj⟩ := consecutive_interval_extra_hole hc conn cap degree ord hp long hx im jm ij mid1
  obtain ⟨t,tm,jt,tk⟩ := consecutive_interval_extra_hole hc conn cap degree ord hp long hx jm km jk mid2
  have bound := extra_holes_card_le_one_nineteen hc conn cap degree ord hp len hx
  have eq := card_le_one.mp bound s sm t tm
  omega

theorem no_nonspanning_length_twelve_at_twenty_one
    (hc : G.Connected) (conn : ConnThree G) (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=12) {x : V} (hx : x∉p.support) : False := by
  classical
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp hx
  have le := hp.2 u v q hq.1
  have ge := hq.2 a b p hp.1
  have ql : q.length=12 := by omega
  have c := omit_add_length hq
  obtain ⟨A,Ac,active⟩ := three_active_of_three_omitted conn hq (by omega)
  exact not_length_twelve_of_three_active hc cap degree hq ql du dv A Ac active

theorem longest_shape_at_twenty_one
    (hc : G.Connected) (conn : ConnThree G) (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) :
    p.length=13 ∨ p.length=14 ∨ p.length=15 := by
  classical
  have lower := length_ge_twelve hc conn degree hp hx
  have no : p.length≠12 := fun e=>no_nonspanning_length_twelve_at_twenty_one hc conn cap degree ord hp e hx
  by_cases c13 : p.length=13
  · exact .inl c13
  by_cases c14 : p.length=14
  · exact .inr (.inl c14)
  by_cases c15 : p.length=15
  · exact .inr (.inr c15)
  have long : 16≤p.length := by omega
  have low := all_omitted_low_long hc conn cap degree (by omega) hp long hx
  have singleton : Omit p={x} := by
    ext y
    constructor
    · intro ym
      apply mem_singleton.mpr
      by_contra ne
      have ly := all_omitted_low_long hc conn cap degree (by omega) hp long (mem_Omit.mp ym)
      rcases degree y x ne with h|h <;> omega
    intro ym
    exact mem_Omit.mpr ((mem_singleton.mp ym).symm ▸ hx)
  have e := omit_add_length hp
  rw [singleton,card_singleton] at e
  exact (no_nonspanning_length_nineteen_at_twenty_one hc conn cap degree (by omega)
    hp (by omega) hx).elim

#print axioms no_nonspanning_length_nineteen_at_twenty_one
#print axioms longest_shape_at_twenty_one
end Graffiti189LongestPath.SixThreeTwentyOne
