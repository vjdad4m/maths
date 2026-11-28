import SixThree20NoHigh189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree length_ge_twelve)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit omit_add_length not_length_twelve_of_three_active)
open private Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem three_active_of_three_omitted (conn : ConnThree G) {a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (big : 3≤(Omit p).card) :
    ∃ A : Finset V,3≤A.card ∧ ∀ v∈A,v∉p.support ∧ (Pins p v).Nonempty := by
  classical
  let A := (Omit p).filter (fun v=>(Pins p v).Nonempty)
  have data (v : V) (vm : v∈A) : v∉p.support ∧ (Pins p v).Nonempty :=
    ⟨mem_Omit.mp (mem_filter.mp vm).1,(mem_filter.mp vm).2⟩
  refine ⟨A,?_,data⟩
  by_contra! bad
  let S := Omit p \ A
  have sub : A⊆Omit p := filter_subset _ _
  have charge := card_sdiff_add_card_eq_card sub
  change S.card+A.card=(Omit p).card at charge
  obtain ⟨u,um⟩ : S.Nonempty := card_pos.mp (by omega)
  have aOff : a∉Omit p := fun h=>(mem_Omit.mp h) p.start_mem_support
  have sa : a∉S := fun h=>aOff (mem_sdiff.mp h).1
  have aa : a∉A := fun h=>aOff (sub h)
  have dis : Disjoint S A := disjoint_left.mpr (fun v sv av=>(mem_sdiff.mp sv).2 av)
  have bound (v : V) (vm : v∈S) (w : V) (wo : w∉S) (vw : G.Adj v w) : w∈A := by
    by_contra no
    obtain ⟨vo,va⟩ := mem_sdiff.mp vm
    have won : w∈p.support := by
      by_contra off
      exact wo (mem_sdiff.mpr ⟨mem_Omit.mpr off,no⟩)
    obtain ⟨j,jm,_⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp (mem_Omit.mp vo) won vw
    exact va (mem_filter.mpr ⟨vo,⟨j,jm⟩⟩)
  exact (Nat.not_le_of_gt bad)
    (Graffiti189LongestPath.boundary_card_of_connectivity 3 conn um sa aa dis bound)

theorem no_nonspanning_length_twelve_at_twenty (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=20) {a b : V} {p : G.Walk a b} (hp : IsLongest p) 
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

theorem longest_shape_at_twenty (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=20) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) :
    p.length=13 ∨ p.length=14 ∨ ((Omit p).card=1 ∧ p.length=18 ∧ G.degree x<6) := by
  classical
  have lower := length_ge_twelve hc conn degree hp hx
  have no : p.length≠12 := fun e=>no_nonspanning_length_twelve_at_twenty hc conn cap degree ord hp e hx
  by_cases c13 : p.length=13
  · exact .inl c13
  by_cases c14 : p.length=14
  · exact .inr (.inl c14)
  have long : 15≤p.length := by omega
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
  exact .inr (.inr ⟨by simp [singleton],by omega,low⟩)

#print axioms three_active_of_three_omitted
#print axioms longest_shape_at_twenty
end Graffiti189LongestPath.SixThreeTwenty
