import SixThree18FirstPin189

namespace Graffiti189LongestPath.SixThreeEighteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree length_ge_twelve rotate_start_first_edge)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem nonspanning_long_impossible (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤18) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 13≤p.length) {x : V} (hx : x∉p.support) : False := by
  classical
  have low := all_omitted_low_long hc conn cap degree ord hp long hx
  have da : 6≤G.degree a := (degree a x (fun e=>hx (e ▸ p.start_mem_support))).resolve_right (by omega)
  have pins := (saturated_flanks hc conn cap degree ord hp long hx).1
  let B := (Pins p x).image (fun j=>p.getVert (j+2))
  have nbr : G.neighborFinset a⊆insert (p.getVert 1) B := by
    intro y ym
    have ay := (mem_neighborFinset _ _ _).mp ym
    have on : y∈p.support := by
      by_contra out
      exact (Graffiti189LongestPath.no_endpoints hp out).1 ay.symm
    obtain ⟨h,he,hl⟩ := mem_support_iff_exists_getVert.mp on
    by_cases h1 : h=1
    · apply mem_insert.mpr
      left
      simpa only [h1] using he.symm
    have h0 : h≠0 := by
      intro e
      exact ay.ne (by simpa [e] using he)
    let j := h-1
    have sh : j+1=h := by dsimp only [j]; omega
    have jl : j<p.length := by dsimp only [j]; omega
    have j0 : 0<j := by dsimp only [j]; omega
    have jump : G.Adj a (p.getVert (j+1)) := by rw [sh,he]; exact ay
    obtain ⟨q,hq,same,first⟩ := rotate_start_first_edge hp j j0 jl jump
    have ql := long.trans (hq.2 a b p hp.1)
    have out : x∉q.support := fun h=>hx ((same x).mpr h)
    have pin := first_pin_of_longest_long hc conn cap degree ord hq ql out
    have e := (Graffiti189LongestPath.pin_data pin).2
    rw [first] at e
    have old : j-1∈Pins p x := mem_filter.mpr ⟨mem_range.mpr (by omega),e⟩
    have eq : j-1+2=h := by dsimp only [j]; omega
    exact mem_insert_of_mem (mem_image.mpr ⟨j-1,old,by rw [eq,he]⟩)
  have m := card_le_card nbr
  rw [card_neighborFinset_eq_degree] at m
  have n := card_insert_le (p.getVert 1) B
  have k : B.card≤(Pins p x).card := card_image_le
  omega

theorem nonspanning_twelve_at_eighteen_impossible (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V=18) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=12) {x : V} (hx : x∉p.support) : False := by
  classical
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp hx
  have eq : p.length=q.length := Nat.le_antisymm (hq.2 a b p hp.1) (hp.2 u v q hq.1)
  have lq := eq.symm.trans len
  have d := omit_add_length hq
  have Osize : (Omit q).card=5 := by omega
  let A := (Omit q).filter (fun y=>6≤G.degree y)
  have Asize : 3≤A.card := by
    have cap := high_filter_card degree (Omit q)
    change (Omit q).card≤A.card+1 at cap
    omega
  apply not_length_twelve_of_three_active hc cap degree hq lq du dv A Asize
  intro y ym
  obtain ⟨yo,dy⟩ := mem_filter.mp ym
  have off := mem_Omit.mp yo
  refine ⟨off,?_⟩
  by_contra no
  have sub : G.neighborFinset y⊆Omit q := by
    intro z zm
    have yz := (mem_neighborFinset _ _ _).mp zm
    apply mem_Omit.mpr
    intro on
    obtain ⟨j,jm,_⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hq off on yz
    exact no ⟨j,jm⟩
  have k := card_le_card sub
  rw [card_neighborFinset_eq_degree,Osize] at k
  omega

theorem traceable_six_at_three_connectivity_order_eighteen
    (hc : G.Connected) (conn : ConnThree G) (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤18) :
    ∃ (a b : V) (p : G.Walk a b),p.IsPath ∧ ∀ v,v∈p.support := by
  classical
  by_cases small : Fintype.card V≤17
  · exact Graffiti189LongestPath.SixThreeSeventeen.traceable_six_at_three_connectivity_order_seventeen
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
  have lower := length_ge_twelve hc conn degree hp hx
  by_cases e : p.length=12
  · exact nonspanning_twelve_at_eighteen_impossible hc conn cap degree (by omega) hp e hx
  exact nonspanning_long_impossible hc conn cap degree ord hp (by omega) hx

#print axioms traceable_six_at_three_connectivity_order_eighteen
end Graffiti189LongestPath.SixThreeEighteen
