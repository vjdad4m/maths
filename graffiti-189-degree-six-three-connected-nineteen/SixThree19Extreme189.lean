import SixThree19ExtremeRotation189

namespace Graffiti189LongestPath.SixThreeNineteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.reverse_longest from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem one_extreme_pinned (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤19) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 14≤p.length) {x : V} (hx : x∉p.support) :
    1∈Pins p x ∨ p.length-1∈Pins p x := by
  classical
  have low := all_omitted_low_long hc conn cap degree ord hp long hx
  have da : 6≤G.degree a := (degree a x (fun e=>hx (e ▸ p.start_mem_support))).resolve_right (by omega)
  have db : 6≤G.degree b := (degree b x (fun e=>hx (e ▸ p.end_mem_support))).resolve_right (by omega)
  have pc := (saturated_flanks hc conn cap degree ord hp long hx).1
  have non : (Pins p x).Nonempty := card_pos.mp (by omega)
  have bound := (saturated_mark_slots hp hx non
    (fun hi h=>no_chord_to_pin_start hc conn cap degree ord hp long hx hi h)
    (fun hi h=>no_chord_to_pin_end hc conn cap degree ord hp long hx hi h)).2
  have off : x∉p.support.toFinset := fun h=>hx (List.mem_toFinset.mp h)
  have count := card_le_univ (insert x p.support.toFinset)
  rw [card_insert_of_not_mem off,List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at count
  by_contra no
  have bad := bound ⟨fun h=>no (.inl h),fun h=>no (.inr h)⟩
  omega

theorem contradict_first_pins_under_rotations (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤19) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 14≤p.length) {x : V} (hx : x∉p.support)
    (first : ∀ {c : V} (q : G.Walk c b), IsLongest q →
      (∀ v,v∈p.support ↔ v∈q.support) →
      q.getVert (q.length-1)=p.getVert (p.length-1) → 1∈Pins q x) : False := by
  classical
  have low := all_omitted_low_long hc conn cap degree ord hp long hx
  have da : 6≤G.degree a := (degree a x (fun e=>hx (e ▸ p.start_mem_support))).resolve_right (by omega)
  have pins := (saturated_flanks hc conn cap degree ord hp long hx).1
  obtain ⟨i,ip⟩ : (Pins p x).Nonempty := card_pos.mp (by omega)
  have noab : ¬G.Adj a b := by
    intro ab
    have eq : p.length-1+1=p.length := by omega
    have start : G.Adj a (p.getVert (p.length-1+1)) := by rwa [eq,getVert_length]
    have step := p.adj_getVert_succ (i:=p.length-1) (by omega)
    rw [eq,getVert_length] at step
    exact not_adj_both_end_marks hp hx (p.getVert_mem_support i) (Graffiti189LongestPath.pin_data ip).2
      (by omega) start step.symm
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
    have hlast : h≠p.length := by
      intro e
      have yb : y=b := by simpa [e] using he.symm
      exact noab (yb ▸ ay)
    let j := h-1
    have sh : j+1=h := by dsimp only [j]; omega
    have jl : j+1<p.length := by dsimp only [j]; omega
    have j0 : 0<j := by dsimp only [j]; omega
    have jump : G.Adj a (p.getVert (j+1)) := by rw [sh,he]; exact ay
    obtain ⟨q,hq,same,succ,last⟩ := rotate_start_both_extreme_indices hp j j0 jl jump
    have pin := first q hq same last
    have e := (Graffiti189LongestPath.pin_data pin).2
    rw [succ] at e
    have old : j-1∈Pins p x := mem_filter.mpr ⟨mem_range.mpr (by omega),e⟩
    have eq : j-1+2=h := by dsimp only [j]; omega
    exact mem_insert_of_mem (mem_image.mpr ⟨j-1,old,by rw [eq,he]⟩)
  have m := card_le_card nbr
  rw [card_neighborFinset_eq_degree] at m
  have n := card_insert_le (p.getVert 1) B
  have k : B.card≤(Pins p x).card := card_image_le
  omega

theorem last_pin_forced (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤19) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 14≤p.length) {x : V} (hx : x∉p.support) : p.length-1∈Pins p x := by
  classical
  by_contra no
  apply contradict_first_pins_under_rotations hc conn cap degree ord hp long hx
  intro c q hq same last
  have ql := long.trans (hq.2 a b p hp.1)
  have off : x∉q.support := fun h=>hx ((same x).mpr h)
  rcases one_extreme_pinned hc conn cap degree ord hq ql off with one|two
  · exact one
  apply False.elim
  have e := (Graffiti189LongestPath.pin_data two).2
  rw [last] at e
  exact no (mem_filter.mpr ⟨mem_range.mpr (by omega),e⟩)

theorem first_pin_forced (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤19) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 14≤p.length) {x : V} (hx : x∉p.support) : 1∈Pins p x := by
  have h := last_pin_forced hc conn cap degree ord
    (Graffiti189LongestPath.Rigidity.reverse_longest hp) (by simpa using long) (by simpa using hx)
  have e := (Graffiti189LongestPath.pin_data h).2
  rw [getVert_reverse,length_reverse,show p.length-(p.length-1)=1 by omega] at e
  exact mem_filter.mpr ⟨mem_range.mpr (by omega),e⟩

theorem nonspanning_long_impossible (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤19) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 14≤p.length) {x : V} (hx : x∉p.support) : False := by
  apply contradict_first_pins_under_rotations hc conn cap degree ord hp long hx
  intro c q hq same _
  exact first_pin_forced hc conn cap degree ord hq (long.trans (hq.2 a b p hp.1))
    (fun h=>hx ((same x).mpr h))

#print axioms nonspanning_long_impossible
end Graffiti189LongestPath.SixThreeNineteen
