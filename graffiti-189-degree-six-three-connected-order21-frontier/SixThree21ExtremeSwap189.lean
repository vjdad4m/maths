import SixThree21LowRotation189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree endpoint_is_flank_implies_first_pin)
open Graffiti189LongestPath.SixThreeEighteen (LM RM left_right_disjoint)
open Graffiti189LongestPath.SixThreeNineteen (pin_indices_not_consecutive)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos Graffiti189LongestPath.Rigidity.reverse_longest
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_extreme_pin_long (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 16≤p.length) {x : V} (hx : x∉p.support) : 1∉Pins p x := by
  intro pin
  have dx := all_omitted_low_long hc conn cap degree ord hp long hx
  have ax : a≠x := fun h=>hx (h ▸ p.start_mem_support)
  have da := (degree a x ax).resolve_right (by omega)
  cases p with
  | nil => simp at long
  | @cons a u b e r =>
    have step : G.Adj x u := by simpa using (Graffiti189LongestPath.pin_data pin).2
    have xo : x∉r.support := fun h=>hx (List.mem_cons_of_mem _ h)
    have oldOff : a∉r.support := (cons_isPath_iff _ _).mp hp.1 |>.2
    let q := Walk.cons step r
    have hq : q.IsPath := hp.1.of_cons.cons xo
    have qe : q.length=(Walk.cons e r).length := rfl
    have maxq : IsLongest q := ⟨hq,fun i j w hw=>qe.symm ▸ hp.2 i j w hw⟩
    have aq : a∉q.support := by
      change a∉x::r.support
      exact fun h=>(List.mem_cons.mp h).elim ax oldOff
    have fa := all_omitted_low_long hc conn cap degree ord maxq (qe.symm ▸ long) aq
    omega

theorem end_outside_flanks_long (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 16≤p.length) {x : V} (hx : x∉p.support) : a∉DistanceTwo G x ∧ b∉DistanceTwo G x := by
  have sat := (saturated_flanks hc conn cap degree ord hp long hx).2
  have n1 := no_extreme_pin_long hc conn cap degree ord hp long hx
  have hq := Graffiti189LongestPath.Rigidity.reverse_longest hp
  have qh : x∉p.reverse.support := by simpa using hx
  have ql : 16≤p.reverse.length := by simpa using long
  have sq := (saturated_flanks hc conn cap degree ord hq ql qh).2
  exact ⟨fun h=>n1 (endpoint_is_flank_implies_first_pin hp hx (sat ▸ h)),
    fun h=>no_extreme_pin_long hc conn cap degree ord hq ql qh
      (endpoint_is_flank_implies_first_pin hq qh (sq ▸ h))⟩

theorem left_mark_not_flank_long (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 16≤p.length) {x : V} (hx : x∉p.support) {i : ℕ} (m : i∈LM p) :
    p.getVert i∉DistanceTwo G x := by
  obtain ⟨q,hq,same,_,_,_⟩ := rotate_start hp i (mem_range.mp (mem_filter.mp m).1) (mem_filter.mp m).2
  exact (end_outside_flanks_long hc conn cap degree ord hq (long.trans (hq.2 a b p hp.1))
    (fun h=>hx ((same x).mpr h))).1

theorem right_mark_not_flank_long (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 16≤p.length) {x : V} (hx : x∉p.support) {i : ℕ} (m : i∈RM p) :
    p.getVert (i+1)∉DistanceTwo G x := by
  let j := p.length-(i+1)
  have il := mem_range.mp (mem_filter.mp m).1
  have e : p.reverse.getVert j=p.getVert (i+1) := by
    rw [getVert_reverse]
    congr 1
    dsimp only [j]
    omega
  have f : p.reverse.getVert (j+1)=p.getVert i := by
    rw [getVert_reverse]
    congr 1
    dsimp only [j]
    omega
  have jm : j∈LM p.reverse := mem_filter.mpr ⟨mem_range.mpr (by rw [length_reverse]; dsimp only [j]; omega),
    by rw [f]; exact (mem_filter.mp m).2⟩
  have h := left_mark_not_flank_long hc conn cap degree ord
    (Graffiti189LongestPath.Rigidity.reverse_longest hp) (by simpa using long) (by simpa using hx) jm
  simpa only [e] using h

#print axioms no_extreme_pin_long
#print axioms right_mark_not_flank_long
end Graffiti189LongestPath.SixThreeTwentyOne
