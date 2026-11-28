import SixThree20LowFlanks189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree rotate_start_first_edge endpoint_is_flank_implies_first_pin)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.reverse_longest Graffiti189LongestPath.Rigidity.pin_reverse from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_chord_to_pin_start (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤20) {a b : V} {p : G.Walk a b} (hp : IsLongest p) (long : 15≤p.length)
    {x : V} (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (imin : 2≤i) :
    ¬G.Adj a (p.getVert i) := by
  classical
  intro edge
  have il := (Graffiti189LongestPath.pin_data hi).1
  have sub : i-1+1=i := by omega
  obtain ⟨q,hq,same,first⟩ := rotate_start_first_edge hp (i-1) (by omega) (by omega)
    (by simpa only [sub] using edge)
  have hxo : x∉q.support := fun h=>hx ((same x).mpr h)
  have old : p.getVert (i-1)∈FlankVertices p x :=
    mem_image.mpr ⟨i-1,mem_union_left _ (mem_image.mpr ⟨i,hi,rfl⟩),rfl⟩
  have inD := (mem_sdiff.mp (flanks_outside_boundary hc hp hx old)).1
  have longq := long.trans (hq.2 a b p hp.1)
  have sat := (saturated_flanks hc conn cap degree ord hq longq hxo).2
  have np := endpoint_is_flank_implies_first_pin hq hxo (sat ▸ inD)
  have edge' := (Graffiti189LongestPath.pin_data np).2
  rw [first] at edge'
  have fi : i-1-1∈Pins p x := mem_filter.mpr ⟨mem_range.mpr (by omega),edge'⟩
  have eq : i-1-1+2=i := by omega
  exact no_gap_two hc conn cap degree ord hp long hx fi (eq.symm ▸ hi)

theorem no_chord_to_pin_end (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤20) {a b : V} {p : G.Walk a b} (hp : IsLongest p) (long : 15≤p.length)
    {x : V} (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (imax : i+2≤p.length) :
    ¬G.Adj b (p.getVert i) := by
  have h := no_chord_to_pin_start hc conn cap degree ord
    (Graffiti189LongestPath.Rigidity.reverse_longest hp) (by simpa using long) (by simpa using hx)
    (Graffiti189LongestPath.Rigidity.pin_reverse hp hx hi) (by omega)
  rw [getVert_reverse,show p.length-(p.length-i)=i by omega] at h
  exact h

#print axioms no_chord_to_pin_start
#print axioms no_chord_to_pin_end
end Graffiti189LongestPath.SixThreeTwenty