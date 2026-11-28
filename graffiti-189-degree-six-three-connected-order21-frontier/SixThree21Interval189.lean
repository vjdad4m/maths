import SixThree21ExtraHoles189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeTwenty (rotate_start_indexed_prefix)
open Graffiti189LongestPath.SixThreeEighteen (LM RM left_right_disjoint)
open Graffiti189LongestPath.SixThreeNineteen (Holes missed_start_hole missed_end_hole pin_indices_not_consecutive)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos Graffiti189LongestPath.Rigidity.reverse_longest
  Graffiti189LongestPath.Rigidity.pin_reverse Graffiti189LongestPath.Rigidity.card_leftMarks
  Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem consecutive_interval_extra_hole (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤21) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (long : 16≤p.length) {x : V} (hx : x∉p.support)
    {i j : ℕ} (ip : i∈Pins p x) (jp : j∈Pins p x) (ij : i<j)
    (middle : ∀ k∈Pins p x,¬(i<k ∧ k<j)) :
    ∃ t∈ExtraHoles p x,i<t ∧ t+1<j := by
  classical
  have jl := (Graffiti189LongestPath.pin_data jp).1
  have iGap : i+3≤j := by
    by_contra! small
    have gap : j=i+1 ∨ j=i+2 := by omega
    rcases gap with e|e
    · exact pin_indices_not_consecutive hp hx ip (e ▸ jp)
    exact no_gap_two hc conn cap degree ord hp long hx ip (e ▸ jp)
  have leftFlank : p.getVert (i+1)∈DistanceTwo G x :=
    (mem_sdiff.mp (flanks_outside_boundary hc hp hx
      (mem_image.mpr ⟨i+1,mem_union_right _ (mem_image.mpr ⟨i,ip,rfl⟩),rfl⟩))).1
  have rightFlank : p.getVert (j-1)∈DistanceTwo G x :=
    (mem_sdiff.mp (flanks_outside_boundary hc hp hx
      (mem_image.mpr ⟨j-1,mem_union_left _ (mem_image.mpr ⟨j,jp,rfl⟩),rfl⟩))).1
  have leftInc : i+1<p.length := by omega
  have leftNo : i+1∉Pins p x := fun m=>middle _ m ⟨by omega,by omega⟩
  have leftNo' : i+1+1∉Pins p x := fun m=>middle _ m ⟨by omega,by omega⟩
  by_cases ml' : i+1∈LM p ∨ i+1∈RM p
  swap
  · exact ⟨i+1,mem_extra_holes_of_unmarked hp hx leftInc leftNo leftNo' ml',by omega,by omega⟩
  have mr : i+1∈RM p := ml'.resolve_left
    (fun l=>left_mark_not_flank_long hc conn cap degree ord hp long hx l leftFlank)
  have big : i+4≤j := by
    by_contra! no
    have e : i+1+1=j-1 := by omega
    exact right_mark_not_flank_long hc conn cap degree ord hp long hx mr (e.symm ▸ rightFlank)
  have rightInc : j-2<p.length := by omega
  have rightNo : j-2∉Pins p x := fun m=>middle _ m ⟨by omega,by omega⟩
  have rightNo' : j-2+1∉Pins p x := fun m=>middle _ m ⟨by omega,by omega⟩
  by_cases mr' : j-2∈LM p ∨ j-2∈RM p
  swap
  · exact ⟨j-2,mem_extra_holes_of_unmarked hp hx rightInc rightNo rightNo' mr',by omega,by omega⟩
  have ml : j-2∈LM p := mr'.resolve_right (fun r=>
    right_mark_not_flank_long hc conn cap degree ord hp long hx r
      ((show j-2+1=j-1 by omega).symm ▸ rightFlank))
  exfalso
  obtain ⟨q,hq,same,index⟩ := rotate_start_indexed_prefix hp (j-2) (by omega) (mem_filter.mp ml).2
  have xq : x∉q.support := fun h=>hx ((same x).mpr h)
  have ql := hq.2 a b p hp.1
  let k := j-2-i
  have e : q.getVert k=p.getVert i := by
    rw [index k (by dsimp only [k]; omega)]
    congr 1
    dsimp only [k]
    omega
  have f : q.getVert (k-1)=p.getVert (i+1) := by
    rw [index (k-1) (by dsimp only [k]; omega)]
    congr 1
    dsimp only [k]
    omega
  have kp : k∈Pins q x := mem_filter.mpr ⟨mem_range.mpr (by dsimp only [k]; omega),
    by rw [e]; exact (Graffiti189LongestPath.pin_data ip).2⟩
  apply end_not_adj_pin_predecessor hq xq kp
  rw [f]
  exact (mem_filter.mp mr).2

#print axioms consecutive_interval_extra_hole
end Graffiti189LongestPath.SixThreeTwentyOne
