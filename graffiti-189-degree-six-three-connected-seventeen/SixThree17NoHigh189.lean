import SixThree17Saturation189

namespace Graffiti189LongestPath.SixThreeSeventeen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos
  Graffiti189LongestPath.Rigidity.LeftMarks Graffiti189LongestPath.Rigidity.RightMarks
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem all_omitted_low17 (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤17) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) : G.degree x<6 := by
  classical
  by_contra! dx
  obtain ⟨u,v,q,hq,same,du,dv⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc 3 (by decide) 6 conn degree hp hx
  have xq : x∉q.support := fun h=>hx ((same x).mpr h)
  obtain ⟨len,_,pc,_⟩ := high_pin_shape hc conn cap degree ord hq xq dx
  obtain ⟨i,ip,imin⟩ : ∃ i∈Pins q x, 2≤i := by
    by_contra no
    have sub : Pins q x⊆{1} := by
      intro i ip
      have positive := Graffiti189LongestPath.Rigidity.pin_pos hq xq ip
      have lower : ¬2≤i := fun h=>no ⟨i,ip,h⟩
      exact mem_singleton.mpr (by omega)
    have d := card_le_card sub
    rw [pc,card_singleton] at d
    omega
  have il := (Graffiti189LongestPath.pin_data ip).1
  let L := Graffiti189LongestPath.Rigidity.LeftMarks q
  let R := Graffiti189LongestPath.Rigidity.RightMarks q
  let j := i-1
  have dis : Disjoint L R := disjoint_left.mpr (fun t tl tr=>
    not_adj_both_end_marks hq xq (q.getVert_mem_support i)
      (Graffiti189LongestPath.pin_data ip).2 (mem_range.mp (mem_filter.mp tl).1)
      (mem_filter.mp tl).2 (mem_filter.mp tr).2)
  have l : j∉L := by
    intro h
    have adj := (mem_filter.mp h).2
    have eq : j+1=i := by dsimp only [j]; omega
    rw [eq] at adj
    exact high_pin_no_start_chord hc conn cap degree ord hq xq dx ip imin adj
  have r : j∉R := fun h=>end_not_adj_pin_predecessor hq xq ip (mem_filter.mp h).2
  have miss : j∉L∪R := fun m=>(mem_union.mp m).elim l r
  have sub : insert j (L∪R) ⊆ range q.length := by
    intro z zm
    rcases mem_insert.mp zm with rfl|mz
    · exact mem_range.mpr (by dsimp only [j]; omega)
    exact union_subset (filter_subset ..) (filter_subset ..) mz
  have d := card_le_card sub
  rw [card_insert_of_not_mem miss,card_union_of_disjoint dis,card_range] at d
  change (Graffiti189LongestPath.Rigidity.LeftMarks q).card+
    (Graffiti189LongestPath.Rigidity.RightMarks q).card+1≤q.length at d
  rw [Graffiti189LongestPath.Rigidity.card_leftMarks hq,
    Graffiti189LongestPath.Rigidity.card_rightMarks hq,len] at d
  omega

#print axioms all_omitted_low17
end Graffiti189LongestPath.SixThreeSeventeen
