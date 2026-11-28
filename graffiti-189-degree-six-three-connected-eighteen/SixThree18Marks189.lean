import SixThree17Final189

namespace Graffiti189LongestPath.SixThreeEighteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
open private Graffiti189LongestPath.Rigidity.pin_pos Graffiti189LongestPath.Rigidity.reverse_longest
  Graffiti189LongestPath.Rigidity.pin_reverse
  Graffiti189LongestPath.Rigidity.LeftMarks Graffiti189LongestPath.Rigidity.RightMarks
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

abbrev LM {a b : V} (p : G.Walk a b) := Graffiti189LongestPath.Rigidity.LeftMarks p
abbrev RM {a b : V} (p : G.Walk a b) := Graffiti189LongestPath.Rigidity.RightMarks p
def Omit {a b : V} (p : G.Walk a b) : Finset V := univ \ p.support.toFinset
theorem mem_Omit {a b : V} {p : G.Walk a b} {x : V} :
    x∈Omit p ↔ x∉p.support := by simp [Omit]

theorem omit_add_length {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (Omit p).card+(p.length+1)=Fintype.card V := by
  have e := card_sdiff_add_card_eq_card (subset_univ p.support.toFinset)
  change (Omit p).card+p.support.toFinset.card=Fintype.card V at e
  rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at e
  exact e

theorem high_filter_card (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (A : Finset V) : A.card≤(A.filter (fun v=>6≤G.degree v)).card+1 := by
  classical
  have l : (A.filter (fun v=>¬6≤G.degree v)).card≤1 := card_le_one.mpr (fun u um v vm=>by
    by_contra ne
    exact (degree u v ne).elim (mem_filter.mp um).2 (mem_filter.mp vm).2)
  have o := filter_card_add_filter_neg_card_eq_card (s:=A) (p:=fun v=>6≤G.degree v)
  omega

theorem left_right_disjoint {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) {i : ℕ} (ip : i∈Pins p x) : Disjoint (LM p) (RM p) :=
  disjoint_left.mpr (fun _j jl jr=>not_adj_both_end_marks hp hx (p.getVert_mem_support i)
    (Graffiti189LongestPath.pin_data ip).2 (mem_range.mp (mem_filter.mp jl).1)
    (mem_filter.mp jl).2 (mem_filter.mp jr).2)

theorem full_marks {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=12)
    (da : 6≤G.degree a) (db : 6≤G.degree b) {x : V} (hx : x∉p.support)
    {i : ℕ} (ip : i∈Pins p x) :
    (LM p).card=6 ∧ (RM p).card=6 ∧ LM p∪RM p=range p.length := by
  have dis := left_right_disjoint hp hx ip
  have sub : LM p∪RM p⊆range p.length := union_subset (filter_subset ..) (filter_subset ..)
  have le := card_le_card sub
  rw [card_union_of_disjoint dis, Graffiti189LongestPath.Rigidity.card_leftMarks hp,
    Graffiti189LongestPath.Rigidity.card_rightMarks hp,card_range,len] at le
  refine ⟨(Graffiti189LongestPath.Rigidity.card_leftMarks hp).trans (by omega),
    (Graffiti189LongestPath.Rigidity.card_rightMarks hp).trans (by omega),?_⟩
  apply eq_of_subset_of_card_le sub
  rw [card_union_of_disjoint dis, Graffiti189LongestPath.Rigidity.card_leftMarks hp,
    Graffiti189LongestPath.Rigidity.card_rightMarks hp,card_range,len]
  omega

theorem both_ends_see_pin {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (full : LM p∪RM p=range p.length) {x : V} (hx : x∉p.support)
    {i : ℕ} (ip : i∈Pins p x) : G.Adj a (p.getVert i) ∧ G.Adj b (p.getVert i) := by
  have il := (Graffiti189LongestPath.pin_data ip).1
  have i0 := Graffiti189LongestPath.Rigidity.pin_pos hp hx ip
  have pred : i-1∈LM p∪RM p := full.symm ▸ mem_range.mpr (by omega)
  have here : i∈LM p∪RM p := full.symm ▸ mem_range.mpr il
  have l : i-1∈LM p := (mem_union.mp pred).resolve_right
    (fun h=>end_not_adj_pin_predecessor hp hx ip (mem_filter.mp h).2)
  have r : i∈RM p := (mem_union.mp here).resolve_left
    (fun h=>start_not_adj_pin_successor hp hx ip (mem_filter.mp h).2)
  have la := (mem_filter.mp l).2
  rw [show i-1+1=i by omega] at la
  exact ⟨la,(mem_filter.mp r).2⟩

theorem marked_left_candidates_see_pin {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=12) (db : 6≤G.degree b) {x : V} (hx : x∉p.support)
    {i j : ℕ} (ip : i∈Pins p x) (jl : j∈LM p) (dj : 6≤G.degree (p.getVert j)) :
    G.Adj (p.getVert j) (p.getVert i) := by
  have n := mem_range.mp (mem_filter.mp jl).1
  obtain ⟨q,hq,same,ql,_,_⟩ := rotate_start hp j n (mem_filter.mp jl).2
  have xq : x∉q.support := fun h=>hx ((same x).mpr h)
  have on : p.getVert i∈q.support := (same _).mp (p.getVert_mem_support i)
  obtain ⟨k,kp,ke⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hq xq on
    (Graffiti189LongestPath.pin_data ip).2
  have f := (full_marks hq (ql.trans len) dj db xq kp).2.2
  simpa only [ke] using (both_ends_see_pin hq f xq kp).1

theorem marked_right_candidates_see_pin {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length=12) (da : 6≤G.degree a) {x : V} (hx : x∉p.support)
    {i j : ℕ} (ip : i∈Pins p x) (jr : j∈RM p) (dj : 6≤G.degree (p.getVert (j+1))) :
    G.Adj (p.getVert (j+1)) (p.getVert i) := by
  classical
  have jl := mem_range.mp (mem_filter.mp jr).1
  let t := p.length-(j+1)
  have e : p.reverse.getVert t=p.getVert (j+1) := by
    rw [getVert_reverse]
    congr 1
    dsimp only [t]
    omega
  have ej : p.reverse.getVert (t+1)=p.getVert j := by
    rw [getVert_reverse]
    congr 1
    dsimp only [t]
    omega
  have rj : t∈LM p.reverse := mem_filter.mpr
    ⟨mem_range.mpr (by rw [length_reverse]; dsimp only [t]; omega),
      by rw [ej]; exact (mem_filter.mp jr).2⟩
  let i' := p.length-i
  have il := (Graffiti189LongestPath.pin_data ip).1
  have ei : p.reverse.getVert i'=p.getVert i := by
    rw [getVert_reverse]
    congr 1
    dsimp only [i']
    omega
  have rip := Graffiti189LongestPath.Rigidity.pin_reverse hp hx ip
  have h := marked_left_candidates_see_pin (Graffiti189LongestPath.Rigidity.reverse_longest hp)
    (by simpa) da (by simpa using hx) rip rj (by rwa [e])
  dsimp only [i'] at ei
  simpa only [e,ei] using h

#print axioms both_ends_see_pin
#print axioms marked_right_candidates_see_pin
end Graffiti189LongestPath.SixThreeEighteen
