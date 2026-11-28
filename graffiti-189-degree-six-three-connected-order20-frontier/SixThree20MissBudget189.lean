import SixThree20Frontier189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeEighteen (LM RM left_right_disjoint)
open Graffiti189LongestPath.SixThreeNineteen (Holes missed_start_hole missed_end_hole)
open private Graffiti189LongestPath.Rigidity.pin_pos
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The two endpoints share a single hole budget over any nonconsecutive
set of pin indices. Each missing adjacency exhausts a different slot. -/
theorem two_end_miss_budget {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (I : Finset ℕ) (non : I.Nonempty)
    (active : ∀ i∈I,∃ x,x∉p.support ∧ i∈Pins p x)
    (sep : ∀ i∈I,i+1∉I) :
    (I.filter (fun i=>¬G.Adj a (p.getVert i))).card+
      (I.filter (fun i=>¬G.Adj b (p.getVert i))).card+
      (G.degree a+G.degree b)≤p.length := by
  classical
  let A := I.filter (fun i=>¬G.Adj a (p.getVert i))
  let B := I.filter (fun i=>¬G.Adj b (p.getVert i))
  let A' := A.image (·-1)
  have pos (i : ℕ) (im : i∈I) : 0<i := by
    obtain ⟨x,hx,ip⟩ := active i im
    exact Graffiti189LongestPath.Rigidity.pin_pos hp hx ip
  have aEq : A'.card=A.card := card_image_iff.mpr (fun i im j jm e=>by
    change i-1=j-1 at e
    have pi := pos i (mem_filter.mp im).1
    have pj := pos j (mem_filter.mp jm).1
    omega)
  have d : Disjoint A' B := by
    apply disjoint_left.mpr
    intro j aj bj
    obtain ⟨i,ai,e⟩ := mem_image.mp aj
    have im := (mem_filter.mp ai).1
    have jm := (mem_filter.mp bj).1
    change i-1=j at e
    have pi := pos i im
    have ji : j+1=i := by omega
    exact sep j jm (ji.symm ▸ im)
  have ah : A'⊆Holes p := by
    intro j jm
    obtain ⟨i,im,rfl⟩ := mem_image.mp jm
    obtain ⟨inI,no⟩ := mem_filter.mp im
    obtain ⟨x,hx,ip⟩ := active i inI
    exact missed_start_hole hp hx ip no
  have bh : B⊆Holes p := by
    intro i im
    obtain ⟨inI,no⟩ := mem_filter.mp im
    obtain ⟨x,hx,ip⟩ := active i inI
    exact missed_end_hole hp hx ip no
  have ud : A.card+B.card≤(Holes p).card := by
    have n := card_le_card (union_subset ah bh)
    rw [card_union_of_disjoint d,aEq] at n
    exact n
  obtain ⟨i,im⟩ := non
  obtain ⟨x,hx,ip⟩ := active i im
  have sub : LM p∪RM p⊆range p.length := union_subset (filter_subset ..) (filter_subset ..)
  have m := card_sdiff_add_card_eq_card sub
  change (Holes p).card+(LM p∪RM p).card=(range p.length).card at m
  rw [card_union_of_disjoint (left_right_disjoint hp hx ip),card_range,
    Graffiti189LongestPath.Rigidity.card_leftMarks hp,
    Graffiti189LongestPath.Rigidity.card_rightMarks hp] at m
  change A.card+B.card+(G.degree a+G.degree b)≤p.length
  omega

#print axioms two_end_miss_budget
end Graffiti189LongestPath.SixThreeTwenty
