import SixThree21Frontier189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeTwenty (HighOmit Sites highOmit_data high_inner_neighbors_ge_three)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit omit_add_length high_filter_card)
open Graffiti189LongestPath.SixThreeNineteen (pin_indices_not_consecutive degree_covered_by_pins_and_omitted)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem high_omitted_short_join_seven (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (size : (Omit p).card≤7) {x y : V} (xm : x∈HighOmit p) (ym : y∈HighOmit p) (xy : x≠y) :
    ∃ q : G.Walk x y,q.IsPath ∧ 0<q.length ∧ ∀ z∈q.support,z∉p.support := by
  classical
  have xo := (highOmit_data xm).1
  have yo := (highOmit_data ym).1
  by_cases adj : G.Adj x y
  · refine ⟨adj.toWalk,by simpa using xy,by simp,?_⟩
    intro v vv he
    have hv : v=x ∨ v=y := by simpa using vv
    rcases hv with rfl|rfl
    · exact xo he
    · exact yo he
  let A := G.neighborFinset x∩Omit p
  let B := G.neighborFinset y∩Omit p
  have la : 3≤A.card := high_inner_neighbors_ge_three hc conn cap hp xm
  have lb : 3≤B.card := high_inner_neighbors_ge_three hc conn cap hp ym
  have meet : (A∩B).Nonempty := by
    by_contra! hn
    have dis : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro v va vb
      exact hn ⟨v,mem_inter.mpr ⟨va,vb⟩⟩
    have sub : A∪B⊆((Omit p).erase x).erase y := by
      intro v vm
      have vd : v∈Omit p ∧ v≠x ∧ v≠y := by
        rcases mem_union.mp vm with vA|vB
        · have hxv := (mem_neighborFinset _ _ _).mp (mem_inter.mp vA).1
          exact ⟨(mem_inter.mp vA).2,hxv.ne.symm,fun e=>adj (e ▸ hxv)⟩
        have hyv := (mem_neighborFinset _ _ _).mp (mem_inter.mp vB).1
        exact ⟨(mem_inter.mp vB).2,fun e=>adj (e ▸ hyv).symm,hyv.ne.symm⟩
      exact mem_erase.mpr ⟨vd.2.2,mem_erase.mpr ⟨vd.2.1,vd.1⟩⟩
    have ya : y∈(Omit p).erase x := mem_erase.mpr ⟨xy.symm,mem_Omit.mpr yo⟩
    have n := card_le_card sub
    rw [card_union_of_disjoint dis,card_erase_of_mem ya,card_erase_of_mem (mem_Omit.mpr xo)] at n
    omega
  obtain ⟨w,wm⟩ := meet
  have wa : w∈A := (mem_inter.mp wm).1
  have wb : w∈B := (mem_inter.mp wm).2
  have wo := mem_Omit.mp (mem_inter.mp wa).2
  have xw := (mem_neighborFinset _ _ _).mp (mem_inter.mp wa).1
  have yw := (mem_neighborFinset _ _ _).mp (mem_inter.mp wb).1
  let q := Walk.cons xw (Walk.cons yw.symm Walk.nil)
  have qp : q.IsPath := by
    rw [isPath_def]
    simp [q,support_cons,xw.ne,yw.ne,yw.ne.symm,xy]
  refine ⟨q,qp,by simp [q],?_⟩
  intro v vv he
  have hv : v=x ∨ v=w ∨ v=y := by simpa [q,support_cons] using vv
  rcases hv with rfl|rfl|rfl
  · exact xo he
  · exact wo he
  · exact yo he

theorem high_sites_separated_seven (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (size : (Omit p).card≤7) :
    ∀ i∈Sites p (HighOmit p),i+1∉Sites p (HighOmit p) := by
  intro i im jm
  obtain ⟨ir,x,xm,xe⟩ := mem_filter.mp im
  obtain ⟨jr,y,ym,ye⟩ := mem_filter.mp jm
  have xp : i∈Pins p x := mem_filter.mpr ⟨ir,xe⟩
  have yp : i+1∈Pins p y := mem_filter.mpr ⟨jr,ye⟩
  by_cases eq : x=y
  · subst y
    exact pin_indices_not_consecutive hp (highOmit_data xm).1 xp yp
  obtain ⟨q,qp,ql,off⟩ := high_omitted_short_join_seven hc conn cap hp size xm ym eq
  have n := gap_three_of_linked_pins hp xp yp (by omega) q qp ql off
  omega

#print axioms high_omitted_short_join_seven
#print axioms high_sites_separated_seven
end Graffiti189LongestPath.SixThreeTwentyOne
