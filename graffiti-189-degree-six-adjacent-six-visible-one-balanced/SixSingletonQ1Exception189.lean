import SixSingletonQ1Splice189
import SixSingletonQ1Inactive189
import SixRootAvoidTwo189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair
open private Cmp from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common strictA strictB from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
open PortCertificates (marks)
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s z : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false

private theorem q1_strict_avoid_balance (bal : nearBal D={z}) :
    z∉strictA D ∧ z∉strictB D := by
  have w : z∈nearBal D := by rw [bal]; simp
  have e := (mem_filter.mp (mem_filter.mp w).1).2
  exact ⟨fun u=>Nat.ne_of_lt (mem_filter.mp u).2 e,fun u=>Nat.ne_of_lt (mem_filter.mp u).2 e.symm⟩

theorem q1_right_pair_route (F : SixVisibleData G D s) (bal : nearBal D={z})
    (ea : (EA D).card≤2) (eb : (EB D).card≤2)
    (l2 : (strictA D).card=2) (right : (strictB D).Nonempty) :
    ∃ u∈strictB D,∃ v∈strictB D,RouteOn G ((Dark D).erase z) u v := by
  classical
  obtain ⟨u,ur⟩ := right
  let J := (Dark D).erase z
  have uJ : u∈J := mem_erase.mpr ⟨fun e=>(q1_strict_avoid_balance bal).2 (e ▸ ur),
    (q1_dark_parts_subsets F).2.1 ur⟩
  obtain ⟨size,deg⟩ := six_q1_core_bounds F bal ea eb
  obtain ⟨v,vJ,p⟩ := rooted_side_route (G:=G) J uJ (fun i hi j hj _ _=>by
    have a := deg i hi
    have b := deg j hj
    dsimp only [J]
    omega)
  have on (w : V) (wJ : w∈J) : w∈strictA D ∨ w∈strictB D := by
    have ⟨ne,d⟩ := mem_erase.mp wJ
    rw [←F.darkPart,bal,mem_union,mem_singleton] at d
    exact mem_union.mp (d.resolve_right ne)
  by_cases vr : v∈strictB D
  · exact ⟨u,ur,v,vr,p.reverse⟩
  have vl := (on v vJ).resolve_right vr
  obtain ⟨x,y,xy,eq⟩ := card_eq_two.mp l2
  have vx : v=x ∨ v=y := by simpa only [eq,mem_insert,mem_singleton] using vl
  let avoid := if v=x then y else x
  have avoid_l : avoid∈strictA D := by rw [eq]; by_cases h:v=x <;> simp [avoid,h]
  have avoid_J : avoid∈J := mem_erase.mpr ⟨fun e=>(q1_strict_avoid_balance bal).1 (e ▸ avoid_l),
    (q1_dark_parts_subsets F).1 avoid_l⟩
  obtain ⟨w,wJ,wv,wa,route⟩ := route_avoid_two_free J p.reverse avoid_J (deg v vJ)
  have noL : w∉strictA D := by
    rw [eq,mem_insert,mem_singleton]
    rcases vx with h|h
    · simp [avoid,h] at wv wa
      exact fun e=>e.elim wv wa
    · have ne : v≠x := fun f=>xy (f.symm.trans h)
      simp [avoid,ne,h,xy.symm] at wv wa
      exact fun e=>e.elim wa wv
  exact ⟨u,ur,w,(on w wJ).resolve_left noL,route⟩

theorem q1_exception_right_links (F : SixVisibleData G D s) (bal : nearBal D={z})
    (r4 : (strictB D).card=4) {y : V} (yb : y∈EB D) (iso : inside G (Vis D) y=∅) :
    ∀ w∈strictB D,G.Adj y w := by
  let R := insert b (insert z (strictB D))
  have cover : G.neighborFinset y⊆R := by
    intro w hw
    have k := F.bBound y yb hw
    rw [iso,empty_union,bal] at k
    rcases mem_insert.mp k with e|k
    · exact mem_insert.mpr (.inl e)
    apply mem_insert_of_mem
    rcases mem_union.mp k with u|v
    · exact mem_insert_of_mem (mem_filter.mp u).1
    exact mem_insert.mpr (.inl (mem_singleton.mp (mem_filter.mp v).1))
  have cap : R.card≤6 := by
    have k := card_insert_le z (strictB D)
    have h := card_insert_le b (insert z (strictB D))
    dsimp [R]
    omega
  have lo := F.highEB y yb
  have eq : G.neighborFinset y=R := by
    apply eq_of_subset_of_card_le cover
    rw [card_neighborFinset_eq_degree]
    omega
  intro w wr
  exact (mem_neighborFinset _ _ _).mp (eq.symm ▸ mem_insert_of_mem (mem_insert_of_mem wr))

theorem q1_exception_common_link (F : SixVisibleData G D s) (bal : nearBal D={z})
    (v6 : (Vis D).card=6)
    {c y y' : V} (cc : c∈Common D) (cv : c∈Vis D) (yv : y∈Vis D) (yv' : y'∈Vis D)
    (cy : c≠y) (cy' : c≠y') (yy' : y≠y') (dj : ¬G.Adj c y) (dj' : ¬G.Adj c y') :
    G.Adj c z := by
  by_contra no
  have h := six_q1_common_slots F bal cc
  simp [marks,no] at h
  exact (visible_four_forces_either (Vis D) v6 cv yv yv' cy cy' yy' h).elim dj dj'

#print axioms q1_right_pair_route
#print axioms q1_exception_right_links
#print axioms q1_exception_common_link
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
