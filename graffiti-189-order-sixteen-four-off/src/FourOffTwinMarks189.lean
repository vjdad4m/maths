import FourOffTwinRows189
import FourOffGraphCore189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {p : G.Walk a b} {x : V}
open private no_endpoints dist_two pin_data pin_of_neighbor_mem pin_pos mem_distanceTwo card_pinVertices cardinal_flankVertices LeftMarks RightMarks card_leftMarks card_rightMarks same_support_optimal reverse_long reverse_pin mark_length degree_off_bound two_flanks_full second_pin_no_start_of_high from SmallOrderFour189
open private hamilton_of_labeled_chain order_sixteen_four_off_labeling length_eleven_left_block_of_small_path_d2 left_boundary_porters_at_most_two right_boundary_porters_at_most_two from FourOffGraphCore189
open private mark_holes_of_pin_and_missing_endpoint from FourOffGraphSupport189

open OffFour16Twin in
private theorem order_sixteen_four_off_mixed_marks
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=11)
    (xo : x∉p.support) {j : ℕ} (h1 : 1∈Pins p x) (jlo : 4≤j) (jhi : j≤9)
    (hole1 : 1∉LeftMarks p∪RightMarks p) (holep : j-1∉LeftMarks p∪RightMarks p)
    (holej : j∉LeftMarks p∪RightMarks p) :
    ∃ m : Marks, m 0=1 ∧ m 10=2 ∧
      (∀ k : Fin 11,Hole 1 j k.val → m k=0) ∧
      (∀ k : Fin 11,¬Hole 1 j k.val → m k≠0) ∧
      markCount m 1=4 ∧ markCount m 2=4 ∧
      (∀ k : Fin 11,m k=1 ↔ G.Adj a (p.getVert (k.val+1))) ∧
      (∀ k : Fin 11,m k=2 ↔ G.Adj b (p.getVert k.val)) := by
  classical
  let T : Finset ℕ := {1,j-1,j}
  have tc : T.card=3 := by
    have ne1 : 1∉({j-1,j}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have ne2 : j-1∉({j}:Finset ℕ) := by simp only [mem_singleton]; omega
    rw [show T={1,j-1,j} from rfl,card_insert_of_not_mem ne1,card_insert_of_not_mem ne2,card_singleton]
  have mt {k : ℕ} : k∈T ↔ Hole 1 j k := by simp [T,Hole]
  have ts : T⊆range p.length := by
    intro k km
    have v := mt.mp km
    simp only [Hole] at v
    rcases v with rfl|rfl|rfl <;> exact mem_range.mpr (by omega)
  have tv {k : ℕ} (ki : k∈T) : k∉LeftMarks p∪RightMarks p := by
    have e := mt.mp ki
    simp only [Hole] at e
    rcases e with rfl|rfl|rfl <;> assumption
  have td : Disjoint (LeftMarks p∪RightMarks p) T :=
    disjoint_left.mpr (fun _ h m => tv m h)
  have degreeSum := mark_length hp xo (p.getVert_mem_support 1) (pin_data h1).2 T ts td
  have exactL : G.degree a=4 := by omega
  have exactR : G.degree b=4 := by omega
  have all {k : ℕ} (kr : k<p.length) (no : k∉T) : k∈LeftMarks p∪RightMarks p := by
    by_contra z
    have dep : Disjoint (LeftMarks p∪RightMarks p) (insert k T) :=
      disjoint_left.mpr (fun w h m => (mem_insert.mp m).elim
        (fun e => z (e ▸ h)) (fun e => tv e h))
    have sub : insert k T⊆range p.length := insert_subset (mem_range.mpr kr) ts
    have bd := mark_length hp xo (p.getVert_mem_support 1) (pin_data h1).2 _ sub dep
    rw [card_insert_of_not_mem no] at bd
    omega
  have e : ∀ k<p.length, ¬(G.Adj a (p.getVert (k+1)) ∧ G.Adj b (p.getVert k)) := by
    intro k kr h
    exact not_adj_both_end_marks hp xo (p.getVert_mem_support 1) (pin_data h1).2 kr h.1 h.2
  let m : Marks := fun k => if G.Adj a (p.getVert (k.val+1)) then 1
    else if G.Adj b (p.getVert k.val) then 2 else 0
  have l (k : Fin 11) : m k=1 ↔ G.Adj a (p.getVert (k.val+1)) := by
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · simp [m,h]
    · by_cases r : G.Adj b (p.getVert k.val) <;> simp [m,h,r]
  have r (k : Fin 11) : m k=2 ↔ G.Adj b (p.getVert k.val) := by
    have kb := k.isLt
    by_cases h : G.Adj a (p.getVert (k.val+1))
    · have no : ¬G.Adj b (p.getVert k.val) := fun n => e _ (by omega) ⟨h,n⟩
      simp [m,h,no]
    · by_cases s : G.Adj b (p.getVert k.val) <;> simp [m,h,s]
  have zero (k : Fin 11) : m k=0 ↔ k.val∉LeftMarks p∪RightMarks p := by
    have kr : k.val<p.length := by have ee := k.isLt; omega
    have km : k.val∈range p.length := mem_range.mpr kr
    by_cases al : G.Adj a (p.getVert (k.val+1)) <;>
      by_cases br : G.Adj b (p.getVert k.val) <;> simp [m,al,br,LeftMarks,RightMarks,km]
  have m0 : m 0=1 := (l 0).mpr (by simpa using p.adj_getVert_succ (i:=0) (by omega))
  have m10 : m 10=2 := (r 10).mpr (by
    have rr := (p.adj_getVert_succ (i:=10) (by omega)).symm
    rw [show 10+1=p.length by omega,p.getVert_length] at rr
    exact rr)
  refine ⟨m,m0,m10,fun k h => (zero k).mpr (tv (mt.mpr h)),?_,?_,?_,l,r⟩
  · intro k h km
    exact (zero k).mp km (all (by have zz := k.isLt; omega) (fun e => h (mt.mp e)))
  · unfold markCount
    let N := univ.filter (fun k : Fin 11 => m k=1)
    have eq : N.image Fin.val=LeftMarks p := by
      ext n
      constructor
      · rintro H
        obtain ⟨k,km,rfl⟩ := mem_image.mp H
        exact mem_filter.mpr ⟨mem_range.mpr (by have g := k.isLt; omega), (l k).mp (mem_filter.mp km).2⟩
      · intro nm
        have nb := mem_range.mp (mem_filter.mp nm).1
        exact mem_image.mpr ⟨⟨n,by omega⟩,mem_filter.mpr ⟨mem_univ _,(l ⟨n,by omega⟩).mpr (mem_filter.mp nm).2⟩,rfl⟩
    have ce : (N.image Fin.val).card=N.card := card_image_iff.mpr (fun _ _ _ _ e => Fin.ext e)
    change N.card=4
    rw [←ce,eq,card_leftMarks hp,exactL]
  · unfold markCount
    let N := univ.filter (fun k : Fin 11 => m k=2)
    have eq : N.image Fin.val=RightMarks p := by
      ext n
      constructor
      · rintro H
        obtain ⟨k,km,rfl⟩ := mem_image.mp H
        exact mem_filter.mpr ⟨mem_range.mpr (by have g := k.isLt; omega),(r k).mp (mem_filter.mp km).2⟩
      · intro nm
        have nb := mem_range.mp (mem_filter.mp nm).1
        exact mem_image.mpr ⟨⟨n,by omega⟩,mem_filter.mpr ⟨mem_univ _,(r ⟨n,by omega⟩).mpr (mem_filter.mp nm).2⟩,rfl⟩
    have ce : (N.image Fin.val).card=N.card := card_image_iff.mpr (fun _ _ _ _ e => Fin.ext e)
    change N.card=4
    rw [←ce,eq,card_rightMarks hp,exactR]

#print axioms order_sixteen_four_off_mixed_marks

end Graffiti189LongestPath.TwoCut.SmallOrderFour
