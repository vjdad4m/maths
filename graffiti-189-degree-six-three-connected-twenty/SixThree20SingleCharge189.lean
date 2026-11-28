import SixThree20SingleProfile189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit high_filter_card)
open Graffiti189LongestPath.SixThreeNineteen (degree_covered_by_pins_and_omitted)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.mem_distanceTwo from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.dist_two from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem single_port_candidate_hit_cap (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (xm : x∈HighOmit p) (single : (Pins p x).card=1)
    (univ : ∀ y,y∉p.support → x≠y → G.Adj x y)
    {i j k : ℕ} (ip : i∈Pins p x) (js : j∈Sites p (HighOmit p)) (ks : k∈Sites p (HighOmit p))
    (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    ((CandHigh p).filter (fun v=>G.Adj v (p.getVert i))).card≤4 := by
  classical
  have xo := (highOmit_data xm).1
  have each (j : ℕ) (js : j∈Sites p (HighOmit p)) (ij : i≠j) :
      p.getVert j∈DistanceTwo G x := by
    obtain ⟨jr,y,yh,yj⟩ := mem_filter.mp js
    have no : ¬G.Adj x (p.getVert j) := by
      intro h
      have jp : j∈Pins p x := mem_filter.mpr ⟨jr,h⟩
      exact ij (card_le_one.mp (by omega : (Pins p x).card≤1) i ip j jp)
    have xy : x≠y := fun e=>no (e.symm ▸ yj)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.Rigidity.dist_two hc
        (fun e=>xo (e.symm ▸ p.getVert_mem_support j)) no (univ y (highOmit_data yh).1 xy) yj)
  let H := (CandHigh p).filter (fun v=>G.Adj v (p.getVert i))
  let B : Finset V := {p.getVert j,p.getVert k}
  have bs : B⊆DistanceTwo G x := by
    intro v vm
    rcases mem_insert.mp vm with rfl|m
    · exact each j js ij
    rw [mem_singleton.mp m]
    exact each k ks ik
  have out (j : ℕ) (js : j∈Sites p (HighOmit p)) : p.getVert j∉CandHigh p := by
    intro m
    obtain ⟨jr,y,yh,yj⟩ := mem_filter.mp js
    exact cand_no_omitted_edge hp (mem_filter.mp m).1 (highOmit_data yh).1 yj
  have dis : Disjoint H B := by
    apply disjoint_left.mpr
    intro v vm bv
    rcases mem_insert.mp bv with rfl|m
    · exact out j js (mem_filter.mp vm).1
    rw [mem_singleton.mp m] at vm
    exact out k ks (mem_filter.mp vm).1
  have cs : H⊆DistanceTwo G x := by
    intro v vm
    obtain ⟨vh,vi⟩ := mem_filter.mp vm
    obtain ⟨w,q,hq,same,_,_⟩ := cand_rotated_path hp (mem_filter.mp vh).1
    have vh' : v∈p.support := (same v).mpr q.start_mem_support
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.Rigidity.dist_two hc
        (fun e=>xo (e.symm ▸ vh')) (cand_no_omitted_edge hp (mem_filter.mp vh).1 xo)
        (Graffiti189LongestPath.pin_data ip).2 vi.symm)
  have ne : p.getVert j≠p.getVert k := fun e=>jk
    (hp.1.getVert_injOn (mem_range.mp (mem_filter.mp js).1).le
      (mem_range.mp (mem_filter.mp ks).1).le e)
  have cb : B.card=2 := by simp [B,ne]
  have n := (card_le_card (union_subset cs bs)).trans (distanceTwo_le_of_even 6 x (cap x))
  rw [card_union_of_disjoint dis,cb] at n
  change H.card ≤ 4
  omega

theorem three_candidate_miss_contradiction (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (size : 6≤E.card) (z : V) (zm : z∈E) (u₁ u₂ u₃ : V)
    (hit₁ : (E.filter (fun v=>G.Adj v u₁)).card≤4)
    (hit₂ : (E.filter (fun v=>G.Adj v u₂)).card≤4)
    (hit₃ : (E.filter (fun v=>G.Adj v u₃)).card≤4)
    (all₁ : G.Adj z u₁) (all₂ : G.Adj z u₂) (all₃ : G.Adj z u₃)
    (p12 : ∀ v∈E,G.Adj v u₁ ∨ G.Adj v u₂)
    (p13 : ∀ v∈E,G.Adj v u₁ ∨ G.Adj v u₃)
    (p23 : ∀ v∈E,G.Adj v u₂ ∨ G.Adj v u₃) : False := by
  classical
  let A := E.filter (fun v=>¬G.Adj v u₁)
  let B := E.filter (fun v=>¬G.Adj v u₂)
  let C := E.filter (fun v=>¬G.Adj v u₃)
  have hA := filter_card_add_filter_neg_card_eq_card (s:=E) (fun v=>G.Adj v u₁)
  have hB := filter_card_add_filter_neg_card_eq_card (s:=E) (fun v=>G.Adj v u₂)
  have hC := filter_card_add_filter_neg_card_eq_card (s:=E) (fun v=>G.Adj v u₃)
  change _+A.card=E.card at hA
  change _+B.card=E.card at hB
  change _+C.card=E.card at hC
  have d12 : Disjoint A B := disjoint_left.mpr (fun v m n=>
    (p12 v (mem_filter.mp m).1).elim (mem_filter.mp m).2 (mem_filter.mp n).2)
  have d13 : Disjoint A C := disjoint_left.mpr (fun v m n=>
    (p13 v (mem_filter.mp m).1).elim (mem_filter.mp m).2 (mem_filter.mp n).2)
  have d23 : Disjoint B C := disjoint_left.mpr (fun v m n=>
    (p23 v (mem_filter.mp m).1).elim (mem_filter.mp m).2 (mem_filter.mp n).2)
  have s : (A∪B)∪C⊆E.erase z := by
    apply union_subset (union_subset ?_ ?_) ?_
    · intro v m
      exact mem_erase.mpr ⟨fun e=>(mem_filter.mp m).2 (e.symm ▸ all₁),(mem_filter.mp m).1⟩
    · intro v m
      exact mem_erase.mpr ⟨fun e=>(mem_filter.mp m).2 (e.symm ▸ all₂),(mem_filter.mp m).1⟩
    · intro v m
      exact mem_erase.mpr ⟨fun e=>(mem_filter.mp m).2 (e.symm ▸ all₃),(mem_filter.mp m).1⟩
  have n := card_le_card s
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨d13,d23⟩),
    card_union_of_disjoint d12,card_erase_of_mem zm] at n
  omega

#print axioms single_port_candidate_hit_cap
#print axioms three_candidate_miss_contradiction
end Graffiti189LongestPath.SixThreeTwenty
