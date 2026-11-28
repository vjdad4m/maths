import SixTripleCutExceptionalRank189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.degree_le_inside_add_rank from SixTripleCutUniversalPort189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.all_adj_of_no_internal_two from SixTripleCutIsolate189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible from SixTripleCutNonSingletonIsolate189

theorem no_exceptional_two_terminal_port
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    {S A B C : Finset V} (ss : S.card=3)
    (shA : Shore G S A) (shB : Shore G S B) (shC : Shore G S C)
    (cB : (G.induce (↑B : Set V)).Connected)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (b4 : 4≤B.card) (c4 : 4≤C.card)
    (va : (visible G S A).card=3) (vb : (visible G S B).card=3)
    (bh : ∀ w∈B,6≤G.degree w) (ch : ∀ w∈C,6≤G.degree w)
    (ra : ∀ w∈A,rank G S w≤2)
    {x l y z t u : V} (ux : ∀ w∈S,G.Adj x w)
    (insideC : ∀ w∈C,w=x∨G.Adj x w)
    (lm : l∈A) (tl : G.Adj t l) (low : G.degree l<6)
    (yt : y∈ports G B t) (yu : y∈ports G B u)
    (zu : z∈ports G A u) (zh : 6≤G.degree z)
    (ts : t∈S) (us : u∈S) (ut : u≠t)
    (budget : (∑ w∈S,(localTwo G C w).card)≤3) : False := by
  classical
  let H := C.filter (fun w=>G.Adj t w ∨ G.Adj u w)
  have reach : H⊆DistanceTwo G y := by
    intro w wm
    obtain ⟨wc,edge⟩ := mem_filter.mp wm
    exact edge.elim
      (fun h=>shB.foreign_distance_two shC bc hc yt (mem_filter.mpr ⟨wc,h⟩))
      (fun h=>shB.foreign_distance_two shC bc hc yu (mem_filter.mpr ⟨wc,h⟩))
  have lD := shB.foreign_distance_two shA ab.symm hc yt (mem_filter.mpr ⟨lm,tl⟩)
  have zD := shB.foreign_distance_two shA ab.symm hc yu zu
  have lz : l≠z := fun e=>Nat.not_le_of_lt low (e ▸ zh)
  have good : Disjoint ({l,z}:Finset V) H :=
    ac.mono (insert_subset_iff.mpr ⟨lm,singleton_subset_iff.mpr (mem_filter.mp zu).1⟩) (filter_subset _ _)
  have two : ({l,z}:Finset V).card=2 := by
    rw [card_insert_of_not_mem (by simpa using lz),card_singleton]
  have upper := (card_le_card (union_subset
    (show ({l,z}:Finset V)⊆DistanceTwo G y by simp [lD,zD,insert_subset_iff]) reach)).trans
    (distanceTwo_le_of_even 6 y (cap y))
  rw [card_union_of_disjoint good,two] at upper
  have misses {w j : V} (wc : w∈C) (js : j∈S) (nj : ¬G.Adj j w) :
      w∈localTwo G C j := by
    have nwx : w≠x := fun e=>nj (e ▸ (ux j js).symm)
    exact mem_inter.mpr ⟨wc,two_of_common hc
      (fun e=>disjoint_left.mp shC.disjoint wc (e ▸ js)) nj
      (ux j js).symm ((insideC w wc).resolve_left nwx)⟩
  have mT : C\H⊆localTwo G C t := by
    intro w wm
    obtain ⟨wc,no⟩ := mem_sdiff.mp wm
    exact misses wc ts (fun h=>no (mem_filter.mpr ⟨wc,Or.inl h⟩))
  have mU : C\H⊆localTwo G C u := by
    intro w wm
    obtain ⟨wc,no⟩ := mem_sdiff.mp wm
    exact misses wc us (fun h=>no (mem_filter.mpr ⟨wc,Or.inr h⟩))
  have tplusu : (localTwo G C t).card+(localTwo G C u).card≤3 := by
    let q : V→ℕ := fun j=>(localTwo G C j).card
    have small : ({t,u}:Finset V)⊆S := insert_subset_iff.mpr ⟨ts,singleton_subset_iff.mpr us⟩
    have h := sum_le_sum_of_subset_of_nonneg (f:=q) small (fun _ _ _=>Nat.zero_le _)
    rw [sum_insert (by simpa using ut.symm),sum_singleton] at h
    exact h.trans budget
  have mCard := card_sdiff_add_card_eq_card (show H⊆C from filter_subset _ _)
  have C5 : C.card≤5 := by
    have a := card_le_card mT
    have b := card_le_card mU
    omega
  have notBoth {w : V} (wc : w∈C) (missT : ¬G.Adj t w) (missU : ¬G.Adj u w) :
      rank G S w≤1 := by
    have h : S.filter (G.Adj w)⊆(S.erase t).erase u := by
      intro j jm
      obtain ⟨js,wj⟩ := mem_filter.mp jm
      exact mem_erase.mpr ⟨fun e=>missU (e ▸ wj.symm),
        mem_erase.mpr ⟨fun e=>missT (e ▸ wj.symm),js⟩⟩
    have le := card_le_card h
    rwa [card_erase_of_mem (mem_erase.mpr ⟨ut,us⟩),card_erase_of_mem ts,ss] at le
  have Hall : H=C := by
    apply eq_of_subset_of_card_le (filter_subset _ _)
    have all : C⊆H := by
      intro w wc
      apply mem_filter.mpr
      refine ⟨wc,?_⟩
      by_contra miss
      have r := notBoth wc (fun e=>miss (Or.inl e)) (fun e=>miss (Or.inr e))
      have d := Graffiti189LongestPath.ThresholdSix.ThreeCut.degree_le_inside_add_rank shC wc
      have h := ch w wc
      omega
    exact card_le_card all
  rw [Hall] at upper reach
  have cExact : C.card=4 := by omega
  have lowElse : ∀ w∈B,w∉DistanceTwo G y := by
    intro w wb wd
    have inner : ({l,z}:Finset V)∪C⊆DistanceTwo G y :=
      union_subset (by simp [lD,zD,insert_subset_iff]) reach
    have dis : Disjoint ({l,z}:Finset V) C :=
      ac.mono_left (insert_subset_iff.mpr ⟨lm,singleton_subset_iff.mpr (mem_filter.mp zu).1⟩)
    have no : w∉({l,z}:Finset V)∪C := by
      have lw : w≠l := fun e=>disjoint_left.mp ab lm (e ▸ wb)
      have zw : w≠z := fun e=>disjoint_left.mp ab (mem_filter.mp zu).1 (e ▸ wb)
      have cw : w∉C := fun h=>disjoint_left.mp bc wb h
      simp [lw,zw,cw]
    have cost := (card_le_card (insert_subset_iff.mpr ⟨wd,inner⟩)).trans
      (distanceTwo_le_of_even 6 y (cap y))
    rw [card_insert_of_not_mem no,card_union_of_disjoint dis,two,cExact] at cost
    omega
  have yb := (mem_filter.mp yt).1
  have unB := Graffiti189LongestPath.ThresholdSix.ThreeCut.all_adj_of_no_internal_two hc cB yb lowElse
  have nB := seven_of_three_visible_and_all_high shB b4 vb bh
  have coverB : B ⊆ ports G B u ∪ localTwo G B u := by
    intro w wb
    by_cases uw : G.Adj u w
    · exact mem_union_left _ (mem_filter.mpr ⟨wb,uw⟩)
    have wy : w≠y := fun e=>uw (e ▸ (mem_filter.mp yu).2)
    exact mem_union_right _ (mem_inter.mpr ⟨wb,two_of_common hc
      (fun e=>disjoint_left.mp shB.disjoint wb (e ▸ us)) uw
      (mem_filter.mp yu).2 ((unB w wb).resolve_left wy)⟩)
  have len := card_le_card coverB
  rw [card_union_of_disjoint (disjoint_ports_localTwo G B u)] at len
  have bu := card_le_card (Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible (G:=G) (W:=B) us)
  rw [vb] at bu
  have lim := three_local_twos_le_six cap ab ac bc u
  have pc := shA.port_cost_rank hc us zu
  have zr := ra z (mem_filter.mp zu).1
  have ua := Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible (G:=G) (W:=A) us
  have pA : (ports G A u).card=3 := by
    have le := card_le_card ua
    rw [va] at le
    omega
  have far : ports G A u⊆DistanceTwo G y :=
    fun _ w=>shB.foreign_distance_two shA ab.symm hc yu w
  have sep : Disjoint (ports G A u) C := ac.mono_left (filter_subset _ _)
  have final := (card_le_card (union_subset far reach)).trans (distanceTwo_le_of_even 6 y (cap y))
  rw [card_union_of_disjoint sep,pA,cExact] at final
  omega

#print axioms no_exceptional_two_terminal_port
end Graffiti189LongestPath.ThresholdSix.ThreeCut
