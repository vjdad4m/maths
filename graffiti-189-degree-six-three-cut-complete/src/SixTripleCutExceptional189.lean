import SixTripleCutBadBudget189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.rank_sum_le_six from SixTripleCutForeignHigh189

theorem exceptional_port_geometry
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S A B C : Finset V} (ss : S.card=3)
    (shA : Shore G S A) (shB : Shore G S B) (shC : Shore G S C)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (a4 : 4≤A.card)
    (va : (visible G S A).card=3) (vb : (visible G S B).card=3)
    (ra : ∀ y∈A,rank G S y≤2) (rb : ∀ y∈B,rank G S y≤2)
    {x t : V} (xc : x∈C) (ux : ∀ u∈S,G.Adj x u)
    (insideC : ∀ w∈C,w=x∨G.Adj x w) (ts : t∈S)
    (bad : ¬ ∃ w∈ports G A t,6≤G.degree w) :
    ∃ l∈A, G.Adj t l ∧ G.degree l<6 ∧ ports G A t={l} ∧
      (∀ u∈S,u≠t → ∃ w∈ports G A u,6≤G.degree w) ∧
      1≤(localTwo G A t).card ∧ (∑ u∈S,(localTwo G C u).card)≤3 ∧ C.card≤6 := by
  classical
  obtain ⟨l,lm,tl⟩ := shA.hit ss conn ts
  have lLow : G.degree l < 6 := Nat.lt_of_not_ge (fun h=>bad ⟨l,mem_filter.mpr ⟨lm,tl⟩,h⟩)
  have highAway (w : V) (nw : w≠l) : 6≤G.degree w :=
    (degree w l nw).resolve_right (Nat.not_le_of_lt lLow)
  have sole : ports G A t={l} := by
    apply subset_antisymm
    · intro w wm
      apply mem_singleton.mpr
      by_cases h : w=l
      · exact h
      exact False.elim (bad ⟨w,wm,highAway w h⟩)
    · rw [singleton_subset_iff]
      exact mem_filter.mpr ⟨lm,tl⟩
  have goodA (u : V) (us : u∈S) (ut : u≠t) : ∃ w∈ports G A u,6≤G.degree w := by
    by_contra! no
    have only : ports G A u ⊆ ({l}:Finset V) := by
      intro w wm
      apply mem_singleton.mpr
      by_cases h : w=l
      · exact h
      exact False.elim (Nat.not_le_of_lt (no w wm) (highAway w h))
    have hall := shA.hall_two_terminals ss conn (show 2≤A.card by omega) ts us ut.symm
    have small := card_le_card (union_subset (show ports G A t⊆{l} by rw [sole]) only)
    rw [card_singleton] at small
    omega
  have n4 : 4≤Fintype.card V := a4.trans (by simpa using (card_le_card (subset_univ A)))
  have minl := Graffiti189LongestPath.FiveThreeHook.min_three_degree_of_small_deletion conn n4 l
  have li := shA.degree_eq_inner_add_rank lm
  have lr := ra l lm
  have pos : 0 < innerDegree G A l := by omega
  obtain ⟨z,zm⟩ := card_pos.mp pos
  have za := (mem_filter.mp zm).2
  have lz := (G.mem_neighborFinset ..).mp (mem_filter.mp zm).1
  have tz : ¬G.Adj t z := by
    intro tz
    have hz : z∈ports G A t := mem_filter.mpr ⟨za,tz⟩
    rw [sole,mem_singleton] at hz
    exact lz.ne.symm hz
  have az : z∈localTwo G A t := mem_inter.mpr ⟨za,two_of_common hc
    (fun eq=>disjoint_left.mp shA.disjoint za (eq ▸ ts)) tz tl lz⟩
  have qa : 1≤(localTwo G A t).card := card_pos.mpr ⟨z,az⟩
  have pa := Graffiti189LongestPath.ThresholdSix.ThreeCut.rank_sum_le_six va ra
  have pb := Graffiti189LongestPath.ThresholdSix.ThreeCut.rank_sum_le_six vb rb
  have charge {W : Finset V} (sh : Shore G S W) (rank2 : ∀ w∈W,rank G S w≤2)
      {u : V} (us : u∈S) (h : ∃ w∈ports G W u,6≤G.degree w) :
      5≤(ports G W u).card+(localTwo G W u).card := by
    obtain ⟨w,wm,wh⟩ := h
    have q := sh.port_cost_rank hc us wm
    have r := rank2 w (mem_filter.mp wm).1
    omega
  have bGood (u : V) (us : u∈S) : ∃ w∈ports G B u,6≤G.degree w := by
    obtain ⟨w,wm,uw⟩ := shB.hit ss conn us
    exact ⟨w,mem_filter.mpr ⟨wm,uw⟩,highAway w (fun e=>disjoint_left.mp ab lm (e ▸ wm))⟩
  have ft {W : Finset V} (sh : Shore G S W) (dw : Disjoint A W) :
      ports G W t ⊆ DistanceTwo G l := by
    intro z zm
    exact shA.foreign_distance_two sh dw hc (mem_filter.mpr ⟨lm,tl⟩) zm
  have pp := (card_le_card (union_subset (ft shB ab) (ft shC ac))).trans
    (distanceTwo_le_of_even 6 l (cap l))
  have dd : Disjoint (ports G B t) (ports G C t) := bc.mono (filter_subset _ _) (filter_subset _ _)
  rw [card_union_of_disjoint dd] at pp
  have ⟨budget,sz⟩ := exceptional_port_charge (pC:=fun u=>(ports G C u).card) ss ts pa pb
    (show (ports G A t).card=1 by rw [sole,card_singleton]) qa
    (fun u us ut=>charge shA ra us (goodA u us ut))
    (fun u us=>charge shB rb us (bGood u us))
    (fun u _=>three_local_twos_le_six cap ab ac bc u) pp
  rw [←shore_card_of_universal_inside hc shC xc ux insideC ts] at sz
  exact ⟨l,lm,tl,lLow,sole,goodA,qa,budget,sz⟩

#print axioms exceptional_port_geometry
end Graffiti189LongestPath.ThresholdSix.ThreeCut
