import SixTripleCutTwoUniversal189
import SixTripleCutHall189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_ranks_eq_sum_ports from SixTripleCutUniversalPort189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible from SixTripleCutNonSingletonIsolate189

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.rank_sum_le_six from SixTripleCutForeignHigh189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.every_rank_two_of_full from SixTripleCutForeignHigh189

theorem no_three_shores_with_high_port_of_universal
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    {S A B C : Finset V} (ss : S.card=3)
    (shA : Shore G S A) (shB : Shore G S B) (shC : Shore G S C)
    (cC : (G.induce (↑C : Set V)).Connected)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (a4 : 4≤A.card) (b4 : 4≤B.card) (c4 : 4≤C.card)
    (ah : ∀ t∈S, ∃ w∈ports G A t, 6≤G.degree w)
    (bh : ∀ t∈S, ∃ w∈ports G B t, 6≤G.degree w)
    (ra : ∀ y∈A,rank G S y≤2) (rb : ∀ y∈B,rank G S y≤2)
    {x : V} (xc : x∈C) (ux : ∀ t∈S,G.Adj x t) : False := by
  classical
  let pa (t : V) := (ports G A t).card
  let pb (t : V) := (ports G B t).card
  let qa (t : V) := (localTwo G A t).card
  let qb (t : V) := (localTwo G B t).card
  let qc (t : V) := (localTwo G C t).card
  have va3 := shA.visible_lower ss conn (by omega)
  have vb3 := shB.visible_lower ss conn (by omega)
  obtain ⟨va,vb,insideC⟩ := universal_port_saturates_other_shores hc cap shC cC shA shB
    ac.symm bc.symm ab va3 vb3 xc ux
  have portsA : (∑ t∈S,pa t)≤6 := Graffiti189LongestPath.ThresholdSix.ThreeCut.rank_sum_le_six va ra
  have portsB : (∑ t∈S,pb t)≤6 := Graffiti189LongestPath.ThresholdSix.ThreeCut.rank_sum_le_six vb rb
  have charge {W : Finset V}
      (sh : Shore G S W) (high : ∀ t∈S, ∃ w∈ports G W t, 6≤G.degree w)
      (two : ∀ y∈W,rank G S y≤2) :
      15≤(∑ t∈S,(ports G W t).card)+(∑ t∈S,(localTwo G W t).card) := by
    have a := sum_le_sum (s:=S) (f:=fun _=>(5:Nat))
      (g:=fun t=>(ports G W t).card+(localTwo G W t).card) (by
        intro t ts
        obtain ⟨u,um,l⟩ := high t ts
        have r := sh.port_cost_rank hc ts um
        have s:=two u (mem_filter.mp um).1
        change 5≤(ports G W t).card+(localTwo G W t).card
        omega)
    have b : (∑ _∈S,(5:Nat))=15 := by simp [ss]
    rw [sum_add_distrib,b] at a
    exact a
  have chA : 15≤(∑ t∈S,pa t)+(∑ t∈S,qa t) := charge shA ah ra
  have chB : 15≤(∑ t∈S,pb t)+(∑ t∈S,qb t) := charge shB bh rb
  have qbnd := sum_le_sum (s:=S) (f:=fun t=>qa t+qb t+qc t) (g:=fun _=>(6:Nat))
    (fun t _ => three_local_twos_le_six cap ab ac bc t)
  have ff : (∑ _∈S,(6:Nat))=18 := by simp [ss]
  rw [sum_add_distrib,sum_add_distrib,ff] at qbnd
  change (∑ t∈S,qa t)+(∑ t∈S,qb t)+(∑ t∈S,qc t)≤18 at qbnd
  have pA6 : (∑ t∈S,(ports G A t).card)=6 := by
    change (∑ t∈S,pa t)=6
    omega
  have pB6 : (∑ t∈S,(ports G B t).card)=6 := by
    change (∑ t∈S,pb t)=6
    omega
  have qc_0 (t : V) (ts : t∈S) : qc t=0 := by
    have h := Finset.single_le_sum (f:=qc) (fun _ _=>Nat.zero_le _) ts
    change qc t≤(∑ j∈S,qc j) at h
    omega
  have cPorts (t : V) (ts : t∈S) : ports G C t=C := by
    have eq := shore_card_of_universal_inside hc shC xc ux insideC ts
    have h := qc_0 t ts
    change (localTwo G C t).card=0 at h
    rw [h,add_zero] at eq
    exact eq_of_subset_of_card_le (filter_subset _ _) eq.le
  have ra' := Graffiti189LongestPath.ThresholdSix.ThreeCut.every_rank_two_of_full va ra pA6
  have rb' := Graffiti189LongestPath.ThresholdSix.ThreeCut.every_rank_two_of_full vb rb pB6
  obtain ⟨u,um⟩ := card_pos.mp (show 0<(visible G S A).card by omega)
  obtain ⟨ua,t,ts,ut⟩ := mem_filter.mp um
  have cSub : C⊆DistanceTwo G u := by
    intro z zm
    have zp : z∈ports G C t := by rw [cPorts t ts]; exact zm
    exact shA.foreign_distance_two shC ac hc (mem_filter.mpr ⟨ua,ut.symm⟩) zp
  have bSub : visible G S B⊆DistanceTwo G u := by
    intro z zm
    let U := S.filter (G.Adj u)
    let T := S.filter (G.Adj z)
    have ur : U.card=2 := ra' u um
    have zr : T.card=2 := rb' z zm
    have h := card_le_card (show U∪T⊆S from union_subset (filter_subset _ _) (filter_subset _ _))
    have s:=card_union_add_card_inter U T
    have i : 0<(U∩T).card := by omega
    obtain ⟨a,am⟩ := card_pos.mp i
    obtain ⟨au,az⟩ := mem_inter.mp am
    have zb := (mem_filter.mp zm).1
    exact shA.foreign_distance_two shB ab hc
      (mem_filter.mpr ⟨ua,(mem_filter.mp au).2.symm⟩) (mem_filter.mpr ⟨zb,(mem_filter.mp az).2.symm⟩)
  have se : Disjoint C (visible G S B) := bc.symm.mono_right (filter_subset _ _)
  have up := (card_le_card (union_subset cSub bSub)).trans (distanceTwo_le_of_even 6 u (cap u))
  rw [card_union_of_disjoint se,vb] at up
  omega

#print axioms no_three_shores_with_high_port_of_universal
end Graffiti189LongestPath.ThresholdSix.ThreeCut
