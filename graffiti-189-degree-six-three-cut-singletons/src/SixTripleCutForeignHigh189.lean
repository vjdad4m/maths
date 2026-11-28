import SixTripleCutIsolateComplete189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_ranks_eq_sum_ports from SixTripleCutUniversalPort189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible from SixTripleCutNonSingletonIsolate189

theorem three_local_twos_le_six
    (cap : ∀ v,(EvenFrom G v).card≤7)
    {A B C : Finset V} (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C) (t : V) :
    (localTwo G A t).card+(localTwo G B t).card+(localTwo G C t).card≤6 := by
  let P := localTwo G A t
  let Q := localTwo G B t
  let R := localTwo G C t
  have pq : Disjoint P Q := ab.mono inter_subset_left inter_subset_left
  have pr : Disjoint P R := ac.mono inter_subset_left inter_subset_left
  have qr : Disjoint Q R := bc.mono inter_subset_left inter_subset_left
  have incl : P∪Q∪R⊆DistanceTwo G t := union_subset
    (union_subset inter_subset_right inter_subset_right) inter_subset_right
  have l := (card_le_card incl).trans (distanceTwo_le_of_even 6 t (cap t))
  rwa [card_union_of_disjoint (disjoint_union_left.mpr ⟨pr,qr⟩),card_union_of_disjoint pq] at l

private theorem rank_visible_sum {S W : Finset V} :
    (∑ x∈visible G S W,rank G S x) = ∑ x∈W,rank G S x := by
  classical
  apply sum_subset (show visible G S W⊆W from filter_subset _ _)
  intro x xw xnot
  unfold rank
  rw [filter_eq_empty_iff.mpr (fun a am h=>xnot (mem_filter.mpr ⟨xw,a,am,h⟩)),card_empty]

private theorem rank_sum_le_six {S W : Finset V}
    (three : (visible G S W).card=3) (rank2 : ∀ x∈W, rank G S x≤2) :
    (∑ t∈S,(ports G W t).card)≤6 := by
  classical
  have a := sum_le_sum (s:=visible G S W) (f:=rank G S) (g:=fun _=>(2:Nat))
    (fun x xm=>rank2 x (mem_filter.mp xm).1)
  have b : (∑ _x∈visible G S W,(2:Nat))=6 := by simp [three]
  rw [rank_visible_sum,b,Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_ranks_eq_sum_ports S W] at a
  exact a

private theorem every_rank_two_of_full {S W : Finset V}
    (three : (visible G S W).card=3) (rank2 : ∀ x∈W,rank G S x≤2)
    (full : (∑ t∈S,(ports G W t).card)=6) : ∀ x∈visible G S W,rank G S x=2 := by
  classical
  intro x xm
  let J := (visible G S W).erase x
  have js : J.card=2 := by dsimp [J]; rw [card_erase_of_mem xm,three]
  have bound := sum_le_sum (s:=J) (f:=rank G S) (g:=fun _=>(2:Nat))
    (fun w wm=>rank2 w (mem_filter.mp (mem_erase.mp wm).2).1)
  have b : (∑ _∈J,(2:Nat))=4 := by simp [js]
  rw [b] at bound
  have tot := sum_erase_add (visible G S W) (rank G S) xm
  rw [rank_visible_sum,Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_ranks_eq_sum_ports S W,full] at tot
  have r := rank2 x (mem_filter.mp xm).1
  change (∑ t∈J,rank G S t)+rank G S x=6 at tot
  change (∑ t∈J,rank G S t)≤4 at bound
  omega

/-- A nonsingleton three-shore cut with a universal port cannot have
all shore vertices high. This applies regardless
of how many edges the cut itself induces. -/
theorem no_three_shores_with_high_foreign_of_universal
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    {S A B C : Finset V} (ss : S.card=3)
    (shA : Shore G S A) (shB : Shore G S B) (shC : Shore G S C)
    (cA : (G.induce (↑A : Set V)).Connected) (cB : (G.induce (↑B : Set V)).Connected)
    (cC : (G.induce (↑C : Set V)).Connected)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (a4 : 4≤A.card) (b4 : 4≤B.card) (c4 : 4≤C.card)
    (ah : ∀ w∈A,6≤G.degree w) (bh : ∀ w∈B,6≤G.degree w) (ch : ∀ w∈C,6≤G.degree w)
    {x : V} (xc : x∈C) (ux : ∀ t∈S,G.Adj x t) : False := by
  classical
  let pa (t : V) := (ports G A t).card
  let pb (t : V) := (ports G B t).card
  let qa (t : V) := (localTwo G A t).card
  let qb (t : V) := (localTwo G B t).card
  let qc (t : V) := (localTwo G C t).card
  have va3 := shA.visible_lower ss conn (by omega)
  have vb3 := shB.visible_lower ss conn (by omega)
  have vc3 := shC.visible_lower ss conn (by omega)
  obtain ⟨va,vb,insideC⟩ := universal_port_saturates_other_shores hc cap shC cC shA shB
    ac.symm bc.symm ab va3 vb3 xc ux
  have noUniv {W Z : Finset V}
      (shW : Shore G S W) (shZ : Shore G S Z)
      (cW : (G.induce (↑W : Set V)).Connected)
      (wz : Disjoint W Z) (wc : Disjoint W C) (zc : Disjoint Z C)
      (vw : (visible G S W).card=3) (vz : 3≤(visible G S Z).card)
      (w4 : 4≤W.card) (highW : ∀ u∈W,6≤G.degree u) :
      ∀ y∈W,∃ z∈S,¬G.Adj y z := by
    intro y ym
    by_cases miss : ∃ z∈S,¬G.Adj y z
    · exact miss
    exfalso
    have uy (t : V) (ts : t∈S) : G.Adj y t := by
      by_cases h : G.Adj y t
      · exact h
      exfalso
      exact miss ⟨t,ts,h⟩
    obtain ⟨t,ts⟩ := card_pos.mp (show 0<S.card by omega)
    obtain ⟨_,vc,insideW⟩ := universal_port_saturates_other_shores hc cap shW cW shZ shC
      wz wc zc vz vc3 ym uy
    have eW := shore_card_of_universal_inside hc shW ym uy insideW ts
    have eC := shore_card_of_universal_inside hc shC xc ux insideC ts
    have pc := card_le_card (Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible (G:=G) (W:=C) ts)
    have pw := card_le_card (Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible (G:=G) (W:=W) ts)
    have nC := seven_of_three_visible_and_all_high shC c4 vc ch
    have nW := seven_of_three_visible_and_all_high shW w4 vw highW
    have far := three_local_twos_le_six cap wz wc zc t
    omega
  have ra (y : V) (ym : y∈A) : rank G S y≤2 := by
    obtain ⟨z,zs,nz⟩ := noUniv shA shB cA ab ac bc va vb3 a4 ah y ym
    exact rank_le_two_of_missing ss zs nz
  have rb (y : V) (ym : y∈B) : rank G S y≤2 := by
    obtain ⟨z,zs,nz⟩ := noUniv shB shA cB ab.symm bc ac vb va3 b4 bh y ym
    exact rank_le_two_of_missing ss zs nz
  have portsA : (∑ t∈S,pa t)≤6 := rank_sum_le_six va ra
  have portsB : (∑ t∈S,pb t)≤6 := rank_sum_le_six vb rb
  have charge {W : Finset V}
      (sh : Shore G S W) (high : ∀ w∈W,6≤G.degree w)
      (two : ∀ y∈W,rank G S y≤2) :
      15≤(∑ t∈S,(ports G W t).card)+(∑ t∈S,(localTwo G W t).card) := by
    have a := sum_le_sum (s:=S) (f:=fun _=>(5:Nat))
      (g:=fun t=>(ports G W t).card+(localTwo G W t).card) (by
        intro t ts
        obtain ⟨u,um,tu⟩ := sh.hit ss conn ts
        have r := sh.port_cost_rank hc ts (mem_filter.mpr ⟨um,tu⟩)
        have l:=high u um
        have s:=two u um
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
  have ra' := every_rank_two_of_full va ra pA6
  have rb' := every_rank_two_of_full vb rb pB6
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

#print axioms no_three_shores_with_high_foreign_of_universal
end Graffiti189LongestPath.ThresholdSix.ThreeCut
