import SixSingletonFiveThreeLowBase189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 k3 p5 from SixSingletonFiveShallowRoute189
open private d2 from CrossSaturation189
open private c_not_s c_not_core core_two_from_port dark_core_five from SixSingletonFiveThreeBase189
open private common_order low_visible_three deep_hits_a_different_balance low_visible_port_cover
  from SixSingletonFiveThreeLowBase189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

private theorem p_disjoint_dark : Disjoint P D := by decide
private theorem k_disjoint_dark : Disjoint K D := by decide

private theorem slot_insert_three {A : Finset V} {c i j k : V}
    (sub : A⊆DistanceTwo G c) (it : i∈DistanceTwo G c) (jt : j∈DistanceTwo G c)
    (kt : k∈DistanceTwo G c)
    (off_i : i∉A) (off_j : j∉insert i A) (off_k : k∉insert j (insert i A)) :
    A.card+3≤(DistanceTwo G c).card := by
  have h := card_le_card (insert_subset kt (insert_subset jt (insert_subset it sub)))
  rw [card_insert_of_not_mem off_k,card_insert_of_not_mem off_j,card_insert_of_not_mem off_i] at h
  omega

private theorem low_misses_chain_ends_impossible {L R S : Finset V} {T z c m t : V}
    (F : ProfileThree G L R S T) (hc : G.Connected) (even : ∀ i,(EvenFrom G i).card≤7)
    (zW : z∈D\S) (zLow : (inside G D z).card≤3)
    (cm : G.Adj c m) (ct : c≠t) (ctNo : ¬G.Adj c t)
    (cK : c∈K) (_mK : m∈K) (tK : t∈K) (Ktag : ({c,m,t}:Finset V)=K)
    (zc : ¬G.Adj z c) (zt : ¬G.Adj z t) : False := by
  classical
  have zd := (mem_sdiff.mp zW).1
  have cover := low_visible_port_cover F zd zLow Ktag zc zt
  have zm := cover m (by simp)
  have zc2 : z∈DistanceTwo G c :=
    d2 hc (fun eq=>disjoint_left.mp k_disjoint_dark cK (eq.symm ▸ zd))
      (fun h=>zc h.symm) cm zm.symm
  have tc2 : t∈DistanceTwo G c := d2 hc ct ctNo (F.commonA c cK).symm (F.commonA t tK)
  have sc2 : s∈DistanceTwo G c :=
    d2 hc (fun e=>(by decide : s∉K) (e ▸ cK)) (c_not_s F cK) (F.commonA c cK).symm F.sa.symm
  have cap := distanceTwo_le_of_even 6 c (even c)
  have zs : z∉S := (mem_sdiff.mp zW).2
  have zns : z≠s := fun e=>(by decide : s∉D) (e ▸ zd)
  have tns : t≠s := fun e=>(by decide : s∉K) (e ▸ tK)
  have znt : z≠t := fun e=>disjoint_left.mp k_disjoint_dark tK (e ▸ zd)
  have slot {A : Finset V} (AS : A⊆S) (AD : A⊆DistanceTwo G c) :
      A.card+3≤(DistanceTwo G c).card := by
    apply slot_insert_three AD zc2 tc2 sc2
    · exact fun h=>zs (AS h)
    · intro h
      rcases mem_insert.mp h with e|a
      · exact znt e.symm
      exact disjoint_left.mp k_disjoint_dark tK (F.core_sub (AS a))
    · intro h
      rcases mem_insert.mp h with e|a
      · exact tns e.symm
      rcases mem_insert.mp a with e|a
      · exact zns e.symm
      exact (by decide : s∉D) (F.core_sub (AS a))
  have nb : ¬(G.Adj c x ∧ G.Adj c y) := by
    rintro ⟨cx,cy⟩
    have sub : L∪R⊆DistanceTwo G c := by
      intro v m
      rcases mem_union.mp m with l|r
      · exact core_two_from_port F hc cK (F.left_sub l) cx (F.xL _ l)
      exact core_two_from_port F hc cK (F.right_sub r) cy (F.yR _ r)
    have n := slot (union_subset F.left_sub F.right_sub) sub
    rw [card_union_of_disjoint F.apart,F.l2,F.r2] at n
    omega
  let N := (D\S).erase z
  have n2 : N.card=2 := by
    change ((D\S).erase z).card=2
    rw [card_erase_of_mem zW,F.balance]
  let u := if G.Adj c x then x else y
  have nbhd : G.neighborFinset c⊆insert a (insert b (insert u (insert m N))) := by
    intro v vm
    have cv := (mem_neighborFinset _ _ _).mp vm
    rcases mem_insert.mp (F.commonBounds c cK v cv) with b|b
    · exact mem_insert.mpr (.inl b)
    rcases mem_insert.mp b with b|b
    · exact mem_insert_of_mem (mem_insert.mpr (.inl b))
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    rcases mem_union.mp b with p|p
    · rcases mem_insert.mp p with p|p
      · exact mem_insert.mpr (.inl (p.trans (if_pos (p ▸ cv)).symm))
      rcases mem_insert.mp p with p|p
      · have nx : ¬G.Adj c x := fun cx=>nb ⟨cx,p ▸ cv⟩
        exact mem_insert.mpr (.inl (p.trans (if_neg nx).symm))
      rw [←Ktag,mem_insert,mem_insert,mem_singleton] at p
      rcases p with e|e|e
      · exact (cv.ne e.symm).elim
      · exact mem_insert_of_mem (mem_insert.mpr (.inl e))
      exact (ctNo (e ▸ cv)).elim
    refine mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨?_,p⟩))
    intro e
    exact zc (e ▸ cv.symm)
  have eq := eq_of_subset_of_card_le nbhd (by
    rw [card_neighborFinset_eq_degree]
    have a1 := card_insert_le a (insert b (insert u (insert m N)))
    have b1 := card_insert_le b (insert u (insert m N))
    have u1 := card_insert_le u (insert m N)
    have m1 := card_insert_le m N
    have h := F.commonHigh c cK
    omega)
  have hit : G.Adj c u := (mem_neighborFinset _ _ _).mp
    (eq.symm ▸ mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _)))
  obtain ⟨b',bN,bT⟩ := deep_hits_a_different_balance F zW
  have cb : G.Adj c b' := (mem_neighborFinset _ _ _).mp (eq.symm ▸
    mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem bN))))
  have cT2 := core_two_from_port F hc cK F.deepS cb bT
  have cone {U : Finset V} {op : V} (US : U⊆S) (U2 : U.card=2)
      (Tn : T∉U) (cp : ∀ j∈U,G.Adj c u ∧ G.Adj u j)
      (opP : op∈P) (opnK : op∉K) (opns : op≠s)
      (op2 : op∈DistanceTwo G c) : False := by
    have Dist : U⊆DistanceTwo G c := fun j hj=>core_two_from_port F hc cK (US hj) (cp j hj).1 (cp j hj).2
    let A := insert op (insert T U)
    have tD := F.core_sub F.deepS
    have no_op : op∉insert T U := by
      intro h
      rcases mem_insert.mp h with j|j
      · exact disjoint_left.mp p_disjoint_dark opP (j.symm ▸ tD)
      exact disjoint_left.mp p_disjoint_dark opP (F.core_sub (US j))
    have a4 : A.card=4 := by
      change (insert op (insert T U)).card=4
      rw [card_insert_of_not_mem no_op,card_insert_of_not_mem Tn,U2]
    have ad : A⊆DistanceTwo G c := insert_subset op2 (insert_subset cT2 Dist)
    have zA : z∉A := by
      intro h
      rcases mem_insert.mp h with j|j
      · exact disjoint_left.mp p_disjoint_dark opP (j ▸ zd)
      rcases mem_insert.mp j with j|j
      · exact zs (j.symm ▸ F.deepS)
      exact zs (US j)
    have tA : t∉A := by
      intro h
      rcases mem_insert.mp h with j|j
      · exact opnK (j ▸ tK)
      rcases mem_insert.mp j with j|j
      · exact disjoint_left.mp k_disjoint_dark tK (j.symm ▸ tD)
      exact disjoint_left.mp k_disjoint_dark tK (F.core_sub (US j))
    have sA : s∉A := by
      intro h
      rcases mem_insert.mp h with j|j
      · exact opns j.symm
      rcases mem_insert.mp j with j|j
      · exact (by decide : s∉D) (j.symm ▸ tD)
      exact (by decide : s∉D) (F.core_sub (US j))
    have h := slot_insert_three ad zc2 tc2 sc2 zA
      (fun m=>(mem_insert.mp m).elim (Ne.symm znt) tA)
      (fun m=>(mem_insert.mp m).elim (Ne.symm tns) (fun m=>(mem_insert.mp m).elim (Ne.symm zns) sA))
    omega
  by_cases cx : G.Adj c x
  · have ny : ¬G.Adj c y := fun cy=>nb ⟨cx,cy⟩
    have y2 : y∈DistanceTwo G c := d2 hc (fun e=>(by decide : y∉K) (e ▸ cK)) ny (F.commonB c cK).symm F.by'
    have fact : ∀ j∈L,G.Adj c u ∧ G.Adj u j := by
      intro j jL
      exact ⟨hit,by simpa [u,cx] using F.xL j jL⟩
    exact cone F.left_sub F.l2 F.deepL fact (by decide : y∈P) (by decide : y∉K) (by decide : y≠s) y2
  have x2 : x∈DistanceTwo G c := d2 hc (fun e=>(by decide : x∉K) (e ▸ cK)) cx (F.commonA c cK).symm F.ax
  have fact : ∀ j∈R,G.Adj c u ∧ G.Adj u j := by
    intro j jR
    exact ⟨hit,by simpa [u,cx] using F.yR j jR⟩
  exact cone F.right_sub F.r2 F.deepR fact (by decide : x∈P) (by decide : x∉K) (by decide : x≠s) x2

theorem three_balance_low_can_exit {L R S : Finset V} {T z : V} (F : ProfileThree G L R S T)
    (hc : G.Connected) (even : ∀ i,(EvenFrom G i).card≤7)
    (zW : z∈D\S) (low : (inside G D z).card≤3) :
    ∃ c∈K,∃ t∈K,RouteOn G K c t ∧ G.Adj z c := by
  classical
  obtain ⟨c,m,t,cm0,ct0,mt0,Ktag,cm,mt⟩ := common_order (common_three_balances_nonisolated F hc even)
  have cK : c∈K := by rw [←Ktag]; exact mem_insert_self _ _
  have mK : m∈K := by rw [←Ktag]; exact mem_insert_of_mem (mem_insert_self _ _)
  have tK : t∈K := by rw [←Ktag]; exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have p : RouteOn G K c t := Ktag ▸ RouteOn.three cm mt ct0
  by_cases zc : G.Adj z c
  · exact ⟨c,cK,t,tK,p,zc⟩
  by_cases zt : G.Adj z t
  · exact ⟨t,tK,c,cK,p.reverse,zt⟩
  by_cases ct : G.Adj c t
  · have zm : G.Adj z m := low_visible_port_cover F (mem_sdiff.mp zW).1 low Ktag zc zt m (by simp)
    have eq : ({m,c,t}:Finset V)=K := (insert_comm m c {t}).trans Ktag
    exact ⟨m,mK,t,tK,eq ▸ RouteOn.three cm.symm ct mt0,zm⟩
  exact (low_misses_chain_ends_impossible F hc even zW low cm ct0 ct cK mK tK Ktag zc zt).elim

#print axioms three_balance_low_can_exit
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
