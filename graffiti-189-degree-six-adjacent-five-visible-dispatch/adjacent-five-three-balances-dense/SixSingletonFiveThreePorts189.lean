import SixSingletonFiveThreeBase189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d8 k3 p5 finish_by_balance finish_plain from SixSingletonFiveShallowRoute189
open private d2 from CrossSaturation189
open private c_not_s c_not_core core_two_from_port deep_hits_balance dark_core_five from SixSingletonFiveThreeBase189
open private small_common_path from SixSingletonFiveDensePorts189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000

private theorem common_isolated_scope {L R S : Finset V} {T c : V} (F : ProfileThree G L R S T)
    (ck : c∈K) (isol : ¬∃ z∈K,G.Adj c z) :
    G.neighborFinset c⊆insert a (insert b (insert x (insert y (D\S)))) := by
  intro z zm
  have j := (mem_neighborFinset _ _ _).mp zm
  rcases mem_insert.mp (F.commonBounds c ck z j) with h|h
  · exact mem_insert.mpr (.inl h)
  rcases mem_insert.mp h with h|h
  · exact mem_insert_of_mem (mem_insert.mpr (.inl h))
  apply mem_insert_of_mem
  apply mem_insert_of_mem
  rcases mem_union.mp h with v|d
  · rcases mem_insert.mp v with v|v
    · exact mem_insert.mpr (.inl v)
    rcases mem_insert.mp v with v|v
    · exact mem_insert_of_mem (mem_insert.mpr (.inl v))
    exact (isol ⟨z,v,j⟩).elim
  exact mem_insert_of_mem (mem_insert_of_mem d)

private theorem both_exclusives_forbidden_at_isolate {L R S : Finset V} {T c : V} (F : ProfileThree G L R S T)
    (hc : G.Connected) (even : ∀ w,(EvenFrom G w).card≤7)
    (ck : c∈K) (nearK : K.erase c⊆DistanceTwo G c) (cs : s∈DistanceTwo G c)
    (cx : G.Adj c x) (cy : G.Adj c y) : False := by
  have lc : L∪R⊆DistanceTwo G c := by
    intro z m
    rcases mem_union.mp m with l|r
    · exact core_two_from_port F hc ck (F.left_sub l) cx (F.xL z l)
    exact core_two_from_port F hc ck (F.right_sub r) cy (F.yR z r)
  have dis : Disjoint (L∪R) (K.erase c) := by
    apply disjoint_left.mpr
    intro z m zk
    have zd := F.core_sub ((mem_union.mp m).elim (fun h=>F.left_sub h) (fun h=>F.right_sub h))
    exact disjoint_left.mp (by decide : Disjoint K D) (mem_erase.mp zk).2 zd
  have off : s∉(L∪R)∪K.erase c := by
    intro m
    rcases mem_union.mp m with z|z
    · exact (by decide : s∉D) (F.core_sub ((mem_union.mp z).elim (fun h=>F.left_sub h) (fun h=>F.right_sub h)))
    exact (by decide : s∉K) (mem_erase.mp z).2
  have n := card_le_card (insert_subset cs (union_subset lc nearK))
  rw [card_insert_of_not_mem off,card_union_of_disjoint dis,card_union_of_disjoint F.apart,
    F.l2,F.r2,card_erase_of_mem ck,k3] at n
  have cap := distanceTwo_le_of_even 6 c (even c)
  omega

private theorem forbidden_single_exclusive_isolate {L R S U : Finset V} {T c p q : V}
    (F : ProfileThree G L R S T) (hc : G.Connected) (even : ∀ w,(EvenFrom G w).card≤7)
    (ck : c∈K) (nearK : K.erase c⊆DistanceTwo G c) (cs : s∈DistanceTwo G c)
    (uS : U⊆S) (u2 : U.card=2) (Tu : T∉U)
    (qP : q∈P) (qK : q∉K) (qs : q≠s)
    (uq : q∈DistanceTwo G c) (cT : T∈DistanceTwo G c)
    (cp : G.Adj c p) (pu : ∀ z∈U,G.Adj p z) : False := by
  have U2 : U⊆DistanceTwo G c := fun z m=>core_two_from_port F hc ck (uS m) cp (pu z m)
  have dis : Disjoint U (K.erase c) := by
    apply disjoint_left.mpr
    intro z m h
    exact disjoint_left.mp (by decide : Disjoint K D) (mem_erase.mp h).2 (F.core_sub (uS m))
  have tD := F.core_sub F.deepS
  have offT : T∉U∪K.erase c := by
    intro m
    exact (mem_union.mp m).elim Tu (fun h=>disjoint_left.mp (by decide : Disjoint K D) (mem_erase.mp h).2 tD)
  have offQ : q∉insert T (U∪K.erase c) := by
    intro m
    rcases mem_insert.mp m with rfl|m
    · exact disjoint_left.mp (by decide : Disjoint P D) qP tD
    exact (mem_union.mp m).elim (fun h=>disjoint_left.mp (by decide : Disjoint P D) qP (F.core_sub (uS h)))
      (fun h=>qK (mem_erase.mp h).2)
  have offS : s∉insert q (insert T (U∪K.erase c)) := by
    intro m
    rcases mem_insert.mp m with e|m
    · exact qs e.symm
    rcases mem_insert.mp m with e|m
    · exact (by decide : s∉D) (e ▸ tD)
    exact (mem_union.mp m).elim (fun h=>(by decide : s∉D) (F.core_sub (uS h)))
      (fun h=>(by decide : s∉K) (mem_erase.mp h).2)
  have n := card_le_card (insert_subset cs (insert_subset uq (insert_subset cT (union_subset U2 nearK))))
  rw [card_insert_of_not_mem offS,card_insert_of_not_mem offQ,card_insert_of_not_mem offT,
    card_union_of_disjoint dis,u2,card_erase_of_mem ck,k3] at n
  have cap := distanceTwo_le_of_even 6 c (even c)
  omega

theorem common_three_balances_nonisolated {L R S : Finset V} {T : V} (F : ProfileThree G L R S T)
    (hc : G.Connected) (even : ∀ w,(EvenFrom G w).card≤7) :
    ∀ c∈K,∃ z∈K,G.Adj c z := by
  classical
  intro c ck
  by_contra isol
  have nearK : (K.erase c)⊆DistanceTwo G c := by
    intro z m
    obtain ⟨ne,zm⟩ := mem_erase.mp m
    exact d2 hc ne.symm (fun h=>isol ⟨z,zm,h⟩) (F.commonA c ck).symm (F.commonA z zm)
  have cs : s∈DistanceTwo G c := d2 hc
    (fun e=>(by decide : s∉K) (e ▸ ck)) (c_not_s F ck) (F.commonA c ck).symm F.sa.symm
  have sub := common_isolated_scope F ck isol
  have mz := F.commonHigh c ck
  have noBoth : ¬(G.Adj c x ∧ G.Adj c y) :=
    fun h=>both_exclusives_forbidden_at_isolate F hc even ck nearK cs h.1 h.2
  let W := D\S
  have narrow (p q : V) (tag : (p=x ∧ q=y) ∨ (p=y ∧ q=x)) (nq : ¬G.Adj c q) :
      G.neighborFinset c⊆insert a (insert b (insert p W)) := by
    intro z zm
    have j := (mem_neighborFinset _ _ _).mp zm
    have h := sub zm
    simp only [mem_insert] at h ⊢
    rcases h with h|h|h|h|h
    · exact .inl h
    · exact .inr (.inl h)
    · rcases tag with tag|tag
      · exact .inr (.inr (.inl (h.trans tag.1.symm)))
      exact (nq (tag.2.symm ▸ h ▸ j)).elim
    · rcases tag with tag|tag
      · exact (nq (tag.2.symm ▸ h ▸ j)).elim
      exact .inr (.inr (.inl (h.trans tag.1.symm)))
    exact .inr (.inr (.inr h))
  have deep (p q : V) (swap : (p=x ∧ q=y) ∨ (p=y ∧ q=x)) (nq : ¬G.Adj c q) :
      T∈DistanceTwo G c := by
    have sub := narrow p q swap nq
    have i := card_insert_le a (insert b (insert p W))
    have j := card_insert_le b (insert p W)
    have k := card_insert_le p W
    have w3 : W.card=3 := F.balance
    have ss := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree]; omega)
    obtain ⟨w,wm,wt⟩ := deep_hits_balance F
    have cw : G.Adj c w := (mem_neighborFinset _ _ _).mp (ss.symm ▸
      mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem wm)))
    exact core_two_from_port F hc ck F.deepS cw wt
  by_cases cx : G.Adj c x
  · have ny : ¬G.Adj c y := fun cy=>noBoth ⟨cx,cy⟩
    have y2 : y∈DistanceTwo G c := d2 hc (fun e=>(by decide : y∉K) (e ▸ ck)) ny
      (F.commonB c ck).symm F.by'
    exact forbidden_single_exclusive_isolate F hc even ck nearK cs F.left_sub F.l2 F.deepL
      (by decide : y∈P) (by decide : y∉K) (by decide : y≠s) y2
      (deep x y (.inl ⟨rfl,rfl⟩) ny) cx F.xL
  by_cases cy : G.Adj c y
  · have x2 : x∈DistanceTwo G c := d2 hc (fun e=>(by decide : x∉K) (e ▸ ck)) cx
      (F.commonA c ck).symm F.ax
    exact forbidden_single_exclusive_isolate F hc even ck nearK cs F.right_sub F.r2 F.deepR
      (by decide : x∈P) (by decide : x∉K) (by decide : x≠s) x2
      (deep y x (.inr ⟨rfl,rfl⟩) cx) cy F.yR
  have ss : G.neighborFinset c⊆insert a (insert b W) := by
    intro z zm
    have j := (mem_neighborFinset _ _ _).mp zm
    have h := sub zm
    simp only [mem_insert] at h ⊢
    rcases h with h|h|h|h|h
    · exact .inl h
    · exact .inr (.inl h)
    · exact (cx (h ▸ j)).elim
    · exact (cy (h ▸ j)).elim
    exact .inr (.inr h)
  have n := card_le_card ss
  rw [card_neighborFinset_eq_degree] at n
  have i := card_insert_le a (insert b W)
  have j := card_insert_le b W
  have w3 : W.card=3 := F.balance
  omega

#print axioms common_three_balances_nonisolated
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
