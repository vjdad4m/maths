import SixSingletonFiveTwoDeepBase189
import SixSingletonFivePairGeometry189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private k3 d8 p5 from SixSingletonFiveShallowRoute189
open private d2 from CrossSaturation189
open private dc_not_s dc_not_core dcore_two_from_port dark_core_six from SixSingletonFiveTwoDeepBase189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem double_common_exhausts {L R S : Finset V} {T c : V} (F : ProfileTwoDeep G L R S T)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7)
    (ck : c∈K) (cx : G.Adj c x) (cy : G.Adj c y) :
    DistanceTwo G c=insert s (L∪R) := by
  have U : L∪R⊆DistanceTwo G c := by
    intro u um
    rcases mem_union.mp um with p|p
    · exact dcore_two_from_port F hc ck (F.left_sub p) cx (F.xL u p)
    exact dcore_two_from_port F hc ck (F.right_sub p) cy (F.yR u p)
  have sn : c≠s := fun e=>(by decide : s∉K) (e ▸ ck)
  have cs : s∈DistanceTwo G c :=
    d2 hc sn (dc_not_s F ck) (F.commonA c ck).symm F.sa.symm
  have off : s∉L∪R := fun h=>(by decide : s∉D)
    (F.core_sub ((mem_union.mp h).elim (fun p=>F.left_sub p) (fun p=>F.right_sub p)))
  have eq := eq_of_subset_of_card_le (insert_subset cs U) (by
    rw [card_insert_of_not_mem off,F.strict5]
    exact distanceTwo_le_of_even 6 c (even c))
  exact eq.symm

theorem both_port_common_universal {L R S : Finset V} {T c : V} (F : ProfileTwoDeep G L R S T)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7)
    (ck : c∈K) (cx : G.Adj c x) (cy : G.Adj c y) :
    ∀ v∈P,v≠c → G.Adj c v := by
  intro v m ne
  rcases mem_insert.mp m with rfl|m
  · exact cx
  rcases mem_insert.mp m with rfl|m
  · exact cy
  by_contra no
  have d := d2 hc ne.symm no (F.commonA c ck).symm (F.commonA v m)
  rw [double_common_exhausts F hc even ck cx cy,mem_insert] at d
  rcases d with rfl|d
  · exact (by decide : s∉K) m
  have vD := F.core_sub ((mem_union.mp d).elim (fun p=>F.left_sub p) (fun p=>F.right_sub p))
  exact disjoint_left.mp (by decide : Disjoint K D) m vD

theorem both_port_common_hits_low {L R S : Finset V} {T c z : V} (F : ProfileTwoDeep G L R S T)
    (hc : G.Connected) (even : ∀ u,(EvenFrom G u).card≤7)
    (ck : c∈K) (cx : G.Adj c x) (cy : G.Adj c y)
    (zW : z∈D\S) (low : (inside G D z).card≤3) : G.Adj c z := by
  by_contra no
  have zd := (mem_sdiff.mp zW).1
  have hit : ∃ p∈P,G.Adj z p := by
    by_contra none
    have sub : G.neighborFinset z⊆inside G D z := by
      intro p m
      have edge := (mem_neighborFinset _ _ _).mp m
      have sc := mem_union.mp (F.darkBounds z zd p edge)
      exact mem_filter.mpr ⟨sc.resolve_right (fun pP=>none ⟨p,pP,edge⟩),edge⟩
    have h := card_le_card sub
    rw [card_neighborFinset_eq_degree] at h
    have q := F.darkHigh z zd
    omega
  obtain ⟨p,pm,zp⟩ := hit
  have pc : p≠c := fun e=>no (e ▸ zp.symm)
  have ne : c≠z := fun e=>disjoint_left.mp (by decide : Disjoint K D) ck (e.symm ▸ zd)
  have d := d2 hc ne no (both_port_common_universal F hc even ck cx cy p pm pc) zp.symm
  rw [double_common_exhausts F hc even ck cx cy,mem_insert] at d
  rcases d with rfl|d
  · exact (by decide : s∉D) zd
  exact (mem_sdiff.mp zW).2 ((mem_union.mp d).elim (fun p=>F.left_sub p) (fun p=>F.right_sub p))

theorem common_two_deep_nonisolated {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ∀ c∈K,∃ z∈K,G.Adj c z := by
  classical
  intro c ck
  by_contra no
  have nboth : ¬(G.Adj c x ∧ G.Adj c y) := by
    rintro ⟨cx,cy⟩
    obtain ⟨p,pm,pc⟩ := exists_ne_of_one_lt_card (s:=K) (by rw [k3]; decide) c
    have pp : p∈P := mem_insert_of_mem (mem_insert_of_mem pm)
    exact no ⟨p,pm,both_port_common_universal F hc even ck cx cy p pp pc⟩
  let q := if G.Adj c x then x else y
  let W := D\S
  have sub : G.neighborFinset c⊆insert a (insert b (insert q W)) := by
    intro u um
    have j := (mem_neighborFinset _ _ _).mp um
    rcases mem_insert.mp (F.commonBounds c ck u j) with h|h
    · exact mem_insert.mpr (.inl h)
    rcases mem_insert.mp h with h|h
    · exact mem_insert_of_mem (mem_insert.mpr (.inl h))
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    rcases mem_union.mp h with p|p
    · rcases mem_insert.mp p with p|p
      · exact mem_insert.mpr (.inl (p.trans (if_pos (p ▸ j)).symm))
      rcases mem_insert.mp p with p|p
      · have nx : ¬G.Adj c x := fun cx=>nboth ⟨cx,p ▸ j⟩
        exact mem_insert.mpr (.inl (p.trans (if_neg nx).symm))
      exact (no ⟨u,p,j⟩).elim
    exact mem_insert_of_mem p
  have h := card_le_card sub
  rw [card_neighborFinset_eq_degree] at h
  have mq := card_insert_le q W
  have mb := card_insert_le b (insert q W)
  have ma := card_insert_le a (insert b (insert q W))
  have n := F.commonHigh c ck
  have j : W.card=2 := F.balance
  omega

#print axioms double_common_exhausts
#print axioms both_port_common_hits_low
#print axioms common_two_deep_nonisolated
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
