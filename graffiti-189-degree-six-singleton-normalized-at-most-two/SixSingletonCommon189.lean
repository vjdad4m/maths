import SixSingletonSplice189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Singleton16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d2 from CrossSaturation189
open private two_local_counts from SixCutFar189
open private d7 k4 from SixSingletonSplice189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem strict_two_if_seen_balances {L R : Finset V} (F : Frame G L R)
    (hc : G.Connected) {c z : V} (ck : c∈K) (zs : z∈L∪R)
    (no : ¬G.Adj c z)
    (two : (D\(L∪R)).card=2)
    (all : ∀ w∈D\(L∪R),G.Adj c w) :
    z∈DistanceTwo G c := by
  have zd := union_subset F.left_sub F.right_sub zs
  have cz : c≠z := fun e=>disjoint_left.mp (by decide : Disjoint K D) ck (e.symm ▸ zd)
  by_cases hit : ∃ w∈D\(L∪R),G.Adj w z
  · obtain ⟨w,wm,wz⟩ := hit
    exact d2 hc cz no (all w wm) wz
  push_neg at hit
  have sub1 : inside G D z⊆D.erase z :=
    fun _ h=>mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,(mem_filter.mp h).1⟩
  have sub2 : D\(L∪R)⊆D.erase z :=
    fun u h=>mem_erase.mpr ⟨fun e=>(mem_sdiff.mp h).2 (e.symm ▸ zs),(mem_sdiff.mp h).1⟩
  have dis : Disjoint (inside G D z) (D\(L∪R)) :=
    disjoint_left.mpr (fun w wm wn=>hit w wn (mem_filter.mp wm).2.symm)
  have n := two_local_counts _ _ dis _ sub1 sub2
  rw [card_erase_of_mem zd,d7] at n
  have p := F.dark5 z zs
  omega

/-- Even-distance saturation forces minimum local degree two among the four
common ports, whenever the number of balanced dark vertices is at most two. -/
theorem common_min_two_of_frame {L R : Finset V} (F : Frame G L R)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ∀ c∈K,2≤(inside G K c).card := by
  classical
  intro c ck
  by_contra bad
  let S := L∪R
  let W := D\S
  let O := insert x (insert y W)
  let E := O.filter (G.Adj c)
  have Ssub : S⊆D := union_subset F.left_sub F.right_sub
  have S5 : 5≤S.card := F.strict5
  have wcount : W.card=7-S.card := by
    change (D\S).card=_
    rw [card_sdiff Ssub,d7]
  have w2 : W.card≤2 := by omega
  have os : O.card≤W.card+2 := by
    have o1 := card_insert_le x (insert y W)
    have o2 := card_insert_le y W
    change O.card≤(insert y W).card+1 at o1
    omega
  have eO : E⊆O := filter_subset _ _
  have Ocover {z : V} (h : z∈P∪W) : z∈K ∨ z∈O := by
    rcases mem_union.mp h with p|w
    · rcases mem_insert.mp p with p|p
      · exact .inr (mem_insert.mpr (.inl p))
      rcases mem_insert.mp p with p|p
      · exact .inr (mem_insert_of_mem (mem_insert.mpr (.inl p)))
      exact .inl p
    exact .inr (mem_insert_of_mem (mem_insert_of_mem w))
  have neigh (v : V) (vk : v∈K) (z : V) (vz : G.Adj v z) :
      z=a ∨ z=b ∨ z∈K ∨ z∈O := by
    rcases mem_insert.mp (F.commonBounds v vk z vz) with e|e
    · exact .inl e
    rcases mem_insert.mp e with e|e
    · exact .inr (.inl e)
    exact .inr (.inr (Ocover e))
  have cSub : G.neighborFinset c⊆insert a (insert b ((inside G K c)∪E)) := by
    intro z zm
    have cz := (mem_neighborFinset _ _ _).mp zm
    rcases neigh c ck z cz with h|h|h|h
    · exact mem_insert.mpr (.inl h)
    · exact mem_insert_of_mem (mem_insert.mpr (.inl h))
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨h,cz⟩)))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨h,cz⟩)))
  have e3 : 3≤E.card := by
    have n := card_le_card cSub
    rw [card_neighborFinset_eq_degree] at n
    have p := card_insert_le a (insert b ((inside G K c)∪E))
    have q := card_insert_le b ((inside G K c)∪E)
    have r := card_union_le (inside G K c) E
    have k := F.commonHigh c ck
    omega
  have pair : (G.Adj c x ∧ G.Adj c y) ∨ (W.card=2 ∧ ∀ z∈W,G.Adj c z) := by
    by_cases h : G.Adj c x ∧ G.Adj c y
    · exact .inl h
    apply Or.inr
    push_neg at h
    let T := W.filter (G.Adj c)
    have ins : ∃ u : V,E⊆insert u T := by
      by_cases hx : G.Adj c x
      · refine ⟨x,?_⟩
        intro z zm
        have em : z∈O.filter (G.Adj c) := zm
        obtain ⟨p,cz⟩ := mem_filter.mp em
        rcases mem_insert.mp p with p|p
        · exact mem_insert.mpr (.inl p)
        rcases mem_insert.mp p with p|p
        · exact (h hx (p ▸ cz)).elim
        exact mem_insert_of_mem (mem_filter.mpr ⟨p,cz⟩)
      refine ⟨y,?_⟩
      intro z zm
      have em : z∈O.filter (G.Adj c) := zm
      obtain ⟨p,cz⟩ := mem_filter.mp em
      rcases mem_insert.mp p with p|p
      · exact (hx (p ▸ cz)).elim
      rcases mem_insert.mp p with p|p
      · exact mem_insert.mpr (.inl p)
      exact mem_insert_of_mem (mem_filter.mpr ⟨p,cz⟩)
    obtain ⟨u,uu⟩ := ins
    have q := card_le_card uu
    have w := card_insert_le u T
    have ts : T⊆W := filter_subset _ _
    have tsz := card_le_card ts
    have eq : T=W := eq_of_subset_of_card_le ts (by omega)
    exact ⟨by omega,fun z zm=>(mem_filter.mp (eq.symm ▸ zm)).2⟩
  have noStrict {z : V} (zs : z∈S) : ¬G.Adj c z := by
    intro cz
    have zd := Ssub zs
    have zW : z∉W := fun m=>(mem_sdiff.mp m).2 zs
    have h := neigh c ck z cz
    rcases h with e|e|e|e
    · exact (by decide : a∉D) (e ▸ zd)
    · exact (by decide : b∉D) (e ▸ zd)
    · exact disjoint_left.mp (by decide : Disjoint K D) e zd
    rcases mem_insert.mp e with f|f
    · exact (by decide : x∉D) (f ▸ zd)
    rcases mem_insert.mp f with g|g
    · exact (by decide : y∉D) (g ▸ zd)
    exact zW g
  have sTwo : s∈DistanceTwo G c := by
    have cs : c≠s := fun e=>(by decide : s∉K) (e ▸ ck)
    have no : ¬G.Adj c s := by
      intro v
      rcases neigh c ck s v with e|e|e|e
      · exact (by decide : s≠a) e
      · exact (by decide : s≠b) e
      · exact (by decide : s∉K) e
      rcases mem_insert.mp e with q|q
      · exact (by decide : s≠x) q
      rcases mem_insert.mp q with q|q
      · exact (by decide : s≠y) q
      exact (by decide : s∉D) (mem_sdiff.mp q).1
    exact d2 hc cs no (F.ac c ck).symm F.sa.symm
  have strictTwo : S⊆DistanceTwo G c := by
    intro z zs
    have cd : c≠z := fun e=>disjoint_left.mp (by decide : Disjoint K D) ck (e.symm ▸ Ssub zs)
    rcases pair with ⟨cx,cy⟩|⟨n,nb⟩
    · rcases mem_union.mp zs with l|r
      · exact d2 hc cd (noStrict zs) cx (F.xL z l)
      exact d2 hc cd (noStrict zs) cy (F.yR z r)
    exact strict_two_if_seen_balances F hc ck zs (noStrict zs) n nb
  have sS : s∉S := fun p=>(by decide : s∉D) (Ssub p)
  have upper := distanceTwo_le_of_even 6 c (even c)
  have am : (insert s S).card≤(DistanceTwo G c).card := card_le_card (insert_subset sTwo strictTwo)
  rw [card_insert_of_not_mem sS] at am
  have s5 : S.card=5 := by omega
  have e1 : (O\E).card≤1 := by
    rw [card_sdiff eO]
    omega
  have tExist : ∃ t∈K,c≠t ∧ ¬G.Adj c t := by
    by_cases hh : ∃ t∈K,c≠t ∧ ¬G.Adj c t
    · exact hh
    exfalso
    have sub : K.erase c⊆inside G K c := by
      intro z zm
      have ⟨zc,zk⟩ := mem_erase.mp zm
      exact mem_filter.mpr ⟨zk,Classical.byContradiction (fun no=>hh ⟨z,zk,zc.symm,no⟩)⟩
    have r := card_le_card sub
    rw [card_erase_of_mem ck,k4] at r
    omega
  obtain ⟨t,tk,ct,nt⟩ := tExist
  have ts : t∉insert s S := by
    intro h
    rcases mem_insert.mp h with r|r
    · exact (by decide : s∉K) (r ▸ tk)
    exact disjoint_left.mp (by decide : Disjoint K D) tk (Ssub r)
  have noShared {z : V} (ze : z∈E) : ¬G.Adj t z := by
    intro tz
    have j := d2 hc ct nt (mem_filter.mp ze).2 tz.symm
    have sub := insert_subset j (insert_subset sTwo strictTwo)
    have n := card_le_card sub
    rw [card_insert_of_not_mem ts,card_insert_of_not_mem sS] at n
    omega
  have tSub : G.neighborFinset t⊆insert a (insert b (((K.erase t).erase c) ∪ (O\E))) := by
    intro z zm
    have tz := (mem_neighborFinset _ _ _).mp zm
    rcases neigh t tk z tz with p|p|p|p
    · exact mem_insert.mpr (.inl p)
    · exact mem_insert_of_mem (mem_insert.mpr (.inl p))
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_erase.mpr
        ⟨fun e=>nt (e ▸ tz).symm,mem_erase.mpr ⟨tz.ne.symm,p⟩⟩)))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _
      (mem_sdiff.mpr ⟨p,fun e=>noShared e tz⟩)))
  have t2 : ((K.erase t).erase c).card=2 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨ct,ck⟩),card_erase_of_mem tk,k4]
  have w := card_le_card tSub
  rw [card_neighborFinset_eq_degree] at w
  have u := card_insert_le a (insert b (((K.erase t).erase c) ∪ (O\E)))
  have v := card_insert_le b (((K.erase t).erase c) ∪ (O\E))
  have k := card_union_le ((K.erase t).erase c) (O\E)
  have high := F.commonHigh t tk
  omega

theorem traceable_of_normalized_singleton_at_most_two_balanced {L R : Finset V}
    (F : Frame G L R) (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support :=
  traceable_of_frame_common_min_two F (common_min_two_of_frame F hc even)

#print axioms common_min_two_of_frame
#print axioms traceable_of_normalized_singleton_at_most_two_balanced
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Singleton16
