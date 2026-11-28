import SixSingletonFiveActual189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset
open private CutGraph Shore mem_shore shore_off shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts three_local_counts from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private Dark bal singleton_neighborhood_exact from SixSingletonGeometry189
open private nearLeft nearRight nearBal deep mainCore deep_at_most_one shallow_partition
  nearLeft_two nearRight_two nearBal_two from SixSingletonFiveGeometry189
open private d2 from CrossSaturation189
open FiveAdjacent (depth)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The two cut terminals' positive-even capacity is shared by their
near dark classes and the opposite exclusive visible ports. -/
theorem adjacent_even_slot_rows (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (D : Cmp G a b) :
    (nearLeft D).card+(nearBal D).card+(bPorts D\aPorts D).card≤6 ∧
    (nearRight D).card+(nearBal D).card+(aPorts D\bPorts D).card≤6 := by
  classical
  have Ad : Disjoint (nearLeft D) (nearBal D) := by
    apply disjoint_left.mpr
    intro z zl zb
    have d := nearBal_two zb
    have e := (mem_filter.mp (mem_filter.mp zl).1).2
    omega
  have Bd : Disjoint (nearRight D) (nearBal D) := by
    apply disjoint_left.mpr
    intro z zl zb
    have d := nearBal_two zb
    have e := (mem_filter.mp (mem_filter.mp zl).1).2
    omega
  have visA : aPorts D\bPorts D⊆Vis D := fun _ h=>
    mem_filter.mpr ⟨(mem_filter.mp (mem_sdiff.mp h).1).1,.inl (mem_filter.mp (mem_sdiff.mp h).1).2⟩
  have visB : bPorts D\aPorts D⊆Vis D := fun _ h=>
    mem_filter.mpr ⟨(mem_filter.mp (mem_sdiff.mp h).1).1,.inr (mem_filter.mp (mem_sdiff.mp h).1).2⟩
  have Dd : Disjoint (Dark D) (Vis D) :=
    disjoint_left.mpr (fun _ h q=>(mem_sdiff.mp h).2 q)
  have subL : nearLeft D⊆Dark D := fun _ h=>(mem_filter.mp (mem_filter.mp h).1).1
  have subR : nearRight D⊆Dark D := fun _ h=>(mem_filter.mp (mem_filter.mp h).1).1
  have subB : nearBal D⊆Dark D := fun _ h=>(mem_filter.mp (mem_filter.mp h).1).1
  have EBa : bPorts D\aPorts D⊆DistanceTwo G a := by
    intro z zm
    have ⟨zb,zn⟩ := mem_sdiff.mp zm
    have ⟨zd,bz⟩ := mem_filter.mp zb
    have ne : a≠z := fun h=>(shore_off D).1 (h.symm ▸ zd)
    exact d2 hc ne (fun e=>zn (mem_filter.mpr ⟨zd,e⟩)) ab bz
  have EAb : aPorts D\bPorts D⊆DistanceTwo G b := by
    intro z zm
    have ⟨za,zn⟩ := mem_sdiff.mp zm
    have ⟨zd,az⟩ := mem_filter.mp za
    have ne : b≠z := fun h=>(shore_off D).2 (h.symm ▸ zd)
    exact d2 hc ne (fun e=>zn (mem_filter.mpr ⟨zd,e⟩)) ab.symm az
  have L := three_local_counts _ _ _ Ad (Dd.mono subL visB) (Dd.mono subB visB) (DistanceTwo G a)
    (fun z m=>mem_filter.mpr ⟨mem_univ _,nearLeft_two m⟩)
    (fun z m=>mem_filter.mpr ⟨mem_univ _,(nearBal_two m).1⟩) EBa
  have R := three_local_counts _ _ _ Bd (Dd.mono subR visA) (Dd.mono subB visA) (DistanceTwo G b)
    (fun z m=>mem_filter.mpr ⟨mem_univ _,nearRight_two m⟩)
    (fun z m=>mem_filter.mpr ⟨mem_univ _,(nearBal_two m).2⟩) EAb
  exact ⟨L.trans (distanceTwo_le_of_even 6 a (even a)), R.trans (distanceTwo_le_of_even 6 b (even b))⟩

/-- The remaining adjacent order-sixteen singleton cases have an explicit
small arithmetic profile; the first cases in each disjunct are now routed. -/
theorem adjacent_singleton_thirteen_even_profile
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13) :
    (((Vis D).card=5 ∧ (aPorts D\bPorts D).card=1 ∧ (bPorts D\aPorts D).card=1 ∧
       (deep D).card≤1 ∧ (nearBal D).card≤2+(deep D).card)) ∨
    (((Vis D).card=6 ∧ 1≤(aPorts D\bPorts D).card ∧ (aPorts D\bPorts D).card≤2 ∧
      1≤(bPorts D\aPorts D).card ∧ (bPorts D\aPorts D).card≤2 ∧
      (nearBal D).card+(aPorts D\bPorts D).card+(bPorts D\aPorts D).card≤5)) := by
  classical
  obtain ⟨A,B⟩ := adjacent_even_slot_rows hc ab even D
  rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13 with five|six
  · obtain ⟨v5,ac,bc,up⟩ := five
    obtain ⟨s,sS⟩ := card_eq_one.mp one
    obtain ⟨u,us,au⟩ := shore_hit_a ab.ne conn S
    obtain ⟨v,vs,bv⟩ := shore_hit_b ab.ne conn S
    have as' : G.Adj a s := (show u=s by simpa only [sS,mem_singleton] using us) ▸ au
    have bs' : G.Adj b s := (show v=s by simpa only [sS,mem_singleton] using vs) ▸ bv
    have h := deep_at_most_one hc even sd sS as' bs' v5
    have d8 : (Dark D).card=8 := by
      change (Shore D\Vis D).card=_
      rw [card_sdiff (vis_sub D),d13,v5]
    have sum := card_union_le (mainCore D) (nearBal D)
    rw [shallow_partition hc D up,d8] at sum
    have co := card_union_le (nearLeft D∪nearRight D) (deep D)
    change (mainCore D).card≤_ at co
    have t := card_union_le (nearLeft D) (nearRight D)
    exact .inl ⟨v5,ac,bc,h,by omega⟩
  obtain ⟨v6,al,au,bl,bu,near⟩ := six
  have up (z : V) (zd : z∈Shore D) : depth G a b z≤3 := by
    by_cases vis : z∈Vis D
    · rcases (mem_filter.mp vis).2 with aa|bb
      · have m := dist_eq_one_iff_adj.mpr aa
        change min (G.dist a z) (G.dist b z)≤3
        omega
      have m := dist_eq_one_iff_adj.mpr bb
      change min (G.dist a z) (G.dist b z)≤3
      omega
    have t := near z (mem_sdiff.mpr ⟨zd,vis⟩)
    omega
  have d7 : (Dark D).card=7 := by
    change (Shore D\Vis D).card=_
    rw [card_sdiff (vis_sub D),d13,v6]
  have dz : (deep D).card=0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_not_mem.mpr
    intro z h
    have p := near z (mem_filter.mp h).1
    have q := (mem_filter.mp h).2
    omega
  have sum := card_union_le (mainCore D) (nearBal D)
  rw [shallow_partition hc D up,d7] at sum
  have co := card_union_le (nearLeft D∪nearRight D) (deep D)
  change (mainCore D).card≤_ at co
  have t := card_union_le (nearLeft D) (nearRight D)
  exact .inr ⟨v6,al,au,bl,bu,by omega⟩

#print axioms adjacent_even_slot_rows
#print axioms adjacent_singleton_thirteen_even_profile
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
