import SixSingletonAdjacentSlots189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset
open private Shore from AdjacentCutFiveActual189
open private Cmp aPorts bPorts DeletionConnected from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private Dark from SixSingletonGeometry189
open private nearLeft nearRight nearBal deep mainCore shallow_partition from SixSingletonFiveGeometry189
open FiveAdjacent (depth)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem near_disjoint (D : Cmp G a b) :
    Disjoint (nearLeft D) (nearRight D) ∧ Disjoint (nearLeft D∪nearRight D) (nearBal D) := by
  refine ⟨?_,?_⟩
  · apply disjoint_left.mpr
    intro z l r
    have p := (mem_filter.mp (mem_filter.mp l).1).2
    have q := (mem_filter.mp (mem_filter.mp r).1).2
    omega
  · apply disjoint_left.mpr
    intro z s h
    have j := (mem_filter.mp (mem_filter.mp h).1).2
    rcases mem_union.mp s with l|r
    · have p := (mem_filter.mp (mem_filter.mp l).1).2
      omega
    have q := (mem_filter.mp (mem_filter.mp r).1).2
    omega

/-- Exact strict-dark counts at the positively balanced multi-exclusive
six-visible profiles. The terminal ordering is marked. -/
theorem adjacent_six_positive_profile_counts
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v6 : (Vis D).card=6) (b2 : (bPorts D\aPorts D).card=2) (pos : 0<(nearBal D).card) :
    let x := (aPorts D\bPorts D).card
    let q := (nearBal D).card
    let l := (nearLeft D).card
    let r := (nearRight D).card
    (x=2 ∧ q=1 ∧ l=3 ∧ r=3) ∨
    (x=1 ∧ q=1 ∧ ((l=2 ∧ r=4) ∨ (l=3 ∧ r=3))) ∨
    (x=1 ∧ q=2 ∧ l=2 ∧ r=3) := by
  classical
  dsimp only
  obtain ⟨AL,AU,near⟩ : 1≤(aPorts D\bPorts D).card ∧ (aPorts D\bPorts D).card≤2 ∧
      ∀ z∈Dark D,depth G a b z=2 := by
    rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13 with
      ⟨m,_,_,_⟩|⟨_,l,u,_,_,j⟩
    · omega
    exact ⟨l,u,j⟩
  have up : ∀ z∈Shore D,depth G a b z≤3 := by
    intro z zd
    by_cases zv : z∈Vis D
    · change min (G.dist a z) (G.dist b z)≤3
      rcases (mem_filter.mp zv).2 with az|bz
      · have h := dist_eq_one_iff_adj.mpr az
        omega
      · have h := dist_eq_one_iff_adj.mpr bz
        omega
    · exact le_trans (le_of_eq (near z (mem_sdiff.mpr ⟨zd,zv⟩))) (by decide)
  have noDeep : deep D=∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro z zd
    have d2 := near z (mem_filter.mp zd).1
    have d3 := (mem_filter.mp zd).2
    omega
  have core : mainCore D=nearLeft D∪nearRight D := by unfold mainCore; simp only [noDeep,union_empty]
  have dark7 : (Dark D).card=7 := by
    change (Shore D\Vis D).card=7
    rw [card_sdiff (vis_sub D),d13,v6]
  have p := shallow_partition hc D up
  rw [core] at p
  obtain ⟨lr,lb⟩ := near_disjoint D
  have sum : (nearLeft D).card+(nearRight D).card+(nearBal D).card=7 := by
    rw [←card_union_of_disjoint lr,←card_union_of_disjoint lb,p,dark7]
  have ⟨A,B⟩ := adjacent_even_slot_rows hc ab even D
  omega

/-- Five-visible residuals have one exclusive of each color, three common
ports, and these exact strict-dark counts once deep and balanced marks
are accounted for. -/
theorem adjacent_five_positive_profile_counts
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v5 : (Vis D).card=5) (q2 : 2≤(nearBal D).card) :
    let q := (nearBal D).card
    let v := (deep D).card
    let l := (nearLeft D).card
    let r := (nearRight D).card
    (q=2 ∧ v=0 ∧ l=3 ∧ r=3) ∨
    (q=2 ∧ v=1 ∧ ((l=2 ∧ r=3) ∨ (l=3 ∧ r=2))) ∨
    (q=3 ∧ v=1 ∧ l=2 ∧ r=2) := by
  classical
  dsimp only
  obtain ⟨ac,bc,deep1,cap⟩ : (aPorts D\bPorts D).card=1 ∧ (bPorts D\aPorts D).card=1 ∧
      (deep D).card≤1 ∧ (nearBal D).card≤2+(deep D).card := by
    rcases adjacent_singleton_thirteen_even_profile hc ab even conn degree sd cover one d13 with
      ⟨_,i,j,k,l⟩|⟨h,_,_,_,_,_⟩
    · exact ⟨i,j,k,l⟩
    omega
  have up : ∀ z∈Shore D,depth G a b z≤3 := by
    rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13 with
      ⟨_,_,_,j⟩|⟨h,_,_,_,_,_⟩
    · exact j
    omega
  have kN : Disjoint (nearLeft D∪nearRight D) (deep D) := by
    apply disjoint_left.mpr
    intro z lm dm
    have dp := (mem_filter.mp dm).2
    rcases mem_union.mp lm with nl|nr
    · have q := (mem_filter.mp nl).2
      omega
    have q := (mem_filter.mp nr).2
    omega
  have kB : Disjoint (mainCore D) (nearBal D) := by
    apply disjoint_left.mpr
    intro z m q
    rcases mem_union.mp m with c|d
    · exact disjoint_left.mp (near_disjoint D).2 c q
    have e := (mem_filter.mp d).2
    have f := (mem_filter.mp q).2
    omega
  have d8 : (Dark D).card=8 := by
    change (Shore D\Vis D).card=8
    rw [card_sdiff (vis_sub D),d13,v5]
  have total : (nearLeft D).card+(nearRight D).card+(deep D).card+(nearBal D).card=8 := by
    rw [←card_union_of_disjoint (near_disjoint D).1,←card_union_of_disjoint kN]
    change (mainCore D).card+(nearBal D).card=8
    rw [←card_union_of_disjoint kB,shallow_partition hc D up,d8]
  have ⟨l,r⟩ := adjacent_even_slot_rows hc ab even D
  omega

#print axioms adjacent_five_positive_profile_counts
#print axioms adjacent_six_positive_profile_counts
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
