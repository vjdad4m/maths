import SixSingletonPositiveProfiles189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset
open private Shore shore_off from AdjacentCutFiveActual189
open private Cmp aPorts bPorts DeletionConnected from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark from SixSingletonGeometry189
open private nearLeft nearRight nearBal deep nearLeft_two nearRight_two nearBal_two
  from SixSingletonFiveGeometry189
open private d2 from CrossSaturation189
open private positive_even_cap from TwoCutOrderCenters189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open FiveAdjacent (depth)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem saturate_a (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (D : Cmp G a b)
    (l : (nearLeft D).card=2) (q : (nearBal D).card=3) (p : (bPorts D\aPorts D).card=1) :
    nearLeft D∪nearBal D∪(bPorts D\aPorts D)=PositiveEven G a := by
  have dis : Disjoint (nearLeft D) (nearBal D) := by
    apply disjoint_left.mpr
    intro z l' q'
    have i := (mem_filter.mp (mem_filter.mp l').1).2
    have j := (mem_filter.mp (mem_filter.mp q').1).2
    omega
  have sep : Disjoint (nearLeft D∪nearBal D) (bPorts D\aPorts D) := by
    apply disjoint_left.mpr
    intro z lm pm
    have dm : z∈Dark D := (mem_union.mp lm).elim (fun h=>(mem_filter.mp (mem_filter.mp h).1).1)
      (fun h=>(mem_filter.mp (mem_filter.mp h).1).1)
    have h := mem_filter.mp (mem_sdiff.mp pm).1
    exact (mem_sdiff.mp dm).2 (mem_filter.mpr ⟨h.1,.inr h.2⟩)
  apply eq_of_subset_of_card_le
  · intro z zm
    rcases mem_union.mp zm with r|s
    · rcases mem_union.mp r with t|u
      · exact in_positive_even_of_dist_two (nearLeft_two t)
      exact in_positive_even_of_dist_two (nearBal_two u).1
    have ⟨uz,un⟩ := mem_sdiff.mp s
    have ⟨dz,bz⟩ := mem_filter.mp uz
    have ne : a≠z := fun e=>(shore_off D).1 (e.symm ▸ dz)
    exact in_positive_even_of_dist_two ((mem_filter.mp (d2 hc ne
      (fun e=>un (mem_filter.mpr ⟨dz,e⟩)) ab bz)).2)
  rw [card_union_of_disjoint sep,card_union_of_disjoint dis,l,q,p]
  exact positive_even_cap (d:=6) (even a)

private theorem saturate_b (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (D : Cmp G a b)
    (l : (nearRight D).card=2) (q : (nearBal D).card=3) (p : (aPorts D\bPorts D).card=1) :
    nearRight D∪nearBal D∪(aPorts D\bPorts D)=PositiveEven G b := by
  have dis : Disjoint (nearRight D) (nearBal D) := by
    apply disjoint_left.mpr
    intro z l' q'
    have i := (mem_filter.mp (mem_filter.mp l').1).2
    have j := (mem_filter.mp (mem_filter.mp q').1).2
    omega
  have sep : Disjoint (nearRight D∪nearBal D) (aPorts D\bPorts D) := by
    apply disjoint_left.mpr
    intro z lm pm
    have dm : z∈Dark D := (mem_union.mp lm).elim (fun h=>(mem_filter.mp (mem_filter.mp h).1).1)
      (fun h=>(mem_filter.mp (mem_filter.mp h).1).1)
    have h := mem_filter.mp (mem_sdiff.mp pm).1
    exact (mem_sdiff.mp dm).2 (mem_filter.mpr ⟨h.1,.inl h.2⟩)
  apply eq_of_subset_of_card_le
  · intro z zm
    rcases mem_union.mp zm with r|s
    · rcases mem_union.mp r with t|u
      · exact in_positive_even_of_dist_two (nearRight_two t)
      exact in_positive_even_of_dist_two (nearBal_two u).2
    have ⟨uz,un⟩ := mem_sdiff.mp s
    have ⟨dz,az⟩ := mem_filter.mp uz
    have ne : b≠z := fun e=>(shore_off D).2 (e.symm ▸ dz)
    exact in_positive_even_of_dist_two ((mem_filter.mp (d2 hc ne
      (fun e=>un (mem_filter.mpr ⟨dz,e⟩)) ab.symm az)).2)
  rw [card_union_of_disjoint sep,card_union_of_disjoint dis,l,q,p]
  exact positive_even_cap (d:=6) (even b)

/-- At five visible vertices and three balanced dark vertices both cut
terminals exhaust their positive-even slots at distance two. The unique
deep vertex is consequently at distance three from both. -/
theorem adjacent_five_three_balance_exact_depths
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v5 : (Vis D).card=5) (q3 : (nearBal D).card=3) :
    (PositiveEven G a=nearLeft D∪nearBal D∪(bPorts D\aPorts D)) ∧
    (PositiveEven G b=nearRight D∪nearBal D∪(aPorts D\bPorts D)) ∧
    ∃ t,deep D={t} ∧ G.dist a t=3 ∧ G.dist b t=3 := by
  classical
  have n := adjacent_five_positive_profile_counts hc ab even conn degree sd cover one d13 v5 (by omega)
  have ⟨dp,l,r⟩ : (deep D).card=1 ∧ (nearLeft D).card=2 ∧ (nearRight D).card=2 := by
    rcases n with h|h|h
    · have k := h.1
      omega
    · have k := h.1
      omega
    exact h.2
  have ⟨al,br⟩ : (aPorts D\bPorts D).card=1 ∧ (bPorts D\aPorts D).card=1 := by
    rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13 with
      ⟨_,i,j,_⟩|⟨inp,_,_,_,_,_⟩
    · exact ⟨i,j⟩
    omega
  have A := saturate_a hc ab even D l q3 br
  have B := saturate_b hc ab even D r q3 al
  obtain ⟨t,tEq⟩ := card_eq_one.mp dp
  have tm : t∈deep D := by rw [tEq]; exact mem_singleton_self _
  have d := (mem_filter.mp tm).2
  have off : t∉Vis D := (mem_sdiff.mp (mem_filter.mp tm).1).2
  have na : t∉PositiveEven G a := by
    rw [←A]
    intro h
    rcases mem_union.mp h with g|g
    · rcases mem_union.mp g with g|g
      · have v := (mem_filter.mp g).2
        omega
      have v := (mem_filter.mp g).2
      omega
    have k := mem_filter.mp (mem_sdiff.mp g).1
    exact off (mem_filter.mpr ⟨k.1,.inr k.2⟩)
  have nb : t∉PositiveEven G b := by
    rw [←B]
    intro h
    rcases mem_union.mp h with g|g
    · rcases mem_union.mp g with g|g
      · have v := (mem_filter.mp g).2
        omega
      have v := (mem_filter.mp g).2
      omega
    have k := mem_filter.mp (mem_sdiff.mp g).1
    exact off (mem_filter.mpr ⟨k.1,.inl k.2⟩)
  have da : G.dist a t≠4 := by
    intro e
    have tna : t≠a := fun p=>(shore_off D).1 (p ▸ (mem_sdiff.mp (mem_filter.mp tm).1).1)
    exact na (mem_erase.mpr ⟨tna,mem_filter.mpr ⟨mem_univ _,by rw [e]; decide⟩⟩)
  have db : G.dist b t≠4 := by
    intro e
    have tnb : t≠b := fun p=>(shore_off D).2 (p ▸ (mem_sdiff.mp (mem_filter.mp tm).1).1)
    exact nb (mem_erase.mpr ⟨tnb,mem_filter.mpr ⟨mem_univ _,by rw [e]; decide⟩⟩)
  have ha := hc.dist_triangle (u:=a) (v:=b) (w:=t)
  have hb := hc.dist_triangle (u:=b) (v:=a) (w:=t)
  rw [dist_eq_one_iff_adj.mpr ab] at ha
  rw [dist_eq_one_iff_adj.mpr ab.symm] at hb
  change min (G.dist a t) (G.dist b t)=3 at d
  exact ⟨A.symm,B.symm,t,tEq,by omega,by omega⟩

#print axioms adjacent_five_three_balance_exact_depths
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
