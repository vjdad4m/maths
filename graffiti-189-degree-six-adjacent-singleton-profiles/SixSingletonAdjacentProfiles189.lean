import SixSingletonAdjacentUniqueComplete189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore mem_shore shore_off shore_closed shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts two_local_counts from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private Dark Common strictA strictB bal port_union_vis singleton_neighborhood_exact
  visible_subset_singleton_even all_dark_depth_two_of_visible_six from SixSingletonGeometry189
open private singleton_distance from SixCutLowSingleton189
open private class_partition class_bal_dis from SixSingletonShape189
open private positive_even_cap from TwoCutOrderCenters189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open private twins_dist_le from AdjacentCutFiveBound189
open private d2 from CrossSaturation189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (depth shore_swapCut)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem ports_at_least_four_adj (_ab : G.Adj a b) {S D : Cmp G a b}
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    {s : V} (sS : Shore S={s}) (high : 6≤G.degree a) :
    4≤(aPorts D).card := by
  have n : G.neighborFinset a⊆insert b (insert s (aPorts D)) := by
    intro z zm
    have az := (mem_neighborFinset _ _ _).mp zm
    by_cases zb : z=b
    · exact mem_insert.mpr (.inl zb)
    rcases cover az.ne.symm zb with zS|zD
    · exact mem_insert_of_mem (mem_insert.mpr (.inl (by simpa only [sS,mem_singleton] using zS)))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨zD,az⟩))
  have c := card_le_card n
  rw [card_neighborFinset_eq_degree] at c
  have i := card_insert_le b (insert s (aPorts D))
  have j := card_insert_le s (aPorts D)
  omega

private theorem no_adjacent_port_domination (hc : G.Connected) (_ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7)
    {S D : Cmp G a b} (sd : S≠D) (d13 : (Shore D).card=13)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    {s : V} (sS : Shore S={s}) (as' : G.Adj a s) (bs' : G.Adj b s) :
    ¬aPorts D⊆bPorts D := by
  classical
  intro pos
  have ss : s∈Shore S := by simp [sS]
  have adjIncl (z : V) (zb : z≠b) (az : G.Adj a z) : G.Adj b z := by
    rcases cover az.ne.symm zb with zS|zD
    · have e : z=s := by simpa only [sS,mem_singleton] using zS
      exact e.symm ▸ bs'
    exact (mem_filter.mp (pos (mem_filter.mpr ⟨zD,az⟩))).2
  have sub : Shore D⊆PositiveEven G b∪PositiveEven G s := by
    intro z zd
    have ⟨za,zb⟩ := (mem_shore.mp zd).choose
    have le := twins_dist_le hc za.symm adjIncl
    by_cases e : Even (G.dist b z)
    · exact mem_union_left _ (mem_erase.mpr ⟨zb,mem_filter.mpr ⟨mem_univ _,e⟩⟩)
    have zn : z≠s := fun h=>disjoint_left.mp (shore_disjoint sd) ss (h ▸ zd)
    have m := singleton_distance sS hc as' bs' zn
    rw [min_eq_right le] at m
    have se : Even (G.dist s z) := by simp only [Nat.even_iff] at e ⊢; omega
    exact mem_union_right _ (mem_erase.mpr ⟨zn,mem_filter.mpr ⟨mem_univ _,se⟩⟩)
  have c := card_le_card sub
  have u := card_union_le (PositiveEven G b) (PositiveEven G s)
  have p := positive_even_cap (d:=6) (even b)
  have q := positive_even_cap (d:=6) (even s)
  omega

/-- Exact five-or-six visible profile of the remaining adjacent singleton cut. -/
theorem adjacent_singleton_thirteen_visible_profile
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13) :
    ((Vis D).card=5 ∧ (aPorts D\bPorts D).card=1 ∧ (bPorts D\aPorts D).card=1 ∧
        ∀ z∈Shore D,depth G a b z≤3) ∨
    ((Vis D).card=6 ∧ 1≤(aPorts D\bPorts D).card ∧ (aPorts D\bPorts D).card≤2 ∧
      1≤(bPorts D\aPorts D).card ∧ (bPorts D\aPorts D).card≤2 ∧
      ∀ z∈Dark D,depth G a b z=2) := by
  classical
  obtain ⟨s,sS⟩ := card_eq_one.mp one
  have ss : s∈Shore S := by simp [sS]
  obtain ⟨u,us,au⟩ := shore_hit_a ab.ne conn S
  obtain ⟨v,vs,bv⟩ := shore_hit_b ab.ne conn S
  have as' : G.Adj a s := (show u=s by simpa only [sS,mem_singleton] using us) ▸ au
  have bs' : G.Adj b s := (show v=s by simpa only [sS,mem_singleton] using vs) ▸ bv
  have s2 : G.degree s=2 := by
    rw [←card_neighborFinset_eq_degree,singleton_neighborhood_exact sS as' bs',
      card_insert_of_not_mem (by simpa using ab.ne),card_singleton]
  have ah := (degree a s as'.ne).resolve_right (by omega)
  have bh := (degree b s bs'.ne).resolve_right (by omega)
  have a4 := ports_at_least_four_adj ab cover sS ah
  have swapCov : ∀ {z : V},z≠b → z≠a → z∈Shore (swapCut S) ∨ z∈Shore (swapCut D) := by
    intro z zb za
    rw [shore_swapCut,shore_swapCut]
    exact cover za zb
  have ss' : Shore (swapCut S)={s} := by rwa [shore_swapCut]
  have b4 : 4≤(bPorts D).card := by
    have h := ports_at_least_four_adj ab.symm swapCov ss' bh
    simpa only [aPorts,bPorts,shore_swapCut] using h
  have pNA := no_adjacent_port_domination hc ab even sd d13 cover sS as' bs'
  have pNB : ¬bPorts D⊆aPorts D := by
    have h := no_adjacent_port_domination (a:=b) (b:=a) hc ab.symm even
      (S:=swapCut S) (D:=swapCut D) (fun g=>sd (swapCut.injective g))
      (by rwa [shore_swapCut]) swapCov ss' bs' as'
    simpa only [aPorts,bPorts,shore_swapCut] using h
  have high : (Vis D).card≤6 :=
    (card_le_card (visible_subset_singleton_even sd hc ss as' bs')).trans (positive_even_cap (d:=6) (even s))
  have aSoft : (aPorts D\bPorts D).card+(bPorts D).card=(Vis D).card := by
    have eq : (Vis D)\bPorts D=aPorts D\bPorts D := by
      rw [←port_union_vis]
      ext z
      simp
      tauto
    have h := card_sdiff_add_card_eq_card (show bPorts D⊆Vis D from by rw [←port_union_vis]; exact subset_union_right)
    rwa [eq] at h
  have bSoft : (bPorts D\aPorts D).card+(aPorts D).card=(Vis D).card := by
    have eq : (Vis D)\aPorts D=bPorts D\aPorts D := by
      rw [←port_union_vis]
      ext z
      simp
      tauto
    have h := card_sdiff_add_card_eq_card (show aPorts D⊆Vis D from by rw [←port_union_vis]; exact subset_union_left)
    rwa [eq] at h
  have aPos : 0<(aPorts D\bPorts D).card := by
    obtain ⟨z,za,zb⟩ := not_subset.mp pNA
    exact card_pos.mpr ⟨z,mem_sdiff.mpr ⟨za,zb⟩⟩
  have bPos : 0<(bPorts D\aPorts D).card := by
    obtain ⟨z,za,zb⟩ := not_subset.mp pNB
    exact card_pos.mpr ⟨z,mem_sdiff.mpr ⟨za,zb⟩⟩
  by_cases five : (Vis D).card=5
  · refine .inl ⟨five,by omega,by omega,?_⟩
    intro z zd
    have zn : z≠s := fun e=>disjoint_left.mp (shore_disjoint sd) ss (e ▸ zd)
    have n := singleton_distance sS hc as' bs' zn
    change G.dist s z=1+depth G a b z at n
    have sPort : Vis D⊆DistanceTwo G s := by
      intro q qq
      have ⟨qD,qv⟩ := mem_filter.mp qq
      have qS : q∉Shore S := fun e=>disjoint_left.mp (shore_disjoint sd) e qD
      have qn : s≠q := fun e=>qS (e ▸ ss)
      have nq : ¬G.Adj s q := by
        intro e
        rcases shore_closed S s ss q e with r|r|r
        · exact (shore_off D).1 (r ▸ qD)
        · exact (shore_off D).2 (r ▸ qD)
        exact qS r
      exact qv.elim (fun e=>d2 hc qn nq as'.symm e) (fun e=>d2 hc qn nq bs'.symm e)
    have cap5 := card_le_card sPort
    by_contra big
    have h := twoEvenLayers_of_radius_five hc 2 conn (x:=s) (y:=z) (by omega)
    have c := even s
    omega
  have six : (Vis D).card=6 := by omega
  exact .inr ⟨six,by omega,by omega,by omega,by omega,
    all_dark_depth_two_of_visible_six hc even sd sS as' bs' six⟩

#print axioms adjacent_singleton_thirteen_visible_profile
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
