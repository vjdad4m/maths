import DegreeFiveBothFiveCounts189
import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed from DegreeFiveActualCut189
open private anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private noncomputable def residue (C : Cmp (G:=G) (a:=a) (b:=b)) : Finset V :=
  Shore C\sharedPortSet C

private theorem cut_mem_iff {C : Cmp (G:=G) (a:=a) (b:=b)} {v : V} :
    v∈cutPorts C ↔ v∈Shore C ∧ (G.Adj a v ∨ G.Adj b v) := mem_filter

private theorem common_sub_ports (C : Cmp (G:=G) (a:=a) (b:=b)) :
    sharedPortSet C⊆cutPorts C := fun _ h=>cut_mem_iff.mpr
  ⟨(mem_filter.mp h).1,.inl (mem_filter.mp h).2.1⟩

private theorem residue_count (C : Cmp (G:=G) (a:=a) (b:=b)) :
    (residue C).card+(sharedPortSet C).card=(Shore C).card :=
  card_sdiff_add_card_eq_card (filter_subset _ _)

private theorem residual_neighbor_bound {C : Cmp (G:=G) (a:=a) (b:=b)} {v : V}
    (vr : v∈residue C) :
    G.degree v ≤ (sharedPortSet C).card+((residue C).filter (G.Adj v)).card+1 := by
  classical
  let K := sharedPortSet C
  let R := (residue C).filter (G.Adj v)
  obtain ⟨vc,vk⟩ := mem_sdiff.mp vr
  have n : ¬(G.Adj a v ∧ G.Adj b v) := fun h=>vk (mem_filter.mpr ⟨vc,h⟩)
  have sh {c d : V} (ord : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) (nd : ¬G.Adj d v) :
      G.neighborFinset v⊆insert c (K∪R) := by
    intro w wm
    have vw := (mem_neighborFinset G _ _).mp wm
    rcases shore_closed C v vc w vw with h|h|wc
    · rcases ord with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact mem_insert.mpr (.inl h)
      exact (nd (h ▸ vw.symm)).elim
    · rcases ord with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact (nd (h ▸ vw.symm)).elim
      exact mem_insert.mpr (.inl h)
    apply mem_insert_of_mem
    by_cases wk : w∈K
    · exact mem_union_left _ wk
    exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨wc,wk⟩,vw⟩)
  have cap (c : V) (s : G.neighborFinset v⊆insert c (K∪R)) :
      G.degree v ≤ K.card+R.card+1 := by
    have h := (card_le_card s).trans (card_insert_le _ _)
    have k := card_union_le K R
    rw [card_neighborFinset_eq_degree] at h
    omega
  by_cases av : G.Adj a v
  · exact cap a (sh (.inl ⟨rfl,rfl⟩) (fun bv=>n ⟨av,bv⟩))
  exact cap b (sh (.inr ⟨rfl,rfl⟩) av)

private theorem residual_neighbor_bound_nonport {C : Cmp (G:=G) (a:=a) (b:=b)} {v : V}
    (vc : v∈Shore C) (vp : v∉cutPorts C) :
    G.degree v ≤ (sharedPortSet C).card+((residue C).filter (G.Adj v)).card := by
  classical
  let K := sharedPortSet C
  let R := (residue C).filter (G.Adj v)
  have n : ¬(G.Adj a v ∨ G.Adj b v) := fun h=>vp (cut_mem_iff.mpr ⟨vc,h⟩)
  have sh : G.neighborFinset v⊆K∪R := by
    intro w wm
    have vw := (mem_neighborFinset G _ _).mp wm
    rcases shore_closed C v vc w vw with rfl|rfl|wc
    · exact (n (.inl vw.symm)).elim
    · exact (n (.inr vw.symm)).elim
    by_cases wk : w∈K
    · exact mem_union_left _ wk
    exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨wc,wk⟩,vw⟩)
  have h := (card_le_card sh).trans (card_union_le K R)
  rwa [card_neighborFinset_eq_degree] at h

theorem residual_edge_at_five_with_big_shared
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)} (five : (cutPorts C).card=5)
    (kRange : (sharedPortSet C).card=3 ∨ ((sharedPortSet C).card=4 ∧ 7≤(Shore C).card)) :
    ∃ u∈residue C,∃ v∈residue C,G.Adj u v := by
  classical
  let K := sharedPortSet C
  let P := cutPorts C
  let S := Shore C
  have psub : P⊆S := filter_subset _ _
  rcases kRange with k3|⟨k4,s7⟩
  · have pos : 2≤(P\K).card := by
      have q := card_sdiff_add_card_eq_card (common_sub_ports C)
      change (P\K).card+K.card=P.card at q
      change P.card=5 at five
      change K.card=3 at k3
      omega
    obtain ⟨u,um,hu⟩ := anywhere_high_of_two degree pos
    have ur : u∈residue C := mem_sdiff.mpr ⟨psub (mem_sdiff.mp um).1,(mem_sdiff.mp um).2⟩
    have cap := residual_neighbor_bound ur
    have e : 0<((residue C).filter (G.Adj u)).card := by omega
    obtain ⟨v,vm⟩ := card_pos.mp e
    exact ⟨u,ur,v,(mem_filter.mp vm).1,(mem_filter.mp vm).2⟩
  have pos : 2≤(S\P).card := by
    have q := card_sdiff_add_card_eq_card psub
    change P.card=5 at five
    change 7≤S.card at s7
    omega
  obtain ⟨u,um,hu⟩ := anywhere_high_of_two degree pos
  obtain ⟨us,up⟩ := mem_sdiff.mp um
  have ur : u∈residue C := mem_sdiff.mpr ⟨us,fun uk=>up (common_sub_ports C uk)⟩
  have cap := residual_neighbor_bound_nonport us up
  have e : 0<((residue C).filter (G.Adj u)).card := by omega
  obtain ⟨v,vm⟩ := card_pos.mp e
  exact ⟨u,ur,v,(mem_filter.mp vm).1,(mem_filter.mp vm).2⟩

theorem residual_two_edges_at_five_with_three_shared
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)} (five : (cutPorts C).card=5)
    (k3 : (sharedPortSet C).card=3) (big : 7≤(Shore C).card) :
    ∃ u∈residue C,∃ v∈residue C,∃ w∈residue C,u≠w ∧ G.Adj u v ∧ G.Adj v w := by
  classical
  let P := cutPorts C
  let S := Shore C
  have psub : P⊆S := filter_subset _ _
  have pos : 2≤(S\P).card := by
    have q := card_sdiff_add_card_eq_card psub
    change P.card=5 at five
    change 7≤S.card at big
    omega
  obtain ⟨v,vm,v5⟩ := anywhere_high_of_two degree pos
  obtain ⟨vs,vp⟩ := mem_sdiff.mp vm
  have vr : v∈residue C := mem_sdiff.mpr ⟨vs,fun vk=>vp (common_sub_ports C vk)⟩
  have cap := residual_neighbor_bound_nonport vs vp
  have e : 1<((residue C).filter (G.Adj v)).card := by omega
  obtain ⟨u,um,w,wm,uw⟩ := one_lt_card.mp e
  exact ⟨u,(mem_filter.mp um).1,v,vr,w,(mem_filter.mp wm).1,uw,
    (mem_filter.mp um).2.symm,(mem_filter.mp wm).2⟩

#print axioms residual_edge_at_five_with_big_shared
#print axioms residual_two_edges_at_five_with_three_shared
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
