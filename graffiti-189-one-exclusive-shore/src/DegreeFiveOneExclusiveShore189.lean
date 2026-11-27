import DegreeFiveOppositeAtMostFive189
import DegreeFiveExclusiveTwoTwo189
import DegreeFiveExclusiveTwoThree189
import DegreeFiveLonelyColorClose189
import DegreeFiveTwoExclusivePath189
import DegreeFiveNoUniqueCommon189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore mem_shore shore_hit_a shore_hit_b shore_off from DegreeFiveActualCut189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private swapCut from DegreeFiveActualCutSwap189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- If one of the two components has only exclusive contacts, the
distance-two cut is traceable under the degree-five #189 premises. A
common witness in the other wing is enough: uniqueness is excluded by
the previously checked exact single-common theorem. -/
theorem traceable_of_one_exclusive_shore_at_five_distance_two
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z)) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let K := sharedPortSet C
  have xk : x∈K := mem_filter.mpr ⟨xC,ax,bx⟩
  have shared : 2≤K.card := by
    apply Classical.byContradiction
    intro fail
    have p := card_pos.mpr ⟨x,xk⟩
    have eq : K={x} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr xk) (by
      rw [card_singleton]; omega)).symm
    have only (z : V) (zc : z∈Shore C) (az : G.Adj a z) (bz : G.Adj b z) : z=x := by
      have m : z∈K := mem_filter.mpr ⟨zc,az,bz⟩
      rw [eq] at m
      exact mem_singleton.mp m
    exact no_unique_common_across_two_components hc two even conn degree cd cover xC ax bx only none
  let A := portColor D a
  let B := portColor D b
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  obtain ⟨u,ud,au⟩ := shore_hit_a ab conn D
  obtain ⟨v,vd,bv⟩ := shore_hit_b ab conn D
  have aPos := card_pos.mpr ⟨u,show u∈A from mem_filter.mpr ⟨ud,au⟩⟩
  have bPos := card_pos.mpr ⟨v,show v∈B from mem_filter.mpr ⟨vd,bv⟩⟩
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro w wa wb
    exact none w (mem_filter.mp wa).1 ⟨(mem_filter.mp wa).2,(mem_filter.mp wb).2⟩
  have eq : A∪B=cutPorts D := by ext w; simp [A,B,portColor,cutPorts,and_or_left]
  have cards := congrArg Finset.card eq
  rw [card_union_of_disjoint dis] at cards
  have cap := opposite_ports_card_le_five_of_common hc even cd xC ax bx
  by_cases A1 : A.card=1
  · by_cases B1 : B.card=1
    · exact traceable_of_two_exclusive_foreign_ports hc two even conn degree cd cover xC ax bx none (by omega)
    exact traceable_of_lonely_color_in_exclusive_shore hc two even conn degree cd cover
      xC ax bx none (.inl ⟨A1,show 2≤B.card by omega⟩)
  by_cases B1 : B.card=1
  · exact traceable_of_lonely_color_in_exclusive_shore hc two even conn degree cd cover
      xC ax bx none (.inr ⟨B1,show 2≤A.card by omega⟩)
  by_cases A2 : A.card=2
  · by_cases B2 : B.card=2
    · exact traceable_of_exclusive_two_two_opposite_common hc two even conn degree cd cover
        shared none A2 B2
    exact traceable_of_exclusive_two_three_opposite_common hc two even conn degree cd cover
      shared none A2 (show B.card=3 by omega)
  have A3 : A.card=3 := by omega
  have B2 : B.card=2 := by omega
  let C' := swapCut C
  let D' := swapCut D
  have C_eq : Shore C'=Shore C := shore_swapCut C
  have D_eq : Shore D'=Shore D := shore_swapCut D
  have dp (c : V) : portColor D' c=portColor D c := by simp [portColor,D_eq]
  have sh : sharedPortSet C'=sharedPortSet C := by simp [sharedPortSet,C_eq,and_comm]
  have cd' : C'≠D' := fun h=>cd (swapCut.injective h)
  have none' (w : V) (wd : w∈Shore D') (p : G.Adj b w ∧ G.Adj a w) : False :=
    none w (D_eq ▸ wd) ⟨p.2,p.1⟩
  have cover' (w : V) : w=b ∨ w=a ∨ w∈Shore C' ∨ w∈Shore D' := by
    rw [C_eq,D_eq]
    rcases cover w with h|h|h|h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr (.inl h))
    exact .inr (.inr (.inr h))
  have rev : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  exact traceable_of_exclusive_two_three_opposite_common (a:=b) (b:=a) hc rev even
    conn degree cd' cover' (by rwa [sh]) none' (by rwa [dp]) (by rwa [dp])

/-- Intrinsic component-count statement: at distance two and with two
components, it suffices that one component has no shared porter. -/
theorem traceable_of_actual_five_distance_two_with_exclusive_shore
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (comp : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (profile : ∃ D : Cmp (G:=G) (a:=a) (b:=b),
      ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z)) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent=2 at comp
  rw [Nat.card_eq_fintype_card] at comp
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨x,ax,xb⟩ := two_walk_middle p (pl.trans two)
  let C := J.connectedComponentMk ⟨x,ax.ne.symm,xb.ne⟩
  have xC : x∈Shore C := mem_shore.mpr ⟨⟨ax.ne.symm,xb.ne⟩,rfl⟩
  obtain ⟨D,none⟩ := profile
  have cd : C≠D := fun e=>none x (e ▸ xC) ⟨ax,xb.symm⟩
  let T := (univ : Finset J.ConnectedComponent).erase C
  have tc : T.card=1 := by
    dsimp [T]
    rw [card_erase_of_mem (mem_univ _),card_univ,comp]
  have dT : D∈T := mem_erase.mpr ⟨cd.symm,mem_univ _⟩
  have tEq : T={D} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr dT) (by
    rw [tc,card_singleton])).symm
  have cover (w : V) : w=a ∨ w=b ∨ w∈Shore C ∨ w∈Shore D := by
    by_cases wa : w=a
    · exact .inl wa
    by_cases wb : w=b
    · exact .inr (.inl wb)
    let W := J.connectedComponentMk ⟨w,wa,wb⟩
    by_cases wc : W=C
    · exact .inr (.inr (.inl (mem_shore.mpr ⟨⟨wa,wb⟩,wc⟩)))
    have wt : W∈T := mem_erase.mpr ⟨wc,mem_univ _⟩
    rw [tEq] at wt
    exact .inr (.inr (.inr (mem_shore.mpr ⟨⟨wa,wb⟩,mem_singleton.mp wt⟩)))
  exact traceable_of_one_exclusive_shore_at_five_distance_two hc two even conn degree
    cd cover xC ax xb.symm none

#print axioms traceable_of_one_exclusive_shore_at_five_distance_two
#print axioms traceable_of_actual_five_distance_two_with_exclusive_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
