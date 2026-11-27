import DegreeFiveCommonUniversalFive189
import DegreeFiveBalancedCommonRoot189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private secondShore charge_at_high_port anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private sharedPortSet inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private shore_neighbor_cover from DegreeFiveDistanceTwoSingletonClose189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The (3,3) common shore opposite an exclusive 2+3 shore has four
vertices, with a low nonporter two steps away from each cut. -/
theorem low_nonporter_of_three_three_opposite_two_three
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (shared : 2 ≤ (sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (cA : (portColor C a).card=3) (cB : (portColor C b).card=3)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3) :
    (Shore C).card=4 ∧
    ∃ z ∈ Shore C, G.dist z a=2 ∧ G.dist z b=2 ∧ G.degree z<5 := by
  classical
  let A := portColor C a
  let B := portColor C b
  let K := sharedPortSet C
  let E := secondShore C a
  let F := secondShore C b
  have kA : K ⊆ A := fun _ h=>mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.1⟩
  have kB : K ⊆ B := fun _ h=>mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.2⟩
  have k3 := (card_le_card kA).trans (le_of_eq cA)
  have dis : Disjoint (portColor D a) (portColor D b) := by
    apply disjoint_left.mpr
    intro w wa wb
    exact none w (mem_filter.mp wa).1 ⟨(mem_filter.mp wa).2,(mem_filter.mp wb).2⟩
  have union : portColor D a ∪ portColor D b = cutPorts D := by
    ext w
    simp [portColor,cutPorts,and_or_left]
  have five : (cutPorts D).card=5 := by
    rw [←union,card_union_of_disjoint dis,pA,pB]
  obtain ⟨x,xk⟩ := card_pos.mp (show 0<K.card by exact lt_of_lt_of_le (by decide) shared)
  obtain ⟨xc,ax,bx⟩ := mem_filter.mp xk
  have uni := common_universal_in_shore_at_five hc even cd xc ax bx five
  obtain ⟨u,up,uh⟩ := anywhere_high_of_two degree (show 2 ≤ (portColor D a).card by omega)
  obtain ⟨ud,au⟩ := mem_filter.mp up
  have bu : ¬G.Adj b u := fun h=>none u ud ⟨au,h⟩
  have hu := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc ud au uh
  rw [if_neg bu] at hu
  change 5 ≤ (portColor D a).card+(secondShore D a).card at hu
  have he := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have e1 : E.card ≤ 1 := by change (secondShore C a).card ≤ 1; omega
  have toE {z : V} (zc : z∈Shore C) (na : ¬G.Adj a z) : z∈E := by
    have xz : x≠z := fun h=>na (h ▸ ax)
    have az : a≠z := fun h=>(shore_off C).1 (h.symm ▸ zc)
    exact mem_inter.mpr ⟨zc,d2 hc az na ax (uni z zc xz)⟩
  have toF {z : V} (zc : z∈Shore C) (nb : ¬G.Adj b z) : z∈F := by
    have xz : x≠z := fun h=>nb (h ▸ bx)
    have bz : b≠z := fun h=>(shore_off C).2 (h.symm ▸ zc)
    exact mem_inter.mpr ⟨zc,d2 hc bz nb bx (uni z zc xz)⟩
  have sizeE : (Shore C).card ≤ 4 := by
    have s : Shore C ⊆ A ∪ E := by
      intro z zc
      by_cases h : G.Adj a z
      · exact mem_union_left _ (mem_filter.mpr ⟨zc,h⟩)
      exact mem_union_right _ (toE zc h)
    have k := (card_le_card s).trans (card_union_le A E)
    change A.card=3 at cA
    omega
  have nonsharedLow {z : V} (zc : z∈Shore C) (no : ¬(G.Adj a z ∧ G.Adj b z)) :
      G.degree z<5 := by
    by_contra! hz
    have h := inside_high_at_least_four_if_exclusive zc hz no
    have s : inside G (Shore C) z ⊆ (Shore C).erase z := by
      intro w hw
      obtain ⟨wc,adj⟩ := mem_filter.mp hw
      exact mem_erase.mpr ⟨adj.ne.symm,wc⟩
    have cap := card_le_card s
    rw [card_erase_of_mem zc] at cap
    omega
  have keq : K.card=3 := by
    by_contra! ne
    have qa : ¬ A ⊆ K := by
      intro h
      have q := card_le_card h
      change A.card=3 at cA
      omega
    have qb : ¬ B ⊆ K := by
      intro h
      have q := card_le_card h
      change B.card=3 at cB
      omega
    obtain ⟨s,sa,sk⟩ := not_subset.mp qa
    obtain ⟨t,tb,tk⟩ := not_subset.mp qb
    obtain ⟨sc,as⟩ := mem_filter.mp sa
    obtain ⟨tc,bt⟩ := mem_filter.mp tb
    have ns : ¬G.Adj b s := fun h=>sk (mem_filter.mpr ⟨sc,as,h⟩)
    have nt : ¬G.Adj a t := fun h=>tk (mem_filter.mpr ⟨tc,h,bt⟩)
    have st : s≠t := fun h=>nt (h ▸ as)
    exact (degree s t st).elim (fun h=>by have q:=nonsharedLow sc (fun e=>ns e.2); omega)
      (fun h=>by have q:=nonsharedLow tc (fun e=>nt e.1); omega)
  have aeq : A=K := (eq_of_subset_of_card_le kA (by change A.card=3 at cA; omega)).symm
  have beq : B=K := (eq_of_subset_of_card_le kB (by change B.card=3 at cB; omega)).symm
  have shape : (Shore C).card=4 := by
    by_contra! z
    have sm : (Shore C).card ≤ 3 := by omega
    have low' (w : V) (wc : w∈Shore C) : G.degree w<5 := by
      have sub : inside G (Shore C) w ⊆ (Shore C).erase w := by
        intro t ht
        obtain ⟨tc,h⟩ := mem_filter.mp ht
        exact mem_erase.mpr ⟨h.ne.symm,tc⟩
      have n := card_le_card sub
      rw [card_erase_of_mem wc] at n
      have k := card_le_card (shore_neighbor_cover C wc)
      rw [card_neighborFinset_eq_degree] at k
      have m := card_insert_le a (insert b (inside G (Shore C) w))
      have p := card_insert_le b (inside G (Shore C) w)
      omega
    obtain ⟨w,wk,t,tk,wt⟩ := one_lt_card.mp (show 1<K.card by omega)
    have hw := low' w (mem_filter.mp wk).1
    have ht := low' t (mem_filter.mp tk).1
    exact (degree w t wt).elim (fun q=>by omega) (fun q=>by omega)
  have existsZ : ¬ Shore C ⊆ K := by
    intro h
    have q := card_le_card h
    omega
  obtain ⟨z,zc,zk⟩ := not_subset.mp existsZ
  have na : ¬G.Adj a z := fun h=>zk (by rw [←aeq]; exact mem_filter.mpr ⟨zc,h⟩)
  have nb : ¬G.Adj b z := fun h=>zk (by rw [←beq]; exact mem_filter.mpr ⟨zc,h⟩)
  have za : G.dist a z=2 := (mem_filter.mp (mem_inter.mp (toE zc na)).2).2
  have zb : G.dist b z=2 := (mem_filter.mp (mem_inter.mp (toF zc nb)).2).2
  exact ⟨shape,z,zc,by rwa [SimpleGraph.dist_comm],by rwa [SimpleGraph.dist_comm],
    nonsharedLow zc (fun h=>na h.1)⟩

#print axioms low_nonporter_of_three_three_opposite_two_three
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
