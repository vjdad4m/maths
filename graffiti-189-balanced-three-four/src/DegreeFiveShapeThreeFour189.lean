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

/-- The (3,4) common shore opposite an exclusive 2+3 shore has four
vertices, all touching b, with exactly one a-shell vertex, which is low. -/
theorem low_b_porter_of_three_four_opposite_two_three
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (shared : 2 ≤ (sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (cA : (portColor C a).card=3) (cB : (portColor C b).card=4)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3) :
    (Shore C).card=4 ∧ (secondShore C a).card=1 ∧
    (∀ w∈Shore C,G.Adj b w) ∧
    ∃ z ∈ Shore C, G.dist z a=2 ∧ G.Adj b z ∧ G.degree z<5 := by
  classical
  let A := portColor C a
  let B := portColor C b
  let K := sharedPortSet C
  let E := secondShore C a
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
  have sizeE : (Shore C).card ≤ 4 := by
    have s : Shore C ⊆ A ∪ E := by
      intro z zc
      by_cases h : G.Adj a z
      · exact mem_union_left _ (mem_filter.mpr ⟨zc,h⟩)
      exact mem_union_right _ (toE zc h)
    have k := (card_le_card s).trans (card_union_le A E)
    change A.card=3 at cA
    omega
  have bsub : B ⊆ Shore C := filter_subset _ _
  have size := card_le_card bsub
  change B.card=4 at cB
  have eq : B=Shore C := eq_of_subset_of_card_le bsub (by omega)
  have bzAll (w : V) (wc : w∈Shore C) : G.Adj b w :=
    (mem_filter.mp (show w∈B by rwa [eq])).2
  have existsZ : ¬ Shore C ⊆ A := by
    intro h
    have q := card_le_card h
    change A.card=3 at cA
    omega
  obtain ⟨z,zc,noa⟩ := not_subset.mp existsZ
  have za : ¬G.Adj a z := fun h=>noa (mem_filter.mpr ⟨zc,h⟩)
  have ez := toE zc za
  have pe : 0<E.card := card_pos.mpr ⟨z,ez⟩
  have dz : G.dist a z=2 := (mem_filter.mp (mem_inter.mp ez).2).2
  have low : G.degree z<5 := by
    by_contra! hz
    have h := inside_high_at_least_four_if_exclusive zc hz (fun e=>za e.1)
    have s : inside G (Shore C) z ⊆ (Shore C).erase z := by
      intro w hw
      obtain ⟨wc,adj⟩ := mem_filter.mp hw
      exact mem_erase.mpr ⟨adj.ne.symm,wc⟩
    have cap := card_le_card s
    rw [card_erase_of_mem zc] at cap
    omega
  exact ⟨by omega,by change E.card=1; omega,bzAll,z,zc,
    by rwa [SimpleGraph.dist_comm],bzAll z zc,low⟩

#print axioms low_b_porter_of_three_four_opposite_two_three
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
