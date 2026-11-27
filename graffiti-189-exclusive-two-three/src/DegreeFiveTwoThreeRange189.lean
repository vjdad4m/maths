import DegreeFiveCommonUniversalFive189
import DegreeFiveBalancedCommonRoot189
import DegreeFiveUniquePortClosureTest189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private secondShore charge_at_high_port anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private sharedPortSet inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private shore_neighbor_cover from DegreeFiveDistanceTwoSingletonClose189
open private shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private opposite_ports_at_exclusive_le_four from DegreeFiveUniquePortClosureTest189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The common contact counts opposite an exclusively attached 2+3 shore
are both between three and four, leaving exactly the four orientations. -/
theorem common_contact_range_opposite_two_three
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2 ≤ (sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3) :
    3 ≤ (portColor C a).card ∧ (portColor C a).card ≤ 4 ∧
    3 ≤ (portColor C b).card ∧ (portColor C b).card ≤ 4 := by
  classical
  let K := sharedPortSet C
  have k2 : 2 ≤ K.card := shared
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
  have part (c : V) (hit : G.Adj c x) (co : c∉Shore C) :
      (portColor C c).card + (secondShore C c).card = (Shore C).card := by
    let P := portColor C c
    let Q := secondShore C c
    have dis : Disjoint P Q := by
      apply disjoint_left.mpr
      intro w wp wq
      have one := dist_eq_one_iff_adj.mpr (mem_filter.mp wp).2
      have two := (mem_filter.mp (mem_inter.mp wq).2).2
      omega
    have eq : P∪Q=Shore C := by
      apply le_antisymm
      · exact union_subset (filter_subset _ _) inter_subset_left
      intro w wc
      by_cases cw : G.Adj c w
      · exact mem_union_left _ (mem_filter.mpr ⟨wc,cw⟩)
      have xw : x≠w := fun h=>cw (h ▸ hit)
      have cw' : c≠w := fun h=>co (h.symm ▸ wc)
      exact mem_union_right _ (mem_inter.mpr ⟨wc,d2 hc cw' cw hit (uni w wc xw)⟩)
    have h := congrArg Finset.card eq
    rwa [card_union_of_disjoint dis] at h
  have partA := part a ax (shore_off C).1
  have partB := part b bx (shore_off C).2
  have ba : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  obtain ⟨v,vp,v5⟩ := anywhere_high_of_two degree (show 2≤(portColor D b).card by omega)
  obtain ⟨vd,bv⟩ := mem_filter.mp vp
  have av : ¬G.Adj a v := fun h=>none _ vd ⟨h,bv⟩
  have q := charge_at_high_port (.inr ⟨rfl,rfl⟩) hc vd bv v5
  rw [if_neg av] at q
  change 5≤(portColor D b).card+(secondShore D b).card at q
  have eB := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ ba even
  have size : 4≤(Shore C).card := by
    by_contra! small
    obtain ⟨m,mk,n,nk,mn⟩ := one_lt_card.mp (show 1<K.card by omega)
    have low (w : V) (wc : w∈Shore C) : G.degree w<5 := by
      have sub : inside G (Shore C) w ⊆ (Shore C).erase w := by
        intro t tt
        obtain ⟨tc,wt⟩ := mem_filter.mp tt
        exact mem_erase.mpr ⟨wt.ne.symm,tc⟩
      have h := card_le_card sub
      rw [card_erase_of_mem wc] at h
      have k := card_le_card (shore_neighbor_cover C wc)
      rw [card_neighborFinset_eq_degree] at k
      have l := card_insert_le a (insert b (inside G (Shore C) w))
      have r := card_insert_le b (inside G (Shore C) w)
      omega
    have m4 := low m (mem_filter.mp mk).1
    have n4 := low n (mem_filter.mp nk).1
    exact (degree m n mn).elim (fun h=>by omega) (fun h=>by omega)
  have a3 : 3≤(portColor C a).card := by change (secondShore C a).card≤1 at e1; omega
  have b3 : 3≤(portColor C b).card := by
    apply Classical.byContradiction
    intro bad
    have small : (portColor C b).card<3 := by omega
    have four : (Shore C).card=4 := by omega
    let B := portColor C b
    have count : 2≤((Shore C)\B).card := by
      have id := card_sdiff_add_card_eq_card (show B⊆Shore C from filter_subset _ _)
      have sb : B.card<3 := small
      omega
    obtain ⟨s,ss,t,tt,st⟩ := one_lt_card.mp (show 1<((Shore C)\B).card by omega)
    have low (w : V) (wm : w∈(Shore C)\B) : G.degree w<5 := by
      by_contra! hw
      obtain ⟨wc,wb⟩ := mem_sdiff.mp wm
      have nb : ¬G.Adj b w := fun h=>wb (mem_filter.mpr ⟨wc,h⟩)
      have h := inside_high_at_least_four_if_exclusive wc hw (fun e=>nb e.2)
      have sub : inside G (Shore C) w⊆(Shore C).erase w := by
        intro y ym
        obtain ⟨yc,wy⟩ := mem_filter.mp ym
        exact mem_erase.mpr ⟨wy.ne.symm,yc⟩
      have k := card_le_card sub
      rw [card_erase_of_mem wc] at k
      omega
    exact (degree s t st).elim (fun q=>by have :=low s ss; omega)
      (fun q=>by have :=low t tt; omega)
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  let S : Split G a b :=
    ⟨Shore D,Shore C,shore_disjoint cd.symm,shore_off D,shore_off C,shore_connected D,
      (fun u ud v vc e=>by
        rcases shore_closed D u ud v e with rfl|rfl|vD
        · exact (shore_off C).1 vc
        · exact (shore_off C).2 vc
        exact disjoint_left.mp (shore_disjoint cd) vc vD),
      shore_hit_a ab conn D,shore_hit_b ab conn D,(fun z=>(cover z).imp id (fun h=>h.imp id Or.symm))⟩
  have a4 := opposite_ports_at_exclusive_le_four S hc even ud au bu
  have b4 := opposite_ports_at_exclusive_le_four S.flip hc even vd bv av
  exact ⟨a3,a4,b3,b4⟩

#print axioms common_contact_range_opposite_two_three
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
