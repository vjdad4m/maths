import DegreeFiveReverseGeometry189
import DegreeFiveReverseTwoShell189
import DegreeFiveReverseThreeShell189
import DegreeFiveBalancedSmallRoute189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset ArticulationPair
open private Shore shore_off shore_disjoint from DegreeFiveActualCut189
open private secondShore charge_at_high_port anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private sharedPortSet inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Exact reverse alignment completes the (4,3) common versus (2,3)
exclusive contact profile. -/
theorem traceable_of_balanced_four_three_opposite_two_three
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2≤(sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (cA : (portColor C a).card=4) (cB : (portColor C b).card=3)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_cases mixed : ∃ u∈portColor D a,∃ v∈portColor D b,G.Adj u v
  · obtain ⟨u,up,v,vp,uv⟩ := mixed
    obtain ⟨ud,au⟩ := mem_filter.mp up
    obtain ⟨vd,bv⟩ := mem_filter.mp vp
    exact traceable_of_balanced_mixed_shore_at_four_foreign hc two even conn degree cd cover
      shared none (by omega) (by omega) (.inl ⟨rfl,rfl⟩) ud au vd bv uv (by omega) cA
  exfalso
  have nonmix (u : V) (up : u∈portColor D a) (v : V) (vp : v∈portColor D b) :
      ¬G.Adj u v := fun uv=>mixed ⟨u,up,v,vp,uv⟩
  obtain ⟨c4,c5,ca,cb⟩ := reverse_common_shore_geometry hc two even degree
    cd shared none cA cB pA pB
  have ba : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have ea := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have eb := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ ba even
  obtain ⟨u,up,u5⟩ := anywhere_high_of_two degree (show 2≤(portColor D a).card by omega)
  obtain ⟨v,vp,v5⟩ := anywhere_high_of_two degree (show 2≤(portColor D b).card by omega)
  obtain ⟨ud,au⟩ := mem_filter.mp up
  obtain ⟨vd,bv⟩ := mem_filter.mp vp
  have p := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc ud au u5
  have q := charge_at_high_port (.inr ⟨rfl,rfl⟩) hc vd bv v5
  rw [if_neg (fun bu=>none u ud ⟨au,bu⟩)] at p
  rw [if_neg (fun av=>none v vd ⟨av,bv⟩)] at q
  change 5≤(portColor D a).card+(secondShore D a).card at p
  change 5≤(portColor D b).card+(secondShore D b).card at q
  have dis : Disjoint (portColor D a) (portColor D b) := by
    apply disjoint_left.mpr
    intro w wa wb
    exact none w (mem_filter.mp wa).1 ⟨(mem_filter.mp wa).2,(mem_filter.mp wb).2⟩
  have union : portColor D a ∪ portColor D b = cutPorts D := by
    ext w
    simp [portColor,cutPorts,and_or_left]
  have five : (cutPorts D).card=5 := by rw [←union,card_union_of_disjoint dis,pA,pB]
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<(sharedPortSet C).card by omega)
  obtain ⟨xc,ax,bx⟩ := mem_filter.mp xm
  have near := exclusive_nonports_in_cut_shells_at_five hc even cd xc ax bx five
  rw [←union] at near
  by_cases big : (Shore C).card=5
  · exact no_tight_shells_in_reverse_alignment hc two even degree cd none nonmix cA cB pA pB
      (by omega) (by omega) near
  have cEq : (Shore C).card=4 := by omega
  have aEq : portColor C a=Shore C := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have existsZ : ¬ Shore C ⊆ portColor C b := by
    intro h
    have l := card_le_card h
    omega
  obtain ⟨z,zc,zn⟩ := not_subset.mp existsZ
  have az : G.Adj a z := (mem_filter.mp (show z∈portColor C a by rwa [aEq])).2
  have nb : ¬G.Adj b z := fun h=>zn (mem_filter.mpr ⟨zc,h⟩)
  have zl : G.degree z<5 := by
    by_contra! hz
    have h := inside_high_at_least_four_if_exclusive zc hz (fun e=>nb e.2)
    have sub : inside G (Shore C) z ⊆ (Shore C).erase z := by
      intro w wm
      obtain ⟨wc,zw⟩ := mem_filter.mp wm
      exact mem_erase.mpr ⟨zw.ne.symm,wc⟩
    have lim := card_le_card sub
    rw [card_erase_of_mem zc] at lim
    omega
  have high (w : V) (wd : w∈Shore D) : 5≤G.degree w := by
    have wz : w≠z := fun e=>disjoint_left.mp (shore_disjoint cd) zc (e ▸ wd)
    exact (degree w z wz).resolve_right (by omega)
  by_cases f2 : (secondShore D b).card=2
  · exact no_two_b_shell_in_all_high_reverse hc two even cd none nonmix cA pA pB
      (by omega) f2 near high
  have f3 : (secondShore D b).card=3 := by omega
  have xz : x≠z := fun e=>nb (e ▸ bx)
  have xz' := common_universal_in_shore_at_five hc even cd xc ax bx five z zc xz
  have bz : G.dist z b=2 := by
    have bw : b≠z := fun e=>(shore_off C).2
      (Eq.mp (congrArg (fun v : V => v∈Shore C) e.symm) zc)
    have db := d2 hc bw nb bx xz'
    have h := (mem_filter.mp db).2
    rwa [SimpleGraph.dist_comm]
  obtain ⟨e,ee,ef⟩ := overlapping_shells_at_three_b_in_reverse hc two even cd none nonmix
    pA f3 zc az bz
  exact no_three_b_shell_in_all_high_reverse hc two even cd none nonmix cA cB pA pB
    (by omega) f3 high ee ef

#print axioms traceable_of_balanced_four_three_opposite_two_three
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
