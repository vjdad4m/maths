import DegreeFiveShapeThreeFour189
import DegreeFiveNonmixedThreeFour189
import DegreeFiveBalancedSmallRoute189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_disjoint from DegreeFiveActualCut189
open private secondShore charge_at_high_port anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The common (3,4) versus exclusive (2,3) profile is traceable. Four
foreign contacts occur on the side with three exclusive contacts. -/
theorem traceable_of_balanced_three_four_opposite_two_three
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2≤(sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (cA : (portColor C a).card=3) (cB : (portColor C b).card=4)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_cases mixed : ∃ u∈portColor D a,∃ v∈portColor D b,G.Adj u v
  · obtain ⟨u,up,v,vp,uv⟩ := mixed
    obtain ⟨ud,au⟩ := mem_filter.mp up
    obtain ⟨vd,bv⟩ := mem_filter.mp vp
    exact traceable_of_balanced_mixed_shore_at_four_foreign hc two even conn degree cd cover
      shared none (by omega) (by omega) (.inr ⟨rfl,rfl⟩) vd bv ud au uv.symm (by omega) cB
  have nonmix (u : V) (up : u∈portColor D a) (v : V) (vp : v∈portColor D b) :
      ¬G.Adj u v := fun uv=>mixed ⟨u,up,v,vp,uv⟩
  obtain ⟨_,one,_,z,zc,za,zb,low⟩ :=
    low_b_porter_of_three_four_opposite_two_three hc two even degree cd shared none cA cB pA pB
  have high (w : V) (wd : w∈Shore D) : 5≤G.degree w := by
    have n : w≠z := fun e=>disjoint_left.mp (shore_disjoint cd) zc (e ▸ wd)
    exact (degree w z n).resolve_right (by omega)
  obtain ⟨u,up⟩ := card_pos.mp (show 0<(portColor D a).card by omega)
  obtain ⟨ud,au⟩ := mem_filter.mp up
  have hu := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc ud au (high u ud)
  rw [if_neg (fun bu=>none u ud ⟨au,bu⟩)] at hu
  change 5≤(portColor D a).card+(secondShore D a).card at hu
  have cap := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have shell : (secondShore D a).card=3 := by omega
  exact (no_nonmixed_at_three_four_opposite_two_three hc two even cd none nonmix pA pB
    cB shell high zc za zb).elim

#print axioms traceable_of_balanced_three_four_opposite_two_three
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
