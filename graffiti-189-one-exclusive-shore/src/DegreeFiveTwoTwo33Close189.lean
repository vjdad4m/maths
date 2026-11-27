import DegreeFiveTwoTwoLow33
import DegreeFiveTwoTwoNonmixed189
import DegreeFiveTwoTwoMixed189
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

/-- The exact common (3,3) versus exclusive (2,2) case is traceable. -/
theorem traceable_of_balanced_three_three_opposite_two_two
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2≤(sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (cA : (portColor C a).card=3) (cB : (portColor C b).card=3)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=2) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  obtain ⟨sh,_,_,_,_,size,oneA,oneB⟩ :=
    two_two_common_shore_geometry hc two even conn degree cd cover shared none pA pB
  obtain ⟨_,ca,cb,z,zc,za,zb,low⟩ :=
    low_nonporter_of_three_three_opposite_two_two hc degree sh size oneA oneB cA cB
  have high (w : V) (wd : w∈Shore D) : 5≤G.degree w := by
    have ne : w≠z := fun e=>disjoint_left.mp (shore_disjoint cd) zc (e ▸ wd)
    exact (degree w z ne).resolve_right (by omega)
  obtain ⟨u,up⟩ := card_pos.mp (show 0<(portColor D a).card by omega)
  obtain ⟨v,vp⟩ := card_pos.mp (show 0<(portColor D b).card by omega)
  obtain ⟨ud,au⟩ := mem_filter.mp up
  obtain ⟨vd,bv⟩ := mem_filter.mp vp
  have hu := charge_at_high_port (.inl ⟨rfl,rfl⟩) hc ud au (high u ud)
  have hv := charge_at_high_port (.inr ⟨rfl,rfl⟩) hc vd bv (high v vd)
  rw [if_neg (fun bu=>none u ud ⟨au,bu⟩)] at hu
  rw [if_neg (fun av=>none v vd ⟨av,bv⟩)] at hv
  change 5≤(portColor D a).card+(secondShore D a).card at hu
  change 5≤(portColor D b).card+(secondShore D b).card at hv
  have ba : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have ea := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have eb := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ ba even
  have eA : (secondShore D a).card=3 := by omega
  have eB : (secondShore D b).card=3 := by omega
  have small : (Shore D).card≤7 := by
    by_cases mixed : ∃ i∈portColor D a,∃ j∈portColor D b,G.Adj i j
    · obtain ⟨i,ip,j,jp,ij⟩ := mixed
      obtain ⟨x,xp⟩ := card_pos.mp (show 0<(sharedPortSet C).card by omega)
      obtain ⟨xc,ax,bx⟩ := mem_filter.mp xp
      exact two_two_mixed_small_of_tight_shells hc two even conn cd none pA pB eA eB ca cb
        high xc ax bx ip jp ij
    have nonmix (i : V) (ip : i∈portColor D a) (j : V) (jp : j∈portColor D b) :
        ¬G.Adj i j := fun ij=>mixed ⟨i,ip,j,jp,ij⟩
    exact two_two_nonmixed_small_of_low_both hc two even cd none nonmix cA pA pB eA eB high zc za zb
  exact traceable_of_balanced_exclusive_shore_at_most_seven hc two even conn degree cd cover
    shared none (by omega) (by omega) small

#print axioms traceable_of_balanced_three_three_opposite_two_two
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
