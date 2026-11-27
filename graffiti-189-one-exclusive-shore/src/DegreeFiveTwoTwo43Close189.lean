import DegreeFiveActualCutSwap189
import DegreeFiveTwoTwoLow43
import DegreeFiveTwoTwoNonmixed34
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

/-- The exact common (4,3) versus exclusive (2,2) case is traceable. -/
theorem traceable_of_balanced_four_three_opposite_two_two
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2≤(sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (cA : (portColor C a).card=4) (cB : (portColor C b).card=3)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=2) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_cases mixed : ∃ u∈portColor D a,∃ v∈portColor D b,G.Adj u v
  · obtain ⟨u,ua,v,vb,uv⟩ := mixed
    obtain ⟨ud,au⟩ := mem_filter.mp ua
    obtain ⟨vd,bv⟩ := mem_filter.mp vb
    exact traceable_of_balanced_mixed_shore_at_four_foreign hc two even conn degree cd cover
      shared none (by omega) (by omega) (.inl ⟨rfl,rfl⟩) ud au vd bv uv (by omega) cA
  exfalso
  obtain ⟨sh,_,_,_,_,size,_,oneB⟩ :=
    two_two_common_shore_geometry hc two even conn degree cd cover shared none pA pB
  obtain ⟨_,cb,z,zc,az,bz,low⟩ :=
    low_a_porter_of_four_three_opposite_two_two hc conn degree sh size oneB cA cB
  have high (w : V) (wd : w∈Shore D) : 5≤G.degree w := by
    have ne : w≠z := fun e=>disjoint_left.mp (shore_disjoint cd) zc (e ▸ wd)
    exact (degree w z ne).resolve_right (by omega)
  obtain ⟨v,vp⟩ := card_pos.mp (show 0<(portColor D b).card by omega)
  obtain ⟨vd,bv⟩ := mem_filter.mp vp
  have hv := charge_at_high_port (.inr ⟨rfl,rfl⟩) hc vd bv (high v vd)
  rw [if_neg (fun av=>none v vd ⟨av,bv⟩)] at hv
  change 5≤(portColor D b).card+(secondShore D b).card at hv
  have rev : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have eb := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ rev even
  have eB : (secondShore D b).card=3 := by omega
  let C' := swapCut C
  let D' := swapCut D
  have C_eq : Shore C'=Shore C := shore_swapCut C
  have D_eq : Shore D'=Shore D := shore_swapCut D
  have cc (c : V) : portColor C' c=portColor C c := by simp [portColor,C_eq]
  have dp (c : V) : portColor D' c=portColor D c := by simp [portColor,D_eq]
  have ds (c : V) : secondShore D' c=secondShore D c := by simp [secondShore,D_eq]
  have cd' : C'≠D' := fun h=>cd (swapCut.injective h)
  have none' (w : V) (wd : w∈Shore D') (p : G.Adj b w ∧ G.Adj a w) : False :=
    none w (D_eq ▸ wd) ⟨p.2,p.1⟩
  have nonmix' (v : V) (vb : v∈portColor D' b) (u : V) (ua : u∈portColor D' a) :
      ¬G.Adj v u := fun vu=>mixed ⟨u,dp a ▸ ua,v,dp b ▸ vb,vu.symm⟩
  exact no_nonmixed_at_three_four_opposite_two_two (a:=b) (b:=a) hc rev even cd' none'
    nonmix' (by rw [dp]; exact pB) (by rw [dp]; exact pA)
    (by rw [cc]; exact cA) (by rw [ds]; exact eB)
    (fun w wd=>high w (D_eq ▸ wd)) (C_eq.symm ▸ zc) bz az

#print axioms traceable_of_balanced_four_three_opposite_two_two
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
