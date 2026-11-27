import C7MultiWeightedGlobal133
import C7MultiRadius4Caps133
import C7MultiWeightedLocal133

namespace Graffiti133MultiWeighted
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133BicycleCharge
  Graffiti133ExteriorSlack
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem incidence_classical_eq {W : Type*} [Fintype W]
    (J : SimpleGraph W) [d : DecidableEq W] [a : DecidableRel J.Adj] (y : W) :
    @triangleIncidence W _ (fun u v=>Classical.propDecidable (u=v)) J
      (fun u v=>Classical.propDecidable (J.Adj u v)) y = triangleIncidence J y := by
  have hd : (fun u v : W=>Classical.propDecidable (u=v)) = d := Subsingleton.elim _ _
  have ha : (fun u v : W=>Classical.propDecidable (J.Adj u v)) = a := Subsingleton.elim _ _
  cases hd
  cases ha
  rfl

private theorem row_is_any_degree {W : Type*} [Fintype W]
    (J : SimpleGraph W) [a : DecidableRel J.Adj] (y : W) :
    row J y Finset.univ = J.degree y := by
  have ha : (fun u v : W=>Classical.propDecidable (J.Adj u v)) = a := Subsingleton.elim _ _
  cases ha
  exact row_is_degree y

private theorem restrict_degree_le (U : Finset V) (x : (U : Set V)) :
    (G.induce (U : Set V)).degree x≤G.degree x.val := by
  classical
  rw [←(G.induce (U : Set V)).card_neighborFinset_eq_degree,←G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro y ym
    exact (G.mem_neighborFinset _ _).mpr ((G.induce (U : Set V)).mem_neighborFinset _ _ |>.mp ym)
  · exact Subtype.val_injective.injOn

private theorem contact_triangle_positive (H : Hole G 7) (x : V)
    (adj : ∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) : 1≤triangleIncidence G x := by
  classical
  obtain ⟨i,im,j,jm,ij⟩ := adj
  apply Finset.card_pos.mpr
  refine ⟨{x,H.c i,H.c j},Finset.mem_filter.mpr ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨(mem_contactSet H _ _).mp im,(mem_contactSet H _ _).mp jm,
      (H.adj i j).mpr ij⟩),by simp⟩⟩

private noncomputable def radiusCredit (H : Hole G 7) (x : V) : Nat :=
  if (∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) then 1 else 2

private theorem radiusCredit_sum (H : Hole G 7) :
    (∑ x∈multiVertices H,radiusCredit H x)=(adjacentMulti H).card+2*(farMulti H).card := by
  classical
  let D := multiVertices H
  let A (x : V) := ∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j
  have row (x : V) : radiusCredit H x=(if A x then 1 else 0)+(if ¬A x then 2 else 0) := by
    by_cases yes : A x
    · simp only [radiusCredit,show (∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) from yes,
        if_true,not_true_eq_false,if_false,add_zero,yes]
    · simp only [radiusCredit,show ¬(∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) from yes,
        yes,if_false,if_true,zero_add,not_false_eq_true]
  have sa : (∑ x∈D,if A x then (1:Nat) else 0)=(adjacentMulti H).card := by
    exact (Finset.card_filter A D).symm
  have sf : (∑ x∈D,if ¬A x then (2:Nat) else 0)=2*(farMulti H).card := by
    rw [←Finset.sum_filter]
    change (∑ x∈farMulti H,(2:Nat))=_
    simp [Nat.mul_comm]
  calc
    _ = ∑ x∈D,((if A x then 1 else 0)+(if ¬A x then 2 else 0)) :=
      Finset.sum_congr rfl (fun x _=>row x)
    _ = _ := by rw [Finset.sum_add_distrib,sa,sf]

private theorem adjacent_radius_arithmetic {d t : Nat} (d4 : d≤4) (t1 : 1≤t) :
    2*d≤4+3*t+1 := by omega

private theorem radius_four_view_step [LinearOrder V] (H : Hole G 7) (hc : G.Connected)
    (h4 : FourCycleFree G) (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (hr : 4≤radius G) (U : Finset V) (y : (U : Set V)) (cy : ∀ i,H.c i∈U)
    (md : y.val∈multiVertices H) :
    2*(G.induce (U : Set V)).degree y+0≤4+3*triangleIncidence (G.induce (U : Set V)) y+
      radiusCredit H y.val := by
  classical
  let J := G.induce (U : Set V)
  let HR := restrictedHole H U cy
  have out : Outside HR.c y := fun i eq=>(Finset.mem_filter.mp md).2.1 i (congrArg Subtype.val eq)
  have cap := radius_four_multi_degree_caps H hc h4 dom hr y.val md
  have eq : contactSet HR y=contactSet H y.val := restricted_contacts H U cy y
  have two : (contactSet HR y).card=2 := eq.symm ▸ cap.1
  have localDom (z : (U : Set V)) (zo : Outside HR.c z) :
      ∃ i,J.Adj z (HR.c i) := dom z.val (fun i e=>zo i (Subtype.ext e))
  change 2*J.degree y+0≤4+3*triangleIncidence J y+radiusCredit H y.val
  by_cases adj : ∃ i∈contactSet H y.val,∃ j∈contactSet H y.val,Cyclic i j
  · have aj : ∃ i∈contactSet HR y,∃ j∈contactSet HR y,Cyclic i j := by rw [eq]; exact adj
    have tri := contact_triangle_positive (G:=G.induce (U:Set V)) HR y aj
    rw [incidence_classical_eq (G.induce (U:Set V)) y] at tri
    have dg : J.degree y≤G.degree y.val := restrict_degree_le (G:=G) U y
    have sp : G.degree y.val=(contactSet H y.val).card+(exteriorNeighbors H y.val).card := by
      rw [←row_is_degree (G:=G),split_degree_contacts H]
    have four : G.degree y.val≤4 := by rw [sp,cap.1]; omega
    have c1 : radiusCredit H y.val=1 := if_pos adj
    rw [c1,Nat.add_zero]
    exact adjacent_radius_arithmetic (dg.trans four) tri
  · have bad : ¬∃ i∈contactSet HR y,∃ j∈contactSet HR y,Cyclic i j := by rwa [eq]
    have loc := local_multi_weight (G:=G.induce (U:Set V)) HR (restricted_c4 h4 U) localDom y out (by rw [two])
    rw [row_is_any_degree (G.induce (U:Set V)) y,
      incidence_classical_eq (G.induce (U:Set V)) y] at loc
    simp only [two,show ¬(2:Nat)=3 by decide,bad,if_false,add_zero] at loc
    have c2 : radiusCredit H y.val=2 := if_neg adj
    rw [c2,Nat.add_zero]
    exact loc

theorem radius_four_dominating_C7_mean_four (H : Hole G 7) (hc : G.Connected)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i)) (hr : 4≤radius G) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let e := Fintype.equivFin V
  letI : LinearOrder V := LinearOrder.lift' e e.injective
  have p := radius_four_pair_profile_counts H hc h4 dom hr
  have budget := radiusCredit_sum H
  have all := sum_local_plus_custom_slack H h4 h9 dom (fun _=>0) (radiusCredit H)
    (radius_four_view_step H hc h4 dom hr)
  simp only [Finset.sum_const_zero,Nat.add_zero] at all
  omega

theorem dominating_C7_radius_three_or_mean_four (H : Hole G 7) (hc : G.Connected)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i)) :
    radius G≤3 ∨ (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  by_cases r : radius G≤3
  · exact Or.inl r
  · exact Or.inr (radius_four_dominating_C7_mean_four H hc h4 h9 dom (by omega))

#print axioms radius_four_dominating_C7_mean_four
#print axioms dominating_C7_radius_three_or_mean_four
end Graffiti133MultiWeighted
