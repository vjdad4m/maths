import C7MultiP8AdjCharge133
import C7MultiWeightedGlobal133
import C7MultiProfileCap133

namespace Graffiti133MultiP8
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133MultiWeighted
  Graffiti133ExteriorSlack Graffiti133BicycleCharge
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option maxRecDepth 100000
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

private theorem adjacent_rotation : ∀ A : Finset (Fin 7), C4Allowed A→A.card=2→
    (∃ i∈A,∃ j∈A,Cyclic i j)→∃ i,A={i,i+1} := by decide

private theorem far_rotation : ∀ A : Finset (Fin 7), C4Allowed A→A.card=2→
    (¬∃ i∈A,∃ j∈A,Cyclic i j)→∃ i,A={i,i+3} := by decide

noncomputable def p8Credit (H : Hole G 7) (x : V) : Nat :=
  if (contactSet H x).card=3 then 0 else
  if (∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) then 1 else 2

private theorem p8_credit_budget (H : Hole G 7) (h4 : FourCycleFree G)
    (h8 : ¬∃ p : Fin 8→V,InducedPath G p) : (∑ x∈multiVertices H,p8Credit H x)≤14 := by
  classical
  let D := multiVertices H
  let R (x : V) := ∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j
  let A := D.filter (fun x=>(contactSet H x).card=2 ∧ R x)
  let F := D.filter (fun x=>(contactSet H x).card=2 ∧ ¬R x)
  have ha (x : V) (xm : x∈A) : Outside H.c x ∧ ∃ i,contactSet H x={i,i+1} := by
    obtain ⟨d,t,r⟩ := Finset.mem_filter.mp xm
    have xout := (Finset.mem_filter.mp d).2.1
    exact ⟨xout,adjacent_rotation _ (contacts_are_allowed H h4 x xout) t r⟩
  have hf (x : V) (xm : x∈F) : Outside H.c x ∧ ∃ i,contactSet H x={i,i+3} := by
    obtain ⟨d,t,r⟩ := Finset.mem_filter.mp xm
    have xout := (Finset.mem_filter.mp d).2.1
    exact ⟨xout,far_rotation _ (contacts_are_allowed H h4 x xout) t r⟩
  have cap := pair_vertex_weight_cap H h4 h8 A F ha hf
  have cost (x : V) (xm : x∈D) :
      p8Credit H x=((if (contactSet H x).card=2 ∧ R x then 1 else 0) +
        (if (contactSet H x).card=2 ∧ ¬R x then 2 else 0)) := by
    have m := (Finset.mem_filter.mp xm).2
    rcases geometry_cap _ (contacts_are_allowed H h4 x m.1) m.2 with ⟨two,_⟩|⟨three,_⟩
    · by_cases yes : R x
      · simp only [p8Credit,two,show ¬(2:Nat)=3 by decide,if_false,if_true,
          show (∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) from yes,yes,
          true_and,not_true_eq_false,add_zero]
      · simp only [p8Credit,two,show ¬(2:Nat)=3 by decide,if_false,if_true,
          show ¬(∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) from yes,yes,
          true_and,not_false_eq_true,zero_add]
    · simp only [p8Credit,three,show ¬(3:Nat)=2 by decide,false_and,if_false,if_true,add_zero]
  have sA : (∑ x∈D,if (contactSet H x).card=2 ∧ R x then (1:Nat) else 0)=A.card :=
    (Finset.card_filter _ D).symm
  have sF : (∑ x∈D,if (contactSet H x).card=2 ∧ ¬R x then (2:Nat) else 0)=2*F.card := by
    rw [←Finset.sum_filter]
    change (∑ x∈F,(2:Nat))=_
    simp [Nat.mul_comm]
  change (∑ x∈D,p8Credit H x)≤14
  rw [Finset.sum_congr (s₁:=D) rfl cost,Finset.sum_add_distrib,sA,sF]
  exact cap

private theorem subhost_P8_charge [LinearOrder V] (H : Hole G 7)
    (h4 : FourCycleFree G) (h8 : ¬∃ p : Fin 8→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (U : Finset V) (y : (U : Set V)) (cy : ∀ i,H.c i∈U)
    (md : y.val∈multiVertices H) :
    2*(G.induce (U : Set V)).degree y+0≤4+3*triangleIncidence (G.induce (U : Set V)) y+
      p8Credit H y.val := by
  classical
  let J := G.induce (U : Set V)
  let HR := restrictedHole H U cy
  have eq : contactSet HR y=contactSet H y.val := restricted_contacts H U cy y
  have out : Outside HR.c y := fun i e=>(Finset.mem_filter.mp md).2.1 i (congrArg Subtype.val e)
  have localDom (z : (U : Set V)) (zo : Outside HR.c z) :
      ∃ i,J.Adj z (HR.c i) := dom z.val (fun i e=>zo i (Subtype.ext e))
  have no8 : ¬∃ p : Fin 8→(U : Set V),InducedPath J p := by
    rintro ⟨p,l⟩
    exact h8 ⟨Subtype.val ∘ p,Subtype.val_injective.comp l.1,l.2⟩
  have two : 2≤(contactSet HR y).card := by rw [eq]; exact (Finset.mem_filter.mp md).2.2
  have l4 := restricted_c4 h4 U
  rcases geometry_cap _ (contacts_are_allowed HR l4 y out) two with ⟨pt,_⟩|⟨tt,_⟩
  · have amb : (contactSet H y.val).card=2 := by rw [←eq]; exact pt
    by_cases near : ∃ i∈contactSet HR y,∃ j∈contactSet HR y,Cyclic i j
    · have an : ∃ i∈contactSet H y.val,∃ j∈contactSet H y.val,Cyclic i j := by rw [←eq]; exact near
      have loc := P8_free_adjacent_multi_charge HR l4 no8 localDom y out pt near
      rw [row_is_any_degree (G.induce (U:Set V)) y,
        incidence_classical_eq (G.induce (U:Set V)) y] at loc
      have c1 : p8Credit H y.val=1 := by
        simp only [p8Credit,amb,show ¬(2:Nat)=3 by decide,if_false,an,if_true]
      rw [c1,Nat.add_zero]
      exact loc
    · have an : ¬∃ i∈contactSet H y.val,∃ j∈contactSet H y.val,Cyclic i j := by rw [←eq]; exact near
      have loc := local_multi_weight HR l4 localDom y out two
      rw [row_is_any_degree (G.induce (U:Set V)) y,
        incidence_classical_eq (G.induce (U:Set V)) y] at loc
      simp only [pt,show ¬(2:Nat)=3 by decide,if_false,near,add_zero] at loc
      have c2 : p8Credit H y.val=2 := by
        simp only [p8Credit,amb,show ¬(2:Nat)=3 by decide,if_false,an]
      rw [c2,Nat.add_zero]
      exact loc
  · have amb : (contactSet H y.val).card=3 := by rw [←eq]; exact tt
    have loc := local_multi_weight HR l4 localDom y out two
    rw [row_is_any_degree (G.induce (U:Set V)) y,
        incidence_classical_eq (G.induce (U:Set V)) y] at loc
    simp only [tt,if_true,add_zero] at loc
    have c0 : p8Credit H y.val=0 := by simp only [p8Credit,amb,if_true]
    simp only [c0,Nat.add_zero]
    exact (Nat.le_succ _).trans loc

theorem P8_free_dominating_C7_mean_four (H : Hole G 7) (h4 : FourCycleFree G)
    (h8 : ¬∃ p : Fin 8→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i)) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let e := Fintype.equivFin V
  letI : LinearOrder V := LinearOrder.lift' e e.injective
  have no9 : ¬∃ p : Fin 9→V,InducedPath G p := by
    rintro ⟨p,h⟩
    exact h8 (Graffiti133Revisit.trim_path (by decide) h)
  have whole := sum_local_plus_custom_slack H h4 no9 dom (fun _=>0) (p8Credit H)
    (subhost_P8_charge H h4 h8 dom)
  simp only [Finset.sum_const_zero,Nat.add_zero] at whole
  have credit := p8_credit_budget H h4 h8
  exact Nat.le_of_add_le_add_right (whole.trans (Nat.add_le_add_left credit _))

#print axioms P8_free_dominating_C7_mean_four
end Graffiti133MultiP8
