import C7MultiWeightedGlobal133
import NestedCoreWeightedCreditCount133
import NestedCoreWeightedLocalCredit133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133MultiWeighted Graffiti133BicycleCharge
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

omit [LinearOrder V] in
theorem profile_credit_bound_two (H : Hole G 7) (h4 : FourCycleFree G) (u v : V)
    (h : (scoredFar H u v).card≤2) :
    (∑ x∈multiVertices H,profileCredit H u v x)≤11 := by
  classical
  unfold profileCredit
  rw [Finset.sum_add_distrib]
  have ae : (∑ x∈multiVertices H, if x∈adjTwo H then (1:Nat) else 0)=(adjTwo H).card := by
    rw [←Finset.sum_filter]
    have eq : ((multiVertices H).filter (·∈adjTwo H))=adjTwo H := by
      ext x
      exact Finset.mem_filter.trans ⟨fun p=>p.2,fun p=>⟨(Finset.mem_filter.mp p).1,p⟩⟩
    simp [eq]
  have be : (∑ x∈multiVertices H, if x∈scoredFar H u v then (2:Nat) else 0)=2*(scoredFar H u v).card := by
    rw [←Finset.sum_filter]
    have eq : ((multiVertices H).filter (·∈scoredFar H u v))=scoredFar H u v := by
      ext x
      exact Finset.mem_filter.trans ⟨fun p=>p.2,fun p=>⟨(Finset.mem_filter.mp p).1,p⟩⟩
    simp [eq,Nat.mul_comm]
  rw [ae,be]
  have r := adjacent_two_bound H h4
  omega


private theorem profile_credit_eq_two (H : Hole G 7) (u v w : V) (xm : w∈multiVertices H) :
    (if (contactSet H w).card=2 then
      if (∃ i∈contactSet H w,∃ j∈contactSet H w,Cyclic i j) then 1
      else if (decide (w=u ∨ w=v) : Bool) then 0 else 2
    else 0)=profileCredit H u v w := by
  classical
  have aa : w∈adjTwo H ↔ (contactSet H w).card=2 ∧
      ∃ i∈contactSet H w,∃ j∈contactSet H w,Cyclic i j := by
    simp only [adjTwo,Finset.mem_filter,xm,true_and]
  have ff : w∈scoredFar H u v ↔ (contactSet H w).card=2 ∧
      (¬∃ i∈contactSet H w,∃ j∈contactSet H w,Cyclic i j) ∧ w≠u ∧ w≠v := by
    simp only [scoredFar,Finset.mem_filter,xm,true_and]
  by_cases t : (contactSet H w).card=2
  · by_cases a : ∃ i∈contactSet H w,∃ j∈contactSet H w,Cyclic i j
    · have am := aa.mpr ⟨t,a⟩
      have fm : w∉scoredFar H u v := fun h=>(ff.mp h).2.1 a
      simp only [profileCredit,t,a,am,fm,if_true,if_false,add_zero]
    · have am : w∉adjTwo H := fun h=>a (aa.mp h).2
      by_cases b : w=u ∨ w=v
      · have pt : (decide (w=u ∨ w=v) : Bool)=true := decide_eq_true b
        have fm : w∉scoredFar H u v := by
          intro e
          obtain ⟨_,_,nu,nv⟩ := ff.mp e
          exact b.elim nu nv
        simp only [profileCredit,t,a,am,fm,pt,if_true,if_false,add_zero]
      · have pf : (decide (w=u ∨ w=v) : Bool)=false := decide_eq_false b
        have fm := ff.mpr ⟨t,a,fun e=>b (Or.inl e),fun e=>b (Or.inr e)⟩
        simp only [profileCredit,t,a,am,fm,pf,Bool.false_eq_true,if_true,if_false,zero_add]
  · have am : w∉adjTwo H := fun h=>t (aa.mp h).1
    have fm : w∉scoredFar H u v := fun h=>t (ff.mp h).1
    simp only [profileCredit,t,am,fm,if_false,add_zero]

private theorem incidence_independent {W : Type*} [Fintype W] (J : SimpleGraph W) (x : W)
    (d e : DecidableEq W) (a b : DecidableRel J.Adj) :
    @Graffiti133ExteriorSlack.triangleIncidence W _ d J a x=
      @Graffiti133ExteriorSlack.triangleIncidence W _ e J b x := by
  rw [show d=e from Subsingleton.elim _ _,show a=b from Subsingleton.elim _ _]

private theorem finish_local_charge (d r t k c : Nat) (de : r=d) (ce : k=c)
    (loc : 2*r≤4+3*t+k) : 2*d≤4+3*t+c := by omega

private theorem refined_near_local_per_two (H : Hole G 7) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (u v : V)
    (short : ∀ x∈adjTwo H,(exteriorNeighbors H x).card≤2)
    (far : ∀ x : V, (x=u ∨ x=v) → (contactSet H x).card=2 →
      (¬∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) →
      ((exteriorNeighbors H x) \ markedNeighbors H x).card=0)
    (U : Finset V) (x : (U : Set V)) (cycle : ∀ i,H.c i∈U) (xm : x.val∈multiVertices H) :
    2*(G.induce (U : Set V)).degree x ≤ 4+
      3*Graffiti133ExteriorSlack.triangleIncidence (G.induce (U : Set V)) x+profileCredit H u v x.val := by
  classical
  let J := G.induce (U : Set V)
  let B := restrictedHole H U cycle
  have allDom (y : (U : Set V)) (off : Outside B.c y) : ∃ i,J.Adj y (B.c i) :=
    dom y.val (fun i e=>off i (Subtype.ext e))
  have xoff : Outside B.c x := fun i e=>(Finset.mem_filter.mp xm).2.1 i (congrArg Subtype.val e)
  have eq : contactSet B x=contactSet H x.val := restricted_contacts H U cycle x
  have high : 2≤(contactSet B x).card := by rw [eq]; exact (Finset.mem_filter.mp xm).2.2
  have extMap (y : (U : Set V)) (ym : y∈exteriorNeighbors B x) : y.val∈exteriorNeighbors H x.val := by
    obtain ⟨_,off,hit⟩ := Finset.mem_filter.mp ym
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i e=>off i (Subtype.ext e),hit⟩
  have cleanMap (y : (U : Set V))
      (ym : y∈(exteriorNeighbors B x) \ markedNeighbors B x) :
      y.val∈(exteriorNeighbors H x.val) \ markedNeighbors H x.val := by
    obtain ⟨out,no⟩ := Finset.mem_sdiff.mp ym
    refine Finset.mem_sdiff.mpr ⟨extMap y out,?_⟩
    rintro yes
    obtain ⟨_,i,hit,hj⟩ := Finset.mem_filter.mp yes
    apply no
    exact Finset.mem_filter.mpr ⟨out,i,by rwa [eq],hj⟩
  have countExt : (exteriorNeighbors B x).card≤(exteriorNeighbors H x.val).card :=
    Finset.card_le_card_of_injOn Subtype.val extMap (by intro a _ b _ e; exact Subtype.ext e)
  have countClean : ((exteriorNeighbors B x) \ markedNeighbors B x).card≤
      ((exteriorNeighbors H x.val) \ markedNeighbors H x.val).card :=
    Finset.card_le_card_of_injOn Subtype.val cleanMap (by intro a _ b _ e; exact Subtype.ext e)
  let pr : Bool := decide (x.val=u ∨ x.val=v)
  have localB := improved_multi_local_credit B (restricted_c4 h4 U) allDom x xoff high pr
    (fun hh=>countExt.trans (short x.val (Finset.mem_filter.mpr ⟨xm,by rwa [←eq]⟩)))
    (by
      intro yes two non
      rw [eq] at two non
      have hz := Nat.eq_zero_of_le_zero (countClean.trans (le_of_eq (far _ (of_decide_eq_true yes) two non)))
      simpa only [Finset.card_eq_zero,Finset.sdiff_eq_empty_iff_subset] using hz)
  let chosen : Nat :=
    if (contactSet B x).card=2 then
      if (∃ i∈contactSet B x,∃ j∈contactSet B x,Cyclic i j) then 1
      else if pr then 0 else 2
    else 0
  have ce : chosen=profileCredit H u v x.val := by
    dsimp only [chosen]
    rw [eq]
    exact profile_credit_eq_two H u v x.val xm
  have deg : row J x Finset.univ=J.degree x := row_is_degree x
  let tri := @Graffiti133ExteriorSlack.triangleIncidence (U : Set V) _
    (fun a b=>Classical.propDecidable (a=b)) J (fun a b=>Classical.propDecidable (J.Adj a b)) x
  let official := Graffiti133ExteriorSlack.triangleIncidence J x
  have ti : tri=official := incidence_independent J x _ _ _ _
  have bound : 2*row J x Finset.univ≤4+3*tri+chosen := localB
  have t : 2*J.degree x ≤ 4+3*tri+profileCredit H u v x.val :=
    finish_local_charge (J.degree x) (row J x Finset.univ) tri chosen (profileCredit H u v x.val) deg ce bound
  change 2*J.degree x ≤ 4+3*official+profileCredit H u v x.val
  exact t.trans (congrArg (fun n : Nat=>4+3*n+profileCredit H u v x.val) ti).le


theorem refined_near_base_slack_two (H : Hole G 7) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (u v : V) (remaining : (scoredFar H u v).card≤2)
    (short : ∀ x∈adjTwo H,(exteriorNeighbors H x).card≤2)
    (far : ∀ x : V, (x=u ∨ x=v) → (contactSet H x).card=2 →
      (¬∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) →
      ((exteriorNeighbors H x) \ markedNeighbors H x).card=0) :
    (∑ x : V,localIndependence G x)+3≤4*Fintype.card V := by
  classical
  have total := sum_local_plus_custom_slack H h4 h9 dom (fun _=>0) (profileCredit H u v) (by
    intro U x cycle xm
    rw [add_zero]
    exact refined_near_local_per_two H h4 dom u v short far U x cycle xm) 
  simp only [Finset.sum_const_zero,add_zero] at total
  have cap := profile_credit_bound_two H h4 u v remaining
  exact (by omega : ∀ {l n w : Nat}, l+14≤4*n+w → w≤11 → l+3≤4*n) total cap

#print axioms refined_near_base_slack_two
end Graffiti133NestedWeightedCore
