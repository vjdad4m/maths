import P5CliqueIndependentFanLift133
import P5CliqueSmallCoreSignedSlack133
import P5CliqueHighPureFan133
import P5CliqueMultiPortBudget133
import HexFlattened133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem independent_four_port_high_mixed_bound
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i) :
    let Q := (Finset.univ : Finset V)\D
    (Q.filter (fun q=>3<localIndependence G q)).card≤8+
      (∑ q∈Q,((D.filter (G.Adj q)).card-1)) := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let pure (q : V) (i : Fin 4) := ∀ x∈D,G.Adj q x↔x=p i
  let H := Q.filter (fun q=>3<localIndependence G q)
  let B (i : Fin 4) := Q.filter (fun q=>pure q i ∧ 3<localIndependence G q)
  let M := Q.filter (fun q=>¬∃ i,pure q i)
  have qo (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have part : H⊆(Finset.univ.biUnion B)∪M := by
    intro q qm
    obtain ⟨qQ,hq⟩ := Finset.mem_filter.mp qm
    by_cases one : ∃i,pure q i
    · obtain ⟨i,hi⟩ := one
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨qQ,hi,hq⟩⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨qQ,one⟩))
  have caps (x : Fin 4) : (B x).card≤2 := by
    let e := Equiv.swap 0 x
    let p' (i : Fin 4) := p (e i)
    have p0 : p' 0=p x := by simp [p',e]
    have at' (q : V) (nq : q∉D) : ∃ i,G.Adj q (p' i) := by
      obtain ⟨i,hi⟩ := attach q nq
      exact ⟨e.symm i,by simpa [p'] using hi⟩
    have pa' (q : V) (nq : q∉D) (w : V) (wd : w∈D) (qw : G.Adj q w) : ∃ i,w=p' i := by
      obtain ⟨i,hi⟩ := palette q nq w wd qw
      exact ⟨e.symm i,by simpa [p'] using hi⟩
    have exFan (q : {q : V // q∈B x}) :
        ∃ f : Fin 4→V, f 0=q.val ∧ (∀ i,f i∉D) ∧
          (∀ i w,w∈D→(G.Adj (f i) w↔w=p' i)) ∧ ∀ i j,i<j→(G.Adj (f i) (f j)↔i=0) := by
      obtain ⟨qQ,qx,qh⟩ := Finset.mem_filter.mp q.property
      have hom (w : V) (wd : w∈D) : G.Adj q.val w↔w=p' 0 := by rw [p0]; exact qx w wd
      exact high_single_site_has_clean_four_port_fan h4 D p' (fun i=>pm (e i))
        (pi.comp e.injective) at' pa' q.val (qo _ qQ) hom qh
    choose f fc fo fp fs using exFan
    let f' (q : V) (i : Fin 4) := if h : q∈B x then f ⟨q,h⟩ i else q
    have family : PortFanFamily G (D : Set V) p' (B x) f' := by
      refine ⟨(fun i=>pm (e i)),pi.comp e.injective,?_,?_,?_,?_⟩
      · intro q qm i
        simpa only [f',dif_pos qm] using fo ⟨q,qm⟩ i
      · intro q qm
        simpa only [f',dif_pos qm] using fc ⟨q,qm⟩
      · intro q qm i w wd
        simpa only [f',dif_pos qm] using fp ⟨q,qm⟩ i w wd
      · intro q qm i j ij
        simpa only [f',dif_pos qm] using fs ⟨q,qm⟩ i j ij
    exact independent_palette_at_most_two_fans h4 h9 family (fun i j=>ind (e i) (e j))
  have u8 : (Finset.univ.biUnion B).card≤8 := by
    calc
      _≤∑ i:Fin 4,(B i).card := Finset.card_biUnion_le
      _≤∑ _i:Fin 4,2 := Finset.sum_le_sum (fun i _=>caps i)
      _=8 := by decide
  have mixedtwo (q : V) (qm : q∈M) : 2≤(D.filter (G.Adj q)).card := by
    obtain ⟨qQ,notpure⟩ := Finset.mem_filter.mp qm
    obtain ⟨i,qi⟩ := attach q (qo _ qQ)
    by_cases yes : 2≤(D.filter (G.Adj q)).card
    · exact yes
    exfalso
    apply notpure
    refine ⟨i,fun w wd=>⟨?_,fun e=>e.symm ▸ qi⟩⟩
    intro qw
    have one := Finset.card_le_one.mp (show (D.filter (G.Adj q)).card≤1 by omega)
    exact one w (Finset.mem_filter.mpr ⟨wd,qw⟩) (p i) (Finset.mem_filter.mpr ⟨pm i,qi⟩)
  have mel : M.card≤∑ q∈Q,((D.filter (G.Adj q)).card-1) := by
    have hs : (∑ q∈Q,(if q∈M then 1 else 0 : Nat))=M.card := by
      rw [←Finset.card_filter]
      congr 1
      ext q
      simp only [Finset.mem_filter,M]
      tauto
    rw [←hs]
    apply Finset.sum_le_sum
    intro q _
    by_cases h : q∈M
    · rw [if_pos h]
      have e := mixedtwo q h
      omega
    · simp [h]
  have e := (Finset.card_le_card part).trans (Finset.card_union_le _ _)
  change H.card≤8+∑ q∈Q,((D.filter (G.Adj q)).card-1)
  omega

#print axioms independent_four_port_high_mixed_bound
theorem independent_four_port_high_mixed_exact
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i) :
    let Q := (Finset.univ : Finset V)\D
    (Q.filter (fun q=>3<localIndependence G q)).card≤8+
      (Q.filter (fun q=>3<localIndependence G q ∧ 2≤(D.filter (G.Adj q)).card)).card := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let pure (q : V) (i : Fin 4) := ∀ x∈D,G.Adj q x↔x=p i
  let H := Q.filter (fun q=>3<localIndependence G q)
  let B (i : Fin 4) := Q.filter (fun q=>pure q i ∧ 3<localIndependence G q)
  let M := Q.filter (fun q=>3<localIndependence G q ∧ ¬∃ i,pure q i)
  have qo (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have part : H⊆(Finset.univ.biUnion B)∪M := by
    intro q qm
    obtain ⟨qQ,hq⟩ := Finset.mem_filter.mp qm
    by_cases one : ∃i,pure q i
    · obtain ⟨i,hi⟩ := one
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨qQ,hi,hq⟩⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨qQ,hq,one⟩))
  have caps (x : Fin 4) : (B x).card≤2 := by
    let e := Equiv.swap 0 x
    let p' (i : Fin 4) := p (e i)
    have p0 : p' 0=p x := by simp [p',e]
    have at' (q : V) (nq : q∉D) : ∃ i,G.Adj q (p' i) := by
      obtain ⟨i,hi⟩ := attach q nq
      exact ⟨e.symm i,by simpa [p'] using hi⟩
    have pa' (q : V) (nq : q∉D) (w : V) (wd : w∈D) (qw : G.Adj q w) : ∃ i,w=p' i := by
      obtain ⟨i,hi⟩ := palette q nq w wd qw
      exact ⟨e.symm i,by simpa [p'] using hi⟩
    have exFan (q : {q : V // q∈B x}) :
        ∃ f : Fin 4→V, f 0=q.val ∧ (∀ i,f i∉D) ∧
          (∀ i w,w∈D→(G.Adj (f i) w↔w=p' i)) ∧ ∀ i j,i<j→(G.Adj (f i) (f j)↔i=0) := by
      obtain ⟨qQ,qx,qh⟩ := Finset.mem_filter.mp q.property
      have hom (w : V) (wd : w∈D) : G.Adj q.val w↔w=p' 0 := by rw [p0]; exact qx w wd
      exact high_single_site_has_clean_four_port_fan h4 D p' (fun i=>pm (e i))
        (pi.comp e.injective) at' pa' q.val (qo _ qQ) hom qh
    choose f fc fo fp fs using exFan
    let f' (q : V) (i : Fin 4) := if h : q∈B x then f ⟨q,h⟩ i else q
    have family : PortFanFamily G (D : Set V) p' (B x) f' := by
      refine ⟨(fun i=>pm (e i)),pi.comp e.injective,?_,?_,?_,?_⟩
      · intro q qm i
        simpa only [f',dif_pos qm] using fo ⟨q,qm⟩ i
      · intro q qm
        simpa only [f',dif_pos qm] using fc ⟨q,qm⟩
      · intro q qm i w wd
        simpa only [f',dif_pos qm] using fp ⟨q,qm⟩ i w wd
      · intro q qm i j ij
        simpa only [f',dif_pos qm] using fs ⟨q,qm⟩ i j ij
    exact independent_palette_at_most_two_fans h4 h9 family (fun i j=>ind (e i) (e j))
  have u8 : (Finset.univ.biUnion B).card≤8 := by
    calc
      _≤∑ i:Fin 4,(B i).card := Finset.card_biUnion_le
      _≤∑ _i:Fin 4,2 := Finset.sum_le_sum (fun i _=>caps i)
      _=8 := by decide
  have mixedtwo (q : V) (qm : q∈M) : 2≤(D.filter (G.Adj q)).card := by
    obtain ⟨qQ,_,notpure⟩ := Finset.mem_filter.mp qm
    obtain ⟨i,qi⟩ := attach q (qo _ qQ)
    by_cases yes : 2≤(D.filter (G.Adj q)).card
    · exact yes
    exfalso
    apply notpure
    refine ⟨i,fun w wd=>⟨?_,fun e=>e.symm ▸ qi⟩⟩
    intro qw
    have one := Finset.card_le_one.mp (show (D.filter (G.Adj q)).card≤1 by omega)
    exact one w (Finset.mem_filter.mpr ⟨wd,qw⟩) (p i) (Finset.mem_filter.mpr ⟨pm i,qi⟩)
  let C := Q.filter (fun q=>3<localIndependence G q ∧ 2≤(D.filter (G.Adj q)).card)
  have mC : M⊆C := by
    intro q qm
    obtain ⟨qQ,hq,_⟩ := Finset.mem_filter.mp qm
    exact Finset.mem_filter.mpr ⟨qQ,hq,mixedtwo q qm⟩
  have e := (Finset.card_le_card part).trans (Finset.card_union_le _ _)
  have mc := Finset.card_le_card mC
  change H.card≤8+C.card
  omega

#print axioms independent_four_port_high_mixed_exact
private theorem P7free_connected_core_budget_independent (D : Finset V)
    (h4 : FourCycleFree G) (hc : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)≤3*D.card := by
  classical
  let J := G.induce (D : Set V)
  have four : FourCycleFree J := by
    intro a b x y ne ax bx ay by'
    exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
  have eq : Fintype.card (D : Set V)=D.card := Fintype.card_coe _
  change (∑ x : (D : Set V),localIndependence J x)≤3*D.card
  by_contra h
  have high : 3*Fintype.card (D : Set V)<∑ x : (D : Set V),localIndependence J x := by omega
  have mean : 3<averageLocal J := by
    letI := hc.nonempty
    have pos : (0:ℚ)<(Fintype.card (D : Set V):ℚ) := by exact_mod_cast Fintype.card_pos (α:=(D : Set V))
    unfold averageLocal
    apply (lt_div_iff₀ pos).mpr
    rw [← Nat.cast_sum]
    exact_mod_cast high
  exact h7 (Graffiti133Revisit.P7_of_strict_mean_three J hc four mean)

theorem independent_four_port_ambient_of_joint_slack
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (slack : let Q := (Finset.univ : Finset V)\D
      (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+8+
        2*(∑ q∈Q,((D.filter (G.Adj q)).card-1))≤4*D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  let A := Q.filter (fun q=>3<localIndependence G q)
  let extra := ∑ q∈Q,((D.filter (G.Adj q)).card-1)
  have a8 : A.card≤8+extra := independent_four_port_high_mixed_bound h4 h9 D p pm pi ind attach palette
  have qa (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have copy := attach
  choose tag htag using copy
  let f (q : V) := if h : q∉D then p (tag q h) else q
  have pick (q : V) (qo : q∉D) : f q∈D ∧ f q∈P ∧ G.Adj q (f q) := by
    have e : f q=p (tag q qo) := dif_pos qo
    rw [e]
    exact ⟨pm _,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,htag q qo⟩
  have palette' (q : V) (qo : q∉D) (w : V) (wd : w∈D) (qw : G.Adj q w) : w∈P := by
    obtain ⟨i,e⟩ := palette q qo w wd qw
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩
  have localCap (q : V) (qo : q∉D) : localIndependence G q≤4 :=
    p4 ▸ outside_independence_le_attachment_palette h4 D P f pick palette' q qo
  have outer : (∑ q∈Q,localIndependence G q)≤3*Q.card+(8+extra) := by
    have point (q : V) (qm : q∈Q) : localIndependence G q≤3+(if q∈A then 1 else 0) := by
      by_cases high : 3<localIndependence G q
      · rw [if_pos (Finset.mem_filter.mpr ⟨qm,high⟩)]
        exact localCap q (qa q qm)
      · have hA : q∉A := fun e=>high (Finset.mem_filter.mp e).2
        rw [if_neg hA]
        omega
    have ss := Finset.sum_le_sum point
    rw [Finset.sum_add_distrib] at ss
    have hsum : (∑ q∈Q,(if q∈A then 1 else 0 : Nat))=A.card := by
      rw [←Finset.card_filter]
      congr 1
      ext q
      simp only [Finset.mem_filter,A]
      tauto
    have cs : (∑ _q∈Q,(3:Nat))=3*Q.card := by simp [Nat.mul_comm]
    rw [hsum,cs] at ss
    exact ss.trans (Nat.add_le_add_left a8 _)
  have crossings := core_crossings_eq_card_add_extra D f (fun q qo=>⟨(pick q qo).1,(pick q qo).2.2⟩)
  change (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card+(∑ q∈Q,((D.filter (G.Adj q)).card-1)) at crossings
  have bound := core_and_exterior_independence_sum (G:=G) D
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card+extra at crossings
  change (∑ v : V,localIndependence G v)≤
    (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+
      (∑ q∈Q,localIndependence G q)+(∑ q∈Q,(D.filter (G.Adj q)).card) at bound
  change (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+8+2*extra≤4*D.card at slack
  omega

#print axioms independent_four_port_ambient_of_joint_slack
theorem independent_four_port_at_most_one_extra_ambient_mean_four
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (Dconn : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7)
    (few : (∑ q∈(Finset.univ : Finset V)\D,((D.filter (G.Adj q)).card-1))≤1) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  have sub : P⊆D := by
    intro x xm
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xm
    exact pm i
  have d4 : 4≤D.card := by have le := Finset.card_le_card sub; omega
  let J := G.induce (D : Set V)
  have ce : Fintype.card (D : Set V)=D.card := Fintype.card_coe D
  have slack : (∑ x : (D : Set V),localIndependence J x)+10≤4*D.card := by
    by_cases large : 10≤D.card
    · have core := P7free_connected_core_budget_independent D h4 Dconn h7
      change (∑ x : (D : Set V),localIndependence J x)≤3*D.card at core
      omega
    · have j4 : FourCycleFree J := by
        intro a b x y ne ax bx ay by'
        exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
      letI : DecidableRel J.Adj := Classical.decRel _
      have z := small_core_ten_signed_slack (G:=J) (by omega) (by omega) j4
      rw [ce] at z
      exact z
  apply independent_four_port_ambient_of_joint_slack h4 h9 D p pm pi ind attach palette
  change (∑ x : (D : Set V),localIndependence J x)+8+
    2*(∑ q∈(Finset.univ : Finset V)\D,((D.filter (G.Adj q)).card-1))≤4*D.card
  omega

#print axioms independent_four_port_at_most_one_extra_ambient_mean_four

/-- With at least twenty vertices in the connected P7-free core, the
same-label two-fan cap absorbs every multivalent attachment. -/
theorem independent_four_port_large_core_ambient_mean_four
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (Dconn : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7) (d20 : 20≤D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  have sub : P⊆D := by
    intro x xm
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xm
    exact pm i
  have copy := attach
  choose tag htag using copy
  let f (q : V) := if h : q∉D then p (tag q h) else q
  have fProp (q : V) (qo : q∉D) : f q∈P ∧ G.Adj q (f q) := by
    rw [show f q=p (tag q qo) from dif_pos qo]
    exact ⟨Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,htag q qo⟩
  have pProp (q : V) (qo : q∉D) (x : V) (xd : x∈D) (qx : G.Adj q x) : x∈P := by
    obtain ⟨i,e⟩ := palette q qo x xd qx
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩
  have exc := extra_port_incidence_le_choose_pair h4 D P sub f fProp pProp
  change (∑ q∈(Finset.univ : Finset V)\D,((D.filter (G.Adj q)).card-1))≤P.card.choose 2 at exc
  rw [p4] at exc
  have exc6 : (∑ q∈(Finset.univ : Finset V)\D,((D.filter (G.Adj q)).card-1))≤6 := exc
  have cf := P7free_connected_core_budget_independent D h4 Dconn h7
  apply independent_four_port_ambient_of_joint_slack h4 h9 D p pm pi ind attach palette
  change (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+8+
    2*(∑ q∈(Finset.univ : Finset V)\D,((D.filter (G.Adj q)).card-1))≤4*D.card
  omega

#print axioms independent_four_port_large_core_ambient_mean_four
end Graffiti133P5CliqueArms
