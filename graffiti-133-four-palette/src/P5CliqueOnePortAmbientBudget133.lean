import CambyDomBase133
import HexFlattened133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133 Graffiti133Camby
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- An independent neighborhood restricted to a one-port layer and its inward
core can use each port at most once. Two layer vertices routed through the same
port would give a square; the port itself and one layer vertex routed through
it are adjacent. -/
theorem one_port_layer_independence_charged_to_ports
    (h4 : FourCycleFree G) (D Q P : Finset V) (sub : P⊆D)
    (dis : ∀ v∈Q,v∉D) (tag : V→V)
    (route : ∀ v∈Q,tag v∈P ∧ ∀ w∈D,G.Adj v w↔w=tag v)
    {q : V} (qm : q∈Q) (S : Finset V)
    (near : ∀ v∈S,G.Adj q v ∧ (v∈D ∨ v∈Q))
    (ind : ∀ v∈S,∀ w∈S,¬G.Adj v w) : S.card≤P.card := by
  classical
  let f (v : V) := if v∈Q then tag v else v
  have hit (v : V) (vm : v∈S) : f v∈P := by
    by_cases vQ : v∈Q
    · simp only [f,if_pos vQ]
      exact (route v vQ).1
    have vD := (near v vm).2.resolve_right vQ
    have e := ((route q qm).2 v vD).mp (near v vm).1
    rw [show f v=v from if_neg vQ,e]
    exact (route q qm).1
  have inject (v : V) (vm : v∈S) (w : V) (wm : w∈S) (e : f v=f w) : v=w := by
    by_cases vQ : v∈Q
    · by_cases wQ : w∈Q
      · simp only [f,if_pos vQ,if_pos wQ] at e
        have vp := (route v vQ).1
        have pD := sub vp
        have vEdge := ((route v vQ).2 _ pD).mpr rfl
        have wEdge := ((route w wQ).2 _ pD).mpr e
        exact h4 q (tag v) v w (fun eq=>dis q qm (eq.symm ▸ pD))
          (near v vm).1 vEdge.symm (near w wm).1 wEdge.symm
      · simp only [f,if_pos vQ,if_neg wQ] at e
        have wD := (near w wm).2.resolve_right wQ
        exact ((ind v vm w wm) (((route v vQ).2 w wD).mpr e.symm)).elim
    · by_cases wQ : w∈Q
      · simp only [f,if_neg vQ,if_pos wQ] at e
        have vD := (near v vm).2.resolve_right vQ
        exact ((ind w wm v vm) (((route w wQ).2 v vD).mpr e)).elim
      · simpa only [f,if_neg vQ,if_neg wQ] using e
  have eq : (S.image f).card=S.card := Finset.card_image_of_injOn inject
  have le := Finset.card_le_card (show S.image f⊆P from by
    intro p pp
    obtain ⟨v,vm,rfl⟩ := Finset.mem_image.mp pp
    exact hit v vm)
  omega

theorem one_port_layer_localIndependence_le
    (h4 : FourCycleFree G) (D Q P : Finset V) (sub : P⊆D)
    (dis : ∀ v∈Q,v∉D) (tag : V→V)
    (route : ∀ v∈Q,tag v∈P ∧ ∀ w∈D,G.Adj v w↔w=tag v)
    {q : V} (qm : q∈Q) (closed : ∀ v,G.Adj q v→v∈D∨v∈Q) :
    localIndependence G q≤P.card := by
  classical
  unfold localIndependence
  apply Finset.sup_le_iff.mpr
  intro S sM
  have b : (∀ v∈S,G.Adj q v) ∧ (∀ v∈S,∀ w∈S,¬G.Adj v w) := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
      Finset.mem_univ,true_and] using sM
  exact one_port_layer_independence_charged_to_ports h4 D Q P sub dis tag route qm S
    (fun v vm=>⟨b.1 v vm,closed v (b.1 v vm)⟩) b.2

#print axioms one_port_layer_independence_charged_to_ports
#print axioms one_port_layer_localIndependence_le

theorem core_localIndependence_le_add_outer_degree
    (D : Finset V) (v : (D : Set V)) :
    localIndependence G v.val ≤ localIndependence (G.induce (D : Set V)) v +
      (((Finset.univ : Finset V)\D).filter (G.Adj v.val)).card := by
  classical
  unfold localIndependence
  apply Finset.sup_le_iff.mpr
  intro S sM
  have hS : (∀ x∈S,G.Adj v.val x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
      Finset.mem_univ,true_and] using sM
  let T := S.subtype (fun x=>x∈D)
  have tM : T∈localIndependentSets (G.induce (D : Set V)) v := by
    simp only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
      Finset.mem_univ,true_and]
    exact ⟨fun x hx=>hS.1 x.val (Finset.mem_subtype.mp hx),
      fun x hx y hy=>hS.2 x.val (Finset.mem_subtype.mp hx) y.val (Finset.mem_subtype.mp hy)⟩
  have le := Finset.le_sup (f:=Finset.card) tM
  rw [show T.card=(S.filter (fun x=>x∈D)).card from Finset.card_subtype _ _] at le
  have ssub : S.filter (fun x=>x∉D)⊆((Finset.univ\D).filter (G.Adj v.val)) := by
    intro x hx
    obtain ⟨xs,xd⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,xd⟩,hS.1 x xs⟩
  have lt := Finset.card_le_card ssub
  have eq := Finset.filter_card_add_filter_neg_card_eq_card (s:=S) (fun x=>x∈D)
  omega

/-- All exterior vertices have one inward port, using only the port set P.
This yields a full ambient budget from the internal core budget. -/
theorem full_one_port_layer_budget
    (h4 : FourCycleFree G) (D P : Finset V) (sub : P⊆D) (tag : V→V)
    (route : ∀ v∉D,tag v∈P ∧ ∀ w∈D,G.Adj v w↔w=tag v) :
    let Q := (Finset.univ : Finset V)\D
    (∑ v : V,localIndependence G v) ≤
      (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x) + (P.card+1)*Q.card := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let J := G.induce (D : Set V)
  let d (v : V) := (Q.filter (G.Adj v)).card
  have bQ (x : V) : x∈Q↔x∉D := by simp [Q]
  have cQ : (∑ q∈Q,localIndependence G q) ≤ Q.card*P.card := by
    calc
      _ ≤ ∑ _q∈Q,P.card := Finset.sum_le_sum (fun q qm=>
        one_port_layer_localIndependence_le h4 D Q P sub (fun v vm=>(bQ v).mp vm) tag
          (fun v vm=>route v ((bQ v).mp vm)) qm
          (fun v _=>by by_cases vd : v∈D; exact Or.inl vd; exact Or.inr ((bQ v).mpr vd)))
      _ = _ := by simp
  have dEq : (∑ v∈D,d v)=Q.card := by
    have f := Finset.card_eq_sum_card_fiberwise (f:=tag) (s:=Q) (t:=D)
      (fun u hu=>sub (route u ((bQ u).mp hu)).1)
    rw [f]
    apply Finset.sum_congr rfl
    intro v vm
    have e : Q.filter (G.Adj v) = Q.filter (fun u=>tag u=v) := by
      ext u
      simp only [Finset.mem_filter]
      refine and_congr_right (fun hu=>?_ )
      exact (SimpleGraph.adj_comm G v u).trans
        (((route u ((bQ u).mp hu)).2 v vm).trans eq_comm)
    exact congrArg Finset.card e
  have dCore : (∑ v∈D,localIndependence G v) ≤
      (∑ x : (D : Set V),localIndependence J x)+Q.card := by
    have cv (v : (D : Set V)) : localIndependence G v.val ≤ localIndependence J v+d v.val :=
      core_localIndependence_le_add_outer_degree D v
    calc
      _ = ∑ x : (D : Set V),localIndependence G x.val := Finset.sum_subtype D (fun _=>Iff.rfl) _
      _ ≤ ∑ x : (D : Set V), (localIndependence J x+d x.val) := Finset.sum_le_sum (fun x _=>cv x)
      _ = _ := by
        have conv : (∑ x : (D : Set V),d x.val) = ∑ v∈D,d v :=
          (Finset.sum_subtype (p:=fun x=>x∈D) D (fun _=>Iff.rfl) d).symm
        rw [Finset.sum_add_distrib,conv,dEq]
  have eq := Finset.sum_sdiff (Finset.subset_univ D) (f:=localIndependence G)
  change (∑ q∈Q,localIndependence G q)+(∑ x∈D,localIndependence G x)=(∑ v : V,localIndependence G v) at eq
  change _ ≤ (∑ x : (D : Set V),localIndependence J x)+(P.card+1)*Q.card
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm P.card Q.card]
  omega

theorem three_port_full_ambient_mean_four
    (h4 : FourCycleFree G) (D P : Finset V) (sub : P⊆D) (tag : V→V)
    (route : ∀ v∉D,tag v∈P ∧ ∀ w∈D,G.Adj v w↔w=tag v)
    (few : P.card≤3)
    (base : (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)≤4*D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  let Q := (Finset.univ : Finset V)\D
  have b := full_one_port_layer_budget h4 D P sub tag route
  change _ ≤ (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+(P.card+1)*Q.card at b
  have m : (P.card+1)*Q.card≤4*Q.card := Nat.mul_le_mul_right _ (by omega)
  have eq := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at eq
  change Q.card+D.card=Fintype.card V at eq
  omega

#print axioms three_port_full_ambient_mean_four

/-- The local port charge only requires the inward labels actually visible
from this vertex, not a bound on the number of ports in the whole graph. -/
theorem visible_one_port_tag_local_charge
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (route : ∀ v∉D,tag v∈D ∧ ∀ w∈D,G.Adj v w↔w=tag v)
    (q : V) (qo : q∉D) :
    let Q := insert q (((Finset.univ : Finset V)\D).filter (G.Adj q))
    localIndependence G q≤(Q.image tag).card := by
  classical
  let Q := insert q (((Finset.univ : Finset V)\D).filter (G.Adj q))
  let P := Q.image tag
  have out (v : V) (vm : v∈Q) : v∉D := by
    rcases Finset.mem_insert.mp vm with e|h
    · exact e.symm ▸ qo
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).2
  have sub : P⊆D := by
    intro p pm
    obtain ⟨v,vm,rfl⟩ := Finset.mem_image.mp pm
    exact (route v (out v vm)).1
  apply one_port_layer_localIndependence_le h4 D Q P sub out tag
  · intro v vm
    exact ⟨Finset.mem_image.mpr ⟨v,vm,rfl⟩,(route v (out v vm)).2⟩
  · exact Finset.mem_insert_self _ _
  · intro v qv
    by_cases vm : v∈D
    · exact Or.inl vm
    right
    exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,vm⟩,qv⟩)

theorem visible_three_port_ambient_mean_four
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (route : ∀ v∉D,tag v∈D ∧ ∀ w∈D,G.Adj v w↔w=tag v)
    (few : ∀ q∉D,((insert q (((Finset.univ : Finset V)\D).filter (G.Adj q))).image tag).card≤3)
    (base : (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)≤4*D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let J := G.induce (D : Set V)
  let d (v : V) := (Q.filter (G.Adj v)).card
  have bQ (x : V) : x∈Q↔x∉D := by simp [Q]
  have bq : (∑ q∈Q,localIndependence G q)≤3*Q.card := by
    calc
      _ ≤ ∑ _q∈Q,3 := Finset.sum_le_sum (fun q qm=>
        (visible_one_port_tag_local_charge h4 D tag route q ((bQ q).mp qm)).trans (few q ((bQ q).mp qm)))
      _ = _ := by simp [Nat.mul_comm]
  have dEq : (∑ v∈D,d v)=Q.card := by
    have f := Finset.card_eq_sum_card_fiberwise (f:=tag) (s:=Q) (t:=D)
      (fun u hu=>(route u ((bQ u).mp hu)).1)
    rw [f]
    apply Finset.sum_congr rfl
    intro v vm
    have e : Q.filter (G.Adj v) = Q.filter (fun u=>tag u=v) := by
      ext u
      simp only [Finset.mem_filter]
      refine and_congr_right (fun hu=>?_ )
      exact (SimpleGraph.adj_comm G v u).trans
        (((route u ((bQ u).mp hu)).2 v vm).trans eq_comm)
    exact congrArg Finset.card e
  have dCore : (∑ v∈D,localIndependence G v) ≤
      (∑ x : (D : Set V),localIndependence J x)+Q.card := by
    have cv (v : (D : Set V)) : localIndependence G v.val ≤ localIndependence J v+d v.val :=
      core_localIndependence_le_add_outer_degree D v
    calc
      _ = ∑ x : (D : Set V),localIndependence G x.val := Finset.sum_subtype D (fun _=>Iff.rfl) _
      _ ≤ ∑ x : (D : Set V), (localIndependence J x+d x.val) := Finset.sum_le_sum (fun x _=>cv x)
      _ = _ := by
        have conv : (∑ x : (D : Set V),d x.val) = ∑ v∈D,d v :=
          (Finset.sum_subtype (p:=fun x=>x∈D) D (fun _=>Iff.rfl) d).symm
        rw [Finset.sum_add_distrib,conv,dEq]
  have eq := Finset.sum_sdiff (Finset.subset_univ D) (f:=localIndependence G)
  change (∑ q∈Q,localIndependence G q)+(∑ x∈D,localIndependence G x)=(∑ v : V,localIndependence G v) at eq
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change (∑ x : (D : Set V),localIndependence J x)≤4*D.card at base
  omega

#print axioms visible_three_port_ambient_mean_four

theorem three_port_P7free_core_ambient_mean_four
    (h4 : FourCycleFree G) (D P : Finset V) (sub : P⊆D) (tag : V→V)
    (route : ∀ v∉D,tag v∈P ∧ ∀ w∈D,G.Adj v w↔w=tag v)
    (few : P.card≤3)
    (conn : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let J := G.induce (D : Set V)
  have four : FourCycleFree J := by
    intro a b x y ne ax bx ay by'
    exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
  have eq : Fintype.card (D : Set V)=D.card := Fintype.card_coe _
  have three : (∑ x : (D : Set V),localIndependence J x)≤3*D.card := by
    by_contra h
    have high : 3*Fintype.card (D : Set V)<∑ x : (D : Set V),localIndependence J x := by omega
    have mean : 3<averageLocal J := by
      letI := conn.nonempty
      have pos : (0:ℚ)<(Fintype.card (D : Set V):ℚ) := by exact_mod_cast Fintype.card_pos (α:=(D : Set V))
      unfold averageLocal
      apply (lt_div_iff₀ pos).mpr
      rw [← Nat.cast_sum]
      exact_mod_cast high
    exact h7 (Graffiti133Revisit.P7_of_strict_mean_three J conn four mean)
  apply three_port_full_ambient_mean_four h4 D P sub tag route few
  exact three.trans (by omega)

#print axioms three_port_P7free_core_ambient_mean_four

theorem visible_three_port_P7free_core_ambient_mean_four
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (route : ∀ v∉D,tag v∈D ∧ ∀ w∈D,G.Adj v w↔w=tag v)
    (few : ∀ q∉D,((insert q (((Finset.univ : Finset V)\D).filter (G.Adj q))).image tag).card≤3)
    (conn : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let J := G.induce (D : Set V)
  have four : FourCycleFree J := by
    intro a b x y ne ax bx ay by'
    exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
  have eq : Fintype.card (D : Set V)=D.card := Fintype.card_coe _
  have three : (∑ x : (D : Set V),localIndependence J x)≤3*D.card := by
    by_contra h
    have high : 3*Fintype.card (D : Set V)<∑ x : (D : Set V),localIndependence J x := by omega
    have mean : 3<averageLocal J := by
      letI := conn.nonempty
      have pos : (0:ℚ)<(Fintype.card (D : Set V):ℚ) := by exact_mod_cast Fintype.card_pos (α:=(D : Set V))
      unfold averageLocal
      apply (lt_div_iff₀ pos).mpr
      rw [← Nat.cast_sum]
      exact_mod_cast high
    exact h7 (Graffiti133Revisit.P7_of_strict_mean_three J conn four mean)
  apply visible_three_port_ambient_mean_four h4 D tag route few
  exact three.trans (by omega)

#print axioms visible_three_port_P7free_core_ambient_mean_four

/-- Quantitative ambient budget with variable visible-port counts. -/
theorem full_visible_port_ambient_budget
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (route : ∀ v∉D,tag v∈D ∧ ∀ w∈D,G.Adj v w↔w=tag v) :
    let Q := (Finset.univ : Finset V)\D
    (∑ v : V,localIndependence G v)≤
      (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x) +
        Q.card + (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card) := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let J := G.induce (D : Set V)
  let d (v : V) := (Q.filter (G.Adj v)).card
  have bQ (x : V) : x∈Q↔x∉D := by simp [Q]
  have bq : (∑ q∈Q,localIndependence G q)≤
      (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card) :=
    Finset.sum_le_sum (fun q qm=>visible_one_port_tag_local_charge h4 D tag route q ((bQ q).mp qm))
  have dEq : (∑ v∈D,d v)=Q.card := by
    have f := Finset.card_eq_sum_card_fiberwise (f:=tag) (s:=Q) (t:=D)
      (fun u hu=>(route u ((bQ u).mp hu)).1)
    rw [f]
    apply Finset.sum_congr rfl
    intro v vm
    have e : Q.filter (G.Adj v) = Q.filter (fun u=>tag u=v) := by
      ext u
      simp only [Finset.mem_filter]
      refine and_congr_right (fun hu=>?_ )
      exact (SimpleGraph.adj_comm G v u).trans
        (((route u ((bQ u).mp hu)).2 v vm).trans eq_comm)
    exact congrArg Finset.card e
  have dCore : (∑ v∈D,localIndependence G v) ≤
      (∑ x : (D : Set V),localIndependence J x)+Q.card := by
    have cv (v : (D : Set V)) : localIndependence G v.val ≤ localIndependence J v+d v.val :=
      core_localIndependence_le_add_outer_degree D v
    calc
      _ = ∑ x : (D : Set V),localIndependence G x.val := Finset.sum_subtype D (fun _=>Iff.rfl) _
      _ ≤ ∑ x : (D : Set V), (localIndependence J x+d x.val) := Finset.sum_le_sum (fun x _=>cv x)
      _ = _ := by
        have conv : (∑ x : (D : Set V),d x.val) = ∑ v∈D,d v :=
          (Finset.sum_subtype (p:=fun x=>x∈D) D (fun _=>Iff.rfl) d).symm
        rw [Finset.sum_add_distrib,conv,dEq]
  have eq := Finset.sum_sdiff (Finset.subset_univ D) (f:=localIndependence G)
  change (∑ q∈Q,localIndependence G q)+(∑ x∈D,localIndependence G x)=(∑ v : V,localIndependence G v) at eq
  change _≤(∑ x : (D : Set V),localIndependence J x)+Q.card+
    (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card)
  omega
#print axioms full_visible_port_ambient_budget

theorem visible_port_weighted_slack_P7free_ambient_mean_four
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (route : ∀ v∉D,tag v∈D ∧ ∀ w∈D,G.Adj v w↔w=tag v)
    (slack :
      let Q := (Finset.univ : Finset V)\D
      (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card)≤3*Q.card+D.card)
    (conn : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let J := G.induce (D : Set V)
  have four : FourCycleFree J := by
    intro a b x y ne ax bx ay by'
    exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
  have eq : Fintype.card (D : Set V)=D.card := Fintype.card_coe _
  have three : (∑ x : (D : Set V),localIndependence J x)≤3*D.card := by
    by_contra h
    have high : 3*Fintype.card (D : Set V)<∑ x : (D : Set V),localIndependence J x := by omega
    have mean : 3<averageLocal J := by
      letI := conn.nonempty
      have pos : (0:ℚ)<(Fintype.card (D : Set V):ℚ) := by exact_mod_cast Fintype.card_pos (α:=(D : Set V))
      unfold averageLocal
      apply (lt_div_iff₀ pos).mpr
      rw [← Nat.cast_sum]
      exact_mod_cast high
    exact h7 (Graffiti133Revisit.P7_of_strict_mean_three J conn four mean)
  let Q := (Finset.univ : Finset V)\D
  have out := full_visible_port_ambient_budget h4 D tag route
  change _≤(∑ x : (D : Set V),localIndependence J x)+Q.card+
    (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card) at out
  change (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card)≤3*Q.card+D.card at slack
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  omega

#print axioms visible_port_weighted_slack_P7free_ambient_mean_four

theorem visible_port_count_le_one_add_cross_tag_degree
    (Q : Finset V) (tag : V→V) (q : V) :
    ((insert q (Q.filter (G.Adj q))).image tag).card ≤
      1+(Q.filter (fun v=>G.Adj q v ∧ tag v≠tag q)).card := by
  classical
  let F := Q.filter (fun v=>G.Adj q v ∧ tag v≠tag q)
  have sub : (insert q (Q.filter (G.Adj q))).image tag⊆insert (tag q) (F.image tag) := by
    intro a am
    obtain ⟨v,vm,rfl⟩ := Finset.mem_image.mp am
    rcases Finset.mem_insert.mp vm with h|h
    · exact h.symm ▸ Finset.mem_insert_self _ _
    obtain ⟨vm,n⟩ := Finset.mem_filter.mp h
    by_cases eq : tag v=tag q
    · exact eq.symm ▸ Finset.mem_insert_self _ _
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨vm,n,eq⟩,rfl⟩)
  exact (Finset.card_le_card sub).trans
    ((Finset.card_insert_le _ _).trans (by
      change (F.image tag).card+1≤1+F.card
      have h : (F.image tag).card≤F.card := Finset.card_image_le
      omega))

/-- It suffices that the total degree through unlike labels in the outside
layer is at most twice that layer's order, plus the core order. -/
theorem cross_tag_degree_cap_P7free_ambient_mean_four
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (route : ∀ v∉D,tag v∈D ∧ ∀ w∈D,G.Adj v w↔w=tag v)
    (cap : let Q := (Finset.univ : Finset V)\D
      (∑ q∈Q,(Q.filter (fun v=>G.Adj q v ∧ tag v≠tag q)).card)≤2*Q.card+D.card)
    (conn : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  apply visible_port_weighted_slack_P7free_ambient_mean_four h4 D tag route _ conn h7
  classical
  let Q := (Finset.univ : Finset V)\D
  change (∑ q∈Q,(Q.filter (fun v=>G.Adj q v ∧ tag v≠tag q)).card)≤2*Q.card+D.card at cap
  change (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card)≤3*Q.card+D.card
  have a : (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card) ≤
      ∑ q∈Q,(1+(Q.filter (fun v=>G.Adj q v ∧ tag v≠tag q)).card) :=
    Finset.sum_le_sum (fun q _=>visible_port_count_le_one_add_cross_tag_degree Q tag q)
  rw [Finset.sum_add_distrib] at a
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at a
  omega

#print axioms cross_tag_degree_cap_P7free_ambient_mean_four
end Graffiti133P5CliqueArms
