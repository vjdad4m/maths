import P5CliqueSingleEdgeFanFive133
import P5CliqueSingleEdgeSignedBudget133
import P5CliqueHighPureFan133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem one_edge_palette_at_most_eleven_high
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (edge12 : G.Adj (p 1) (p 2))
    (n10 : ¬G.Adj (p 1) (p 0)) (n20 : ¬G.Adj (p 2) (p 0))
    (n13 : ¬G.Adj (p 1) (p 3)) (n23 : ¬G.Adj (p 2) (p 3))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i) :
    (((Finset.univ : Finset V)\D).filter (fun q=>3<localIndependence G q)).card≤11 := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let H := Q.filter (fun q=>3<localIndependence G q)
  let B (i : Fin 4) := Q.filter (fun q=>(∀ x∈D,G.Adj q x↔x=p i) ∧ 3<localIndependence G q)
  let X := doubleIsolateClients G D (p 0) (p 3)
  have qo (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  let P : Finset V := {p 0,p 1,p 2,p 3}
  have inP (i : Fin 4) : p i∈P := by fin_cases i <;> simp [P]
  have att (q : V) (nq : q∉D) : ∃ x∈P,G.Adj q x := by
    obtain ⟨i,hi⟩ := attach q nq
    exact ⟨p i,inP i,hi⟩
  have pal (q : V) (nq : q∉D) (x : V) (xd : x∈D) (qx : G.Adj q x) : x∈P := by
    obtain ⟨i,rfl⟩ := palette q nq x xd qx
    exact inP i
  have attcopy := att
  choose tag htag using attcopy
  let k (q : V) := if h : q∉D then tag q h else q
  have pk (q : V) (nq : q∉D) : k q∈P ∧ G.Adj q (k q) := by simpa only [k,dif_pos nq] using htag q nq
  have pd : P⊆D := by
    intro x xm
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at xm
    rcases xm with rfl|rfl|rfl|rfl <;> apply pm
  have freeNe (i j : Fin 4) (ij : i≠j) : p i≠p j := fun e=>ij (pi e)
  have pc : P.card=4 := by
    simp [P,freeNe 0 1 (by decide),freeNe 0 2 (by decide),freeNe 0 3 (by decide),
      freeNe 1 2 (by decide),freeNe 1 3 (by decide),freeNe 2 3 (by decide)]
  have pick (q : V) (nq : q∉D) : k q∈D ∧ G.Adj q (k q) := ⟨pd (pk q nq).1,(pk q nq).2⟩
  have part : H⊆(B 0∪B 3)∪X := by
    intro q qm
    obtain ⟨qQ,hq⟩ := Finset.mem_filter.mp qm
    have nq := qo q qQ
    have n1 : ¬G.Adj q (p 1) := fun e=>(not_le_of_gt hq)
      (outside_independence_le_of_nonisolated_port h4 D k pick P pc pal q nq
        (p 1) (p 2) (pm 1) (pm 2) (inP 2) e edge12)
    have n2 : ¬G.Adj q (p 2) := fun e=>(not_le_of_gt hq)
      (outside_independence_le_of_nonisolated_port h4 D k pick P pc pal q nq
        (p 2) (p 1) (pm 2) (pm 1) (inP 1) e edge12.symm)
    have h (i j : Fin 4) (ii : i=0 ∨ i=3) (jj : j=0 ∨ j=3) (ij : i≠j)
        (qi : G.Adj q (p i)) (qj : ¬G.Adj q (p j)) : ∀ w∈D,G.Adj q w ↔ w=p i := by
      intro w wd
      constructor
      · intro qw
        obtain ⟨l,eq⟩ := palette q nq w wd qw
        have cases : l=i ∨ l=j ∨ l=1 ∨ l=2 := by
          rcases ii with e|e <;> rcases jj with f|f
          · exact (ij (e.trans f.symm)).elim
          · fin_cases l <;> simp [e,f]
          · fin_cases l <;> simp [e,f]
          · exact (ij (e.trans f.symm)).elim
        rcases cases with e|e|e|e
        · exact eq.trans (congrArg p e)
        · exact (qj (eq.trans (congrArg p e) ▸ qw)).elim
        · exact (n1 (eq.trans (congrArg p e) ▸ qw)).elim
        · exact (n2 (eq.trans (congrArg p e) ▸ qw)).elim
      · rintro rfl
        exact qi
    rcases one_edge_palette_high_isolate_dichotomy h4 D (p 0) (p 1) (p 2) (p 3)
      (pm 0) (pm 1) (pm 2) (pm 3) (freeNe 0 1 (by decide)) (freeNe 0 2 (by decide)) (freeNe 0 3 (by decide))
      (freeNe 1 3 (by decide)) (freeNe 2 3 (by decide)) edge12 att pal q nq hq with a|a|a
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨qQ,a⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨qQ,h 0 3 (Or.inl rfl) (Or.inr rfl) (by decide) a.1 a.2.1,hq⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨qQ,h 3 0 (Or.inr rfl) (Or.inl rfl) (by decide) a.1 a.2.1,hq⟩))))
  have cap (e : Fin 4 ≃ Fin 4) (e1 : e 1=1) (e2 : e 2=2)
      (x : Fin 4) (ex : e 0=x)
      (none1 : ¬G.Adj (p 1) (p (e 3))) (none2 : ¬G.Adj (p 2) (p (e 3))) :
      (B x).card≤5 := by
    let p' (i : Fin 4) := p (e i)
    let R := Q.filter (fun q=>∀ w∈D,G.Adj q w↔w=p' 3)
    have p0 : p' 0=p x := congrArg p ex
    have p1 : p' 1=p 1 := congrArg p e1
    have p2 : p' 2=p 2 := congrArg p e2
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
    have rin (r : V) (rm : r∈R) : r∉D ∧ ∀ w∈D,G.Adj r w↔w=p' 3 := by
      obtain ⟨rQ,r3⟩ := Finset.mem_filter.mp rm
      exact ⟨qo _ rQ,r3⟩
    have rall (r : V) (rm : r∈B x) : f' r 3∈R := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,family.outer _ rm _⟩,
        (family.onlyPort r rm 3)⟩
    have ed : G.Adj (p' 1) (p' 2) := by simpa [p1,p2] using edge12
    have n1 : ¬G.Adj (p' 1) (p' 3) := by simpa [p1] using none1
    have n2 : ¬G.Adj (p' 2) (p' 3) := by simpa [p2] using none2
    exact one_edge_fan_family_at_most_five h4 family ed n1 n2 R rin rall h9
  have c0 : (B 0).card≤5 := cap (Equiv.refl _) rfl rfl 0 rfl n13 n23
  have c3 : (B 3).card≤5 := cap (Equiv.swap (0:Fin 4) 3)
    (by decide) (by decide) 3 (by decide)
    (show ¬G.Adj (p 1) (p (Equiv.swap (0:Fin 4) 3 3)) by simpa using n10)
    (show ¬G.Adj (p 2) (p (Equiv.swap (0:Fin 4) 3 3)) by simpa using n20)
  have total := (Finset.card_le_card part).trans (Finset.card_union_le _ _)
  have both := Finset.card_union_le (B 0) (B 3)
  have x1 := double_isolate_clients_at_most_one h4 D (p 0) (p 3) (freeNe 0 3 (by decide))
  change X.card≤1 at x1
  change H.card≤11
  omega

#print axioms one_edge_palette_at_most_eleven_high
private theorem P7free_connected_core_budget_multi_one_edge (D : Finset V)
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

theorem one_edge_multi_attachment_ambient_mean_four_of_slack
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (edge12 : G.Adj (p 1) (p 2))
    (n10 : ¬G.Adj (p 1) (p 0)) (n20 : ¬G.Adj (p 2) (p 0))
    (n13 : ¬G.Adj (p 1) (p 3)) (n23 : ¬G.Adj (p 2) (p 3))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (slack : let Q := (Finset.univ : Finset V)\D
      (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x) +
        (∑ q∈Q,((D.filter (G.Adj q)).card-1)) + 11≤4*D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  let A := Q.filter (fun q=>3<localIndependence G q)
  have a11 : A.card≤11 := one_edge_palette_at_most_eleven_high h4 h9 D p pm pi
    edge12 n10 n20 n13 n23 attach palette
  have qa (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  choose tag htag using attach
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
  have outer : (∑ q∈Q,localIndependence G q)≤3*Q.card+11 := by
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
    exact ss.trans (Nat.add_le_add_left a11 _)
  have crossings := core_crossings_eq_card_add_extra D f (fun q qo=>⟨(pick q qo).1,(pick q qo).2.2⟩)
  change (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card+(∑ q∈Q,((D.filter (G.Adj q)).card-1)) at crossings
  change (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+
    (∑ q∈Q,((D.filter (G.Adj q)).card-1))+11≤4*D.card at slack
  have bound := core_and_exterior_independence_sum (G:=G) D
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change _≤_ + (∑ q∈Q,localIndependence G q) + (∑ q∈Q,(D.filter (G.Adj q)).card) at bound
  omega

theorem one_edge_multi_attachment_ambient_mean_four_large_core
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (edge12 : G.Adj (p 1) (p 2))
    (n10 : ¬G.Adj (p 1) (p 0)) (n20 : ¬G.Adj (p 2) (p 0))
    (n13 : ¬G.Adj (p 1) (p 3)) (n23 : ¬G.Adj (p 2) (p 3))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (Dconn : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7) (large : 17≤D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  have sub : P⊆D := by
    intro x xm
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xm
    exact pm i
  have att := attach
  choose tag htag using att
  let f (q : V) := if h : q∉D then p (tag q h) else q
  have pick (q : V) (qo : q∉D) : f q∈P ∧ G.Adj q (f q) := by
    have e : f q=p (tag q qo) := dif_pos qo
    rw [e]
    exact ⟨Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,htag q qo⟩
  have pal (q : V) (qo : q∉D) (w : V) (wd : w∈D) (qw : G.Adj q w) : w∈P := by
    obtain ⟨i,e⟩ := palette q qo w wd qw
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩
  have cap := extra_port_incidence_le_choose_pair h4 D P sub f pick pal
  have six : P.card.choose 2=6 := by rw [p4]; decide
  change (∑ q∈Q,((D.filter (G.Adj q)).card-1))≤P.card.choose 2 at cap
  have core := P7free_connected_core_budget_multi_one_edge D h4 Dconn h7
  apply one_edge_multi_attachment_ambient_mean_four_of_slack h4 h9 D p pm pi
    edge12 n10 n20 n13 n23 attach palette
  change (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+
    (∑ q∈Q,((D.filter (G.Adj q)).card-1))+11≤4*D.card
  omega

#print axioms one_edge_multi_attachment_ambient_mean_four_of_slack
#print axioms one_edge_multi_attachment_ambient_mean_four_large_core
end Graffiti133P5CliqueArms
