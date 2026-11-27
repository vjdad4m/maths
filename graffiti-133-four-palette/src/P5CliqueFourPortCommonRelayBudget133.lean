import P5CliqueFourPortCommonRelayFans133
import P5CliqueMultiPortBudget133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem common_relay_forces_singleton_attachment
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V) (t : V) (td : t∈D)
    (relay : ∀ i,G.Adj t (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (q : V) (qo : q∉D) (i : Fin 4) (qi : G.Adj q (p i)) :
    ∀ w∈D,G.Adj q w↔w=p i := by
  intro w wm
  constructor
  · intro qw
    obtain ⟨j,rfl⟩ := palette q qo w wm qw
    by_contra ne
    exact qo ((h4 (p j) (p i) q t ne qw.symm qi.symm (relay j).symm (relay i).symm).symm ▸ td)
  · rintro rfl
    exact qi

theorem high_clients_at_one_relay_port_at_most_six
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (t : V) (td : t∈D) (relay : ∀ i,G.Adj t (p i))
    (far : ¬G.Adj (p 2) (p 3))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (noP9 : NoPath G 9) :
    (((Finset.univ : Finset V)\D).filter
      (fun q=>G.Adj q (p 0) ∧ 3<localIndependence G q)).card≤6 := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let A := Q.filter (fun q=>G.Adj q (p 0) ∧ 3<localIndependence G q)
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  choose lab hlab using attach
  let tag (q : V) := if h : q∉D then p (lab q h) else q
  have pick (q : V) (qo : q∉D) : tag q∈D ∧ tag q∈P ∧ G.Adj q (tag q) := by
    have e : tag q=p (lab q qo) := dif_pos qo
    rw [e]
    exact ⟨pm _,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,hlab q qo⟩
  have single (q : V) (qo : q∉D) (i : Fin 4) (qi : G.Adj q (p i)) :
      ∀ w∈D,G.Adj q w↔w=p i :=
    common_relay_forces_singleton_attachment h4 D p t td relay palette q qo i qi
  have finfo (q : {q : V // q∈A}) :
      ∃ fn : Fin 4→V,fn 0=q.val ∧
        (∀ i,fn i∉D) ∧
        (∀ i x,x∈D→(G.Adj (fn i) x↔x=p i)) ∧
        ∀ i j,i<j→(G.Adj (fn i) (fn j)↔i=0) := by
    obtain ⟨qQ,qa,high⟩ := Finset.mem_filter.mp q.property
    have qo := (Finset.mem_sdiff.mp qQ).2
    have ne : (localIndependentSets G q.val).Nonempty := by
      refine ⟨∅,?_⟩
      simp [localIndependentSets]
    obtain ⟨S,hS,sval⟩ := Finset.exists_mem_eq_sup _ ne Finset.card
    have sc : S.card≥4 := by
      change localIndependence G q.val=S.card at sval
      omega
    have info : (∀ x∈S,G.Adj q.val x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) := by
      simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,
        Finset.subset_iff,Finset.mem_univ,true_and] using hS
    let g (x : V) := if x∈D then x else tag x
    have hit (x : V) (xm : x∈S) : g x∈P := by
      by_cases xd : x∈D
      · obtain ⟨i,ix⟩ := palette q.val qo x xd (info.1 _ xm)
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simpa only [g,if_pos xd] using ix.symm⟩
      · simpa only [g,if_neg xd] using (pick x xd).2.1
    have inj : Set.InjOn g (S : Set V) := by
      intro v vm w wm e
      by_cases vd : v∈D
      · by_cases wd : w∈D
        · simpa only [g,if_pos vd,if_pos wd] using e
        simp only [g,if_pos vd,if_neg wd] at e
        exact ((info.2 w wm v vm) (e.symm ▸ (pick w wd).2.2)).elim
      by_cases wd : w∈D
      · simp only [g,if_neg vd,if_pos wd] at e
        exact ((info.2 v vm w wm) (e ▸ (pick v vd).2.2)).elim
      simp only [g,if_neg vd,if_neg wd] at e
      have qn : q.val≠tag v := fun eq=>qo (eq.symm ▸ (pick v vd).1)
      exact h4 q.val (tag v) v w qn (info.1 _ vm) (pick v vd).2.2.symm
        (info.1 _ wm) (e.symm ▸ (pick w wd).2.2).symm
    have sub : S.image g⊆P := by
      intro v vm
      obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp vm
      exact hit w wm
    have im := Finset.card_image_of_injOn inj
    have eq : S.image g=P := Finset.eq_of_subset_of_card_le sub (by omega)
    have repr (i : Fin 4) (i0 : i≠0) : ∃ x∈S,x∉D ∧ G.Adj x (p i) := by
      have M : p i∈S.image g := eq.symm ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      obtain ⟨x,xS,xg⟩ := Finset.mem_image.mp M
      have xo : x∉D := by
        intro xm
        have xp : x=p 0 := (single q.val qo 0 qa x xm).mp (info.1 _ xS)
        simp only [g,if_pos xm] at xg
        exact i0 (pi (xg.symm.trans xp))
      simp only [g,if_neg xo] at xg
      exact ⟨x,xS,xo,xg ▸ (pick x xo).2.2⟩
    choose v vS vo va using repr
    let fn (i : Fin 4) := if h : i=0 then q.val else v i h
    have z : fn 0=q.val := dif_pos rfl
    have s (i : Fin 4) (i0 : i≠0) : fn i=v i i0 := dif_neg i0
    have out (i : Fin 4) : fn i∉D := by
      by_cases e : i=0
      · subst i
        simpa only [z] using qo
      · rw [s i e]
        exact vo i e
    have ea (i : Fin 4) : G.Adj (fn i) (p i) := by
      by_cases e : i=0
      · subst i
        simpa only [z] using qa
      · rw [s i e]
        exact va i e
    refine ⟨fn,z,out,fun i=>single _ (out i) i (ea i),?_⟩
    intro i j ij
    have j0 : j≠0 := by
      intro e
      subst j
      exact (not_lt_of_ge (Fin.zero_le i)) ij
    by_cases i0 : i=0
    · subst i
      rw [z,s j j0]
      exact ⟨fun _=>rfl,fun _=>info.1 _ (vS j j0)⟩
    · rw [s i i0,s j j0]
      exact ⟨fun e=>(info.2 _ (vS i i0) _ (vS j j0) e).elim,fun e=>(i0 e).elim⟩
  choose f fc fo fp fs using finfo
  let f' (q : V) (i : Fin 4) := if h : q∈A then f ⟨q,h⟩ i else q
  have H : PortFanFamily G (D : Set V) p A f' := by
    refine ⟨pm,pi,?_,?_,?_,?_⟩
    · intro q qm i
      simpa only [f',dif_pos qm] using fo ⟨q,qm⟩ i
    · intro q qm
      simpa only [f',dif_pos qm] using fc ⟨q,qm⟩
    · intro q qm i x xm
      simpa only [f',dif_pos qm] using fp ⟨q,qm⟩ i x xm
    · intro q qm i j ij
      simpa only [f',dif_pos qm] using fs ⟨q,qm⟩ i j ij
  exact six_same_port_fans_or_induced_P9 h4 H t td (fun i=>(relay i).ne) (relay 2).symm (relay 3) far noP9

#print axioms common_relay_forces_singleton_attachment
#print axioms high_clients_at_one_relay_port_at_most_six
theorem common_relay_ambient_mean_four_of_core_slack
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (t : V) (td : t∈D) (relay : ∀ i,G.Adj t (p i))
    (independent : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (noP9 : NoPath G 9)
    (slack : (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+24≤4*D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  let A := Q.filter (fun q=>3<localIndependence G q)
  let B (i : Fin 4) := Q.filter (fun q=>G.Adj q (p i) ∧ 3<localIndependence G q)
  have caps (i : Fin 4) : (B i).card≤6 := by
    let e := Equiv.swap 0 i
    let p' (j : Fin 4) := p (e j)
    have e0 : p' 0=p i := by simp [p',e]
    have newattach (q : V) (qo : q∉D) : ∃ j,G.Adj q (p' j) := by
      obtain ⟨k,ok⟩ := attach q qo
      exact ⟨e.symm k,by simpa [p'] using ok⟩
    have newpal (q : V) (qo : q∉D) (w : V) (wd : w∈D) (qw : G.Adj q w) : ∃ j,w=p' j := by
      obtain ⟨k,eq⟩ := palette q qo w wd qw
      exact ⟨e.symm k,by simpa [p'] using eq⟩
    have exact := high_clients_at_one_relay_port_at_most_six h4 D p' (fun j=>pm (e j))
      (pi.comp e.injective) t td (fun j=>relay (e j)) (independent _ _) newattach newpal noP9
    simpa only [B,Q,e0] using exact
  have qa (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have allA : A⊆Finset.univ.biUnion B := by
    intro q qm
    obtain ⟨qQ,hq⟩ := Finset.mem_filter.mp qm
    obtain ⟨i,qi⟩ := attach q (qa q qQ)
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨qQ,qi,hq⟩⟩
  have a24 : A.card≤24 := by
    calc
      _≤(Finset.univ.biUnion B).card := Finset.card_le_card allA
      _≤ ∑ i:Fin 4,(B i).card := Finset.card_biUnion_le
      _≤∑ _i:Fin 4,6 := Finset.sum_le_sum (fun i _=>caps i)
      _=24 := by decide
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
  have outer : (∑ q∈Q,localIndependence G q)≤3*Q.card+24 := by
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
    exact ss.trans (Nat.add_le_add_left a24 _)
  have crossings : (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card := by
    calc
      _=∑ _q∈Q,1 := by
        apply Finset.sum_congr rfl
        intro q qm
        have att := htag q (qa q qm)
        have once := common_relay_forces_singleton_attachment h4 D p t td relay palette q (qa q qm) _ att
        have eq : D.filter (G.Adj q)={p (tag q (qa q qm))} := by
          ext w
          constructor
          · intro wm
            obtain ⟨wd,e⟩ := Finset.mem_filter.mp wm
            exact Finset.mem_singleton.mpr ((once w wd).mp e)
          · intro wm
            obtain rfl := Finset.mem_singleton.mp wm
            exact Finset.mem_filter.mpr ⟨pm _,att⟩
        rw [eq,Finset.card_singleton]
      _=_ := by simp
  have bound := core_and_exterior_independence_sum (G:=G) D
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change _≤_ + (∑ q∈Q,localIndependence G q) + (∑ q∈Q,(D.filter (G.Adj q)).card) at bound
  omega

#print axioms common_relay_ambient_mean_four_of_core_slack
end Graffiti133P5CliqueArms
