import ThreeTerminalGeometry
import ContactRepair
import DominoF1

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open FourRingCutAux HandleExtension PathSlides DominoGadget FourRingCyclicEquivalence
noncomputable section
universe u

/-- If the cyclic-four conjecture holds, every order-divisible-by-six
cubic graph with exactly three minimal nontrivial three-cut shores has a
P3 packing missing at most six vertices. This is not a factor claim. -/
theorem cyclic4_factor_implies_six_vacancies_at_three_shores
    (promise : CyclicUniversal.{u})
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀v,G.degree v=3) (min : MinBoundaryThree G) (dvd : 6∣Fintype.card V)
    {A B C : Finset V} (ma : MinimalShore G A) (mb : MinimalShore G B) (mc : MinimalShore G C)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (every : ∀s,MinimalShore G s→s=A ∨ s=B ∨ s=C)
    {a a' b b' d d' : V} (aa : G.Adj a a') (bb : G.Adj b b') (dd : G.Adj d d')
    (aA : a∈A) (a'A : a'∈A) (bB : b∈B) (b'B : b'∈B) (dC : d∈C) (d'C : d'∈C) :
    ∃ P : Parts V, PackIn G univ P ∧ ((univ:Finset V)\P.biUnion id).card≤6 := by
  classical
  obtain ⟨E,F,small⟩ := two_handles_for_three_minimal cub min ma mb mc ab ac bc every
    aa bb dd aA a'A bB b'B dC d'C
  let W := (V⊕Bool)⊕Bool
  let x : W := Sum.inr true
  have cw : Fintype.card W=Fintype.card V+4 := by
    change Fintype.card ((V⊕Bool)⊕Bool)=_
    simp [Fintype.card_sum]
  have modV : Fintype.card V%6=0 := Nat.mod_eq_zero_of_dvd dvd
  have res : Fintype.card W%6=4 := by omega
  have cubE := E.cubic cub
  have fac := cyclic4_factor_implies_f1 promise (F.cubic cubE)
    (three_connected_of_small_trivial F.host (F.cubic cubE) F.host_order_ge_four small) small res x
  let embed : V↪Rest x :=
    ⟨fun v=>⟨Sum.inl (Sum.inl v),by simp [x]⟩,
      fun _ _ eq=>Sum.inl.inj (Sum.inl.inj (congrArg Subtype.val eq))⟩
  have refl (v w : V) (h : (oldGraph F.host x).Adj (embed v) (embed w)) :
      G.Adj v w := h.1.1
  have cRest : Fintype.card (Rest x)=Fintype.card V+3 := by
    have sizeX : Fintype.card {z : W // z=x}=1 := Fintype.card_unique
    have eq := Fintype.card_subtype_compl (fun z : W=>z=x)
    change Fintype.card (Rest x)=Fintype.card W-Fintype.card {z : W // z=x} at eq
    rw [eq,cw,sizeX]
    omega
  obtain ⟨P,ok,bound⟩ := packing_restrict_factor embed refl fac
  refine ⟨P,ok,?_⟩
  rw [cRest] at bound
  omega

/-- If the cyclic-four conjecture holds, every order-divisible-by-six
cubic graph with exactly three minimal nontrivial three-cut shores has a
P3 packing missing at most three vertices. This is not a factor claim. -/
theorem cyclic4_factor_implies_three_vacancies_at_three_shores
    (promise : CyclicUniversal.{u})
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀v,G.degree v=3) (min : MinBoundaryThree G) (dvd : 6∣Fintype.card V)
    {A B C : Finset V} (ma : MinimalShore G A) (mb : MinimalShore G B) (mc : MinimalShore G C)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (every : ∀s,MinimalShore G s→s=A ∨ s=B ∨ s=C)
    {a a' b b' d d' : V} (aa : G.Adj a a') (bb : G.Adj b b') (dd : G.Adj d d')
    (aA : a∈A) (a'A : a'∈A) (bB : b∈B) (b'B : b'∈B) (dC : d∈C) (d'C : d'∈C) :
    ∃ P : Parts V, PackIn G univ P ∧ ((univ:Finset V)\P.biUnion id).card≤3 := by
  classical
  obtain ⟨E,F,small,Ea,Eb,_,_,Fa,Fb,_,_⟩ := explicit_two_handles_for_three_minimal cub min ma mb mc ab ac bc every
    aa bb dd aA a'A bB b'B dC d'C
  let W := (V⊕Bool)⊕Bool
  let x : W := Sum.inr true
  have cw : Fintype.card W=Fintype.card V+4 := by
    change Fintype.card ((V⊕Bool)⊕Bool)=_
    simp [Fintype.card_sum]
  have modV : Fintype.card V%6=0 := Nat.mod_eq_zero_of_dvd dvd
  have res : Fintype.card W%6=4 := by omega
  have cubE := E.cubic cub
  have fac := cyclic4_factor_implies_f1 promise (F.cubic cubE)
    (three_connected_of_small_trivial F.host (F.cubic cubE) F.host_order_ge_four small) small res x
  let embed : V↪Rest x :=
    ⟨fun v=>⟨Sum.inl (Sum.inl v),by simp [x]⟩,
      fun _ _ eq=>Sum.inl.inj (Sum.inl.inj (congrArg Subtype.val eq))⟩
  have refl (v w : V) (h : (oldGraph F.host x).Adj (embed v) (embed w)) :
      G.Adj v w := h.1.1
  have cRest : Fintype.card (Rest x)=Fintype.card V+3 := by
    have sizeX : Fintype.card {z : W // z=x}=1 := Fintype.card_unique
    have eq := Fintype.card_subtype_compl (fun z : W=>z=x)
    change Fintype.card (Rest x)=Fintype.card W-Fintype.card {z : W // z=x} at eq
    rw [eq,cw,sizeX]
    omega

  let p : Rest x := ⟨Sum.inr false,by intro e; exact Bool.false_ne_true (Sum.inr.inj e)⟩
  let q : Rest x := ⟨Sum.inl (Sum.inr false),by simp [x]⟩
  have np : ¬∃ v,embed v=p := by
    rintro ⟨v,ev⟩
    have same : (Sum.inl (Sum.inl v) : W)=Sum.inr false := congrArg Subtype.val ev
    cases same
  have nq : ¬∃ v,embed v=q := by
    rintro ⟨v,ev⟩
    have same : (Sum.inl (Sum.inl v) : W)=Sum.inl (Sum.inr false) := congrArg Subtype.val ev
    cases (Sum.inl.inj same)
  have pq : p≠q := by
    intro same
    have opp : (Sum.inr false : W)=Sum.inl (Sum.inr false) := congrArg Subtype.val same
    cases opp
  have onlyP (v : V) (h : (oldGraph F.host x).Adj p (embed v)) : v=a := by
    change Sum.inl v=F.a false ∨ Sum.inl v=F.b false at h
    rw [Fa,Fb] at h
    rcases h with l|r
    · exact Sum.inl.inj l
    · cases r
  have onlyQ (v : V) (h : (oldGraph F.host x).Adj q (embed v)) : v=a' := by
    change E.Ends false v ∧ ¬F.Removed (Sum.inr false) (Sum.inl v) at h
    obtain ⟨contact,cannot⟩ := h
    change v=E.a false ∨ v=E.b false at contact
    rw [Ea,Eb] at contact
    rcases contact with rfl|e
    · exact (cannot ⟨false,Or.inr ⟨Fb.symm,Fa.symm⟩⟩).elim
    · exact e
  exact three_aux_single_contact_repair embed refl cRest np nq pq aa onlyP onlyQ fac

#print axioms cyclic4_factor_implies_six_vacancies_at_three_shores
#print axioms cyclic4_factor_implies_three_vacancies_at_three_shores
end
end KelmansCactus.AtomicBridge.OddUncross
