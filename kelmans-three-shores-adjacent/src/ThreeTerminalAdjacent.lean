import ThreeTerminalDomain
import AdjacentVacancyRepair

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open FourRingCutAux HandleExtension PathSlides DominoGadget FourRingCyclicEquivalence
noncomputable section
universe u

/-- If the cyclic-four conjecture holds, every order-divisible-by-six
cubic graph with exactly three minimal nontrivial three-cut shores has a
P3 packing missing at most three vertices with two adjacent vacancies,
unless it already admits a factor. -/
theorem cyclic4_factor_implies_adjacent_vacancies_at_three_shores
    (promise : CyclicUniversal.{u})
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀v,G.degree v=3) (min : MinBoundaryThree G) (dvd : 6∣Fintype.card V)
    {A B C : Finset V} (ma : MinimalShore G A) (mb : MinimalShore G B) (mc : MinimalShore G C)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (every : ∀s,MinimalShore G s→s=A ∨ s=B ∨ s=C)
    {a a' b b' d d' : V} (aa : G.Adj a a') (bb : G.Adj b b') (dd : G.Adj d d')
    (aA : a∈A) (a'A : a'∈A) (bB : b∈B) (b'B : b'∈B) (dC : d∈C) (d'C : d'∈C) :
    KelmansStarter.HasP3Factor G ∨
      ∃ P : Parts V, PackIn G univ P ∧ ((univ:Finset V)\P.biUnion id).card≤3 ∧
        ∃ i j,G.Adj i j ∧ i∉P.biUnion id ∧ j∉P.biUnion id := by
  classical
  obtain ⟨E,F,small,Ea,Eb,Ec,Ed,Fa,Fb,_,_⟩ := explicit_two_handles_for_three_minimal cub min ma mb mc ab ac bc every
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
  let r : Rest x := ⟨Sum.inl (Sum.inr true),by simp [x]⟩
  have nr : ¬∃ v,embed v=r := by
    rintro ⟨v,ev⟩
    have same : (Sum.inl (Sum.inl v) : W)=Sum.inl (Sum.inr true) := congrArg Subtype.val ev
    cases (Sum.inl.inj same)
  have pr : p≠r := by
    intro same
    have opp : (Sum.inr false : W)=Sum.inl (Sum.inr true) := congrArg Subtype.val same
    cases opp
  have qr : q≠r := by
    intro same
    have opp : (Sum.inl (Sum.inr false) : W)=Sum.inl (Sum.inr true) := congrArg Subtype.val same
    exact Bool.false_ne_true (Sum.inr.inj (Sum.inl.inj opp))
  have rContact (v : V) (h : (oldGraph F.host x).Adj r (embed v)) : v=b ∨ v=b' := by
    have hE := h.1
    change v=E.a true ∨ v=E.b true at hE
    rwa [Ec,Ed] at hE
  have linked (u v : V) (ne : u≠v) (hu : (oldGraph F.host x).Adj r (embed u))
      (hv : (oldGraph F.host x).Adj r (embed v)) : G.Adj u v := by
    rcases rContact u hu with rfl|rfl <;> rcases rContact v hv with rfl|rfl
    · exact (ne rfl).elim
    · exact bb
    · exact bb.symm
    · exact (ne rfl).elim
  exact three_aux_repair_with_adjacent_vacancies embed refl cRest np nq nr pq pr qr aa onlyP onlyQ linked fac

private theorem terminal_has_edge
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀v,G.degree v=3) {s : Finset V} (hs : ShoreThree G s) :
    ∃ a b,a∈s∧b∈s∧G.Adj a b := by
  classical
  let c := colourOf s
  have acy : ¬(shoreGraph G c).IsAcyclic := by
    intro ac
    apply hs.2
    left
    intro x y hx hy
    refine Classical.byContradiction ?_
    intro ne
    have large := acyclic_shore_large_cut G c cub ac hx hy ne
    have small := hs.1
    change (boundary G c).card=3 at small
    omega
  refine Classical.byContradiction ?_
  intro none
  have h : shoreGraph G c=⊥ := by
    ext a b
    constructor
    · intro e
      exact (none ⟨a.val,b.val,colour_true.mp a.property,colour_true.mp b.property,e⟩).elim
    · exact False.elim
  exact acy (h.symm ▸ isAcyclic_bot)

/-- Plain cyclically four-edge-connected Kelmans implies a factor or exactly three vacancies with an adjacent pair for cubic, three-vertex-connected simple graphs of order
divisible by six with exactly three minimal nontrivial three-cut shores.
Terminal shores are counted as oriented vertex sets: both sides of each
nontrivial three-cut are considered before taking inclusion-minimal sides. -/
theorem cyclic4_factor_implies_adjacent_vacancies_in_exact_three_terminal_domain
    (promise : CyclicUniversal.{u})
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀v,G.degree v=3) (connected : KelmansStarter.ThreeConnected G)
    (dvd : 6∣Fintype.card V)
    (three : ∃ A B C : Finset V, MinimalShore G A ∧ MinimalShore G B ∧
      MinimalShore G C ∧ A≠B ∧ A≠C ∧ B≠C ∧
      ∀ S,MinimalShore G S→S=A ∨ S=B ∨ S=C) :
    KelmansStarter.HasP3Factor G ∨
      ∃ P : Parts V,PackIn G univ P ∧ ((univ:Finset V)\P.biUnion id).card=3 ∧
        ∃ i j,G.Adj i j ∧ i∉P.biUnion id ∧ j∉P.biUnion id := by
  obtain ⟨A,B,C,ma,mb,mc,ab,ac,bc,every⟩ := three
  have min := min_boundary_three_of_three_connected G cub connected
  obtain ⟨a,a',aA,a'A,ea⟩ := terminal_has_edge cub ma.1
  obtain ⟨b,b',bB,b'B,eb⟩ := terminal_has_edge cub mb.1
  obtain ⟨d,d',dC,d'C,ed⟩ := terminal_has_edge cub mc.1
  have output := cyclic4_factor_implies_adjacent_vacancies_at_three_shores promise cub min dvd ma mb mc
    (minimals_disjoint G min ma mb ab) (minimals_disjoint G min ma mc ac)
    (minimals_disjoint G min mb mc bc) every ea eb ed aA a'A bB b'B dC d'C

  rcases output with yes|⟨P,ok,bound,a,b,e,noA,noB⟩
  · exact Or.inl yes
  · right
    have pos : 0<((univ : Finset V)\P.biUnion id).card := card_pos.mpr
      ⟨a,mem_sdiff.mpr ⟨mem_univ _,noA⟩⟩
    have covered : (P.biUnion id).card=3*P.card := by
      rw [card_biUnion (show (↑P : Set (Finset V)).PairwiseDisjoint id from
        fun t ht r hr ne=>ok.part.disj t ht r hr ne)]
      have sz : ∀ t∈P,(id t).card=3 := fun t ht=>(ok.part.tile t ht).1
      rw [sum_congr rfl sz]
      simp [Nat.mul_comm]
    have sum := card_sdiff_add_card_eq_card (show P.biUnion id⊆(univ : Finset V) from subset_univ _)
    rw [covered,card_univ] at sum
    obtain ⟨k,ke⟩ := dvd
    exact ⟨P,ok,by omega,a,b,e,noA,noB⟩

#print axioms cyclic4_factor_implies_adjacent_vacancies_at_three_shores
#print axioms cyclic4_factor_implies_adjacent_vacancies_in_exact_three_terminal_domain
end
end KelmansCactus.AtomicBridge.OddUncross
