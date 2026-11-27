import ThreeTerminalVacancies

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open FourRingCutAux FourRingCyclicEquivalence PathSlides
noncomputable section
universe u

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

/-- Plain cyclically four-edge-connected Kelmans implies at most three
vacancies for cubic, three-vertex-connected simple graphs of order
divisible by six with exactly three minimal nontrivial three-cut shores.
Terminal shores are counted as oriented vertex sets: both sides of each
nontrivial three-cut are considered before taking inclusion-minimal sides. -/
theorem cyclic4_factor_implies_three_vacancies_in_exact_three_terminal_domain
    (promise : CyclicUniversal.{u})
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀v,G.degree v=3) (connected : KelmansStarter.ThreeConnected G)
    (dvd : 6∣Fintype.card V)
    (three : ∃ A B C : Finset V, MinimalShore G A ∧ MinimalShore G B ∧
      MinimalShore G C ∧ A≠B ∧ A≠C ∧ B≠C ∧
      ∀ S,MinimalShore G S→S=A ∨ S=B ∨ S=C) :
    ∃ P : Parts V,PackIn G univ P ∧ ((univ:Finset V)\P.biUnion id).card≤3 := by
  obtain ⟨A,B,C,ma,mb,mc,ab,ac,bc,every⟩ := three
  have min := min_boundary_three_of_three_connected G cub connected
  obtain ⟨a,a',aA,a'A,ea⟩ := terminal_has_edge cub ma.1
  obtain ⟨b,b',bB,b'B,eb⟩ := terminal_has_edge cub mb.1
  obtain ⟨d,d',dC,d'C,ed⟩ := terminal_has_edge cub mc.1
  exact cyclic4_factor_implies_three_vacancies_at_three_shores promise cub min dvd ma mb mc
    (minimals_disjoint G min ma mb ab) (minimals_disjoint G min ma mc ac)
    (minimals_disjoint G min mb mc bc) every ea eb ed aA a'A bB b'B dC d'C

#print axioms cyclic4_factor_implies_three_vacancies_in_exact_three_terminal_domain
end
end KelmansCactus.AtomicBridge.OddUncross
