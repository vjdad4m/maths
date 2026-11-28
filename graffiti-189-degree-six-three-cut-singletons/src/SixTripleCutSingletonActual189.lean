import SixTripleCutSingletonComplete189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An actual three-cut that isolates a vertex leaves at most two
components, without any hypothesis on the edges inside the cut. -/
theorem three_cut_at_most_two_with_singleton
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S : Finset V} (ss : S.card=3) {X : (Removed G S).ConnectedComponent}
    (one : (shoreSet X).card=1) :
    Nat.card (Removed G S).ConnectedComponent≤2 := by
  classical
  by_contra! big
  let C := (Removed G S).ConnectedComponent
  letI : Finite C := Finite.of_surjective (Removed G S).connectedComponentMk (fun y=>y.exists_rep)
  letI : Fintype C := Fintype.ofFinite C
  have c : 3≤Fintype.card C := by
    change 2<Nat.card C at big
    rw [Nat.card_eq_fintype_card] at big
    omega
  have rest : 1<((univ:Finset C).erase X).card := by
    rw [card_erase_of_mem (mem_univ X),card_univ]
    change 1 < Fintype.card C - 1
    omega
  obtain ⟨Y,Ym,Z,Zm,yz⟩ := one_lt_card.mp rest
  have xy : X≠Y := (mem_erase.mp Ym).1.symm
  have xz : X≠Z := (mem_erase.mp Zm).1.symm
  obtain ⟨s,eq⟩ := card_eq_one.mp one
  exact no_three_shores_one_singleton hc cap conn degree ss
    (eq ▸ shoreSet_shore X) (shoreSet_shore Y) (shoreSet_shore Z)
    (eq ▸ shoreSet_disjoint xy) (eq ▸ shoreSet_disjoint xz) (shoreSet_disjoint yz)

#print axioms three_cut_at_most_two_with_singleton
end Graffiti189LongestPath.ThresholdSix.ThreeCut
