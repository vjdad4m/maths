import SixTripleCutUniversalPort189
import SixTripleCutSingletonIsolate189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.bad_terminal_low_only from SixTripleCutUniversalPort189

/-- Every independent 3-vertex separator at degree threshold six
splits at most two components. The absence of high ports forces a
common singleton, whose saturated even-distance sphere is then
incompatible with the three pairwise nonadjacent terminals. -/
theorem independent_three_cut_at_most_two_components
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S : Finset V} (ss : S.card=3)
    (independent : ∀ t∈S,∀ a∈S,a≠t → ¬G.Adj t a) :
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
  let f : Fin 3 ↪ C := (Fin.castLEEmb c).trans (Fintype.equivFin C).symm.toEmbedding
  let A (i : Fin 3) := shoreSet (f i)
  have sh (i : Fin 3) : Shore G S (A i) := shoreSet_shore (f i)
  have ac (i : Fin 3) : (G.induce (↑(A i) : Set V)).Connected := shoreSet_connected (f i)
  have dis : Pairwise fun i j=>Disjoint (A i) (A j) :=
    fun _ _ ne=>shoreSet_disjoint (f.injective.ne ne)
  have lost (t : V) (tm : t∈S) :
      ∃ i,∃ s∈A i,G.Adj t s ∧ G.degree s<6 ∧ ∀ x∈A i,G.Adj t x → G.degree x<6 := by
    apply Graffiti189LongestPath.ThresholdSix.ThreeCut.bad_terminal_low_only conn ss A sh tm
    exact not_three_high_port_shores_at_isolated_terminal hc cap degree ss A sh ac dis tm (independent t tm)
  obtain ⟨t,tm⟩ := card_pos.mp (show 0<S.card by omega)
  obtain ⟨i,s,sm,_,low,_⟩ := lost t tm
  have same {x : V} (xlow : G.degree x<6) : x=s := by
    by_contra ne
    rcases degree x s ne with h|h <;> omega
  have only (u : V) (um : u∈S) (x : V) (xi : x∈A i) (ux : G.Adj u x) : x=s := by
    obtain ⟨j,w,wj,_,wl,bad⟩ := lost u um
    have ws := same wl
    subst w
    have ij : i=j := by
      by_contra ne
      exact disjoint_left.mp (dis ne) sm wj
    subst j
    exact same (bad x xi ux)
  have vis : (visible G S (A i)).card≤1 := by
    have sub : visible G S (A i)⊆({s}:Finset V) := by
      intro x xm
      obtain ⟨xi,u,um,xu⟩ := mem_filter.mp xm
      exact mem_singleton.mpr (only u um x xi xu.symm)
    exact (card_le_card sub).trans (by simp)
  have small : (A i).card<3 := by
    by_contra! large
    have v := (sh i).visible_lower ss conn large
    omega
  have singleton : A i={s} := by
    ext x
    constructor
    · intro xm
      have d := (sh i).degree_bound xm
      rw [ss] at d
      exact mem_singleton.mpr (same (by omega))
    · intro xm
      exact (mem_singleton.mp xm).symm ▸ sm
  obtain ⟨j,k,ij,ik,jk⟩ :=
    (show ∀ i : Fin 3,∃ j k : Fin 3,i≠j ∧ i≠k ∧ j≠k by decide) i
  exact no_independent_three_cut_singleton hc cap conn degree ss (singleton ▸ sh i) (sh j) (sh k)
    (singleton ▸ dis ij) (singleton ▸ dis ik) (dis jk) independent

#print axioms independent_three_cut_at_most_two_components
end Graffiti189LongestPath.ThresholdSix.ThreeCut
