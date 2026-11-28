import SixTripleCutForeignHigh189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At threshold six, if every vertex outside a three-cut is high,
deleting the cut leaves at most two components. The cut itself may
contain the exceptional vertex or induce any of its four edge types. -/
theorem three_cut_at_most_two_of_high_outside
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S : Finset V} (ss : S.card=3) (high : ∀ v∉S,6≤G.degree v) :
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
  have big (i : Fin 3) : 4≤(A i).card := by
    obtain ⟨x,xm⟩ := (sh i).nonempty
    have h := high x (fun t=>disjoint_left.mp (sh i).disjoint xm t)
    have d := (sh i).degree_bound xm
    rw [ss] at d
    omega
  have highIn (i : Fin 3) : ∀x∈A i,6≤G.degree x :=
    fun x xm=>high x (fun t=>disjoint_left.mp (sh i).disjoint xm t)
  obtain ⟨i,x,xm,un⟩ := universal_port_of_three_shores hc cap conn degree ss A sh ac dis
  obtain ⟨j,k,ij,ik,jk⟩ :=
    (show ∀ i : Fin 3,∃ j k : Fin 3,i≠j ∧ i≠k ∧ j≠k by decide) i
  exact no_three_shores_with_high_foreign_of_universal hc cap conn ss
    (sh j) (sh k) (sh i) (ac j) (ac k) (ac i) (dis jk) (dis ij.symm) (dis ik.symm)
    (big j) (big k) (big i) (highIn j) (highIn k) (highIn i) xm un

#print axioms three_cut_at_most_two_of_high_outside
end Graffiti189LongestPath.ThresholdSix.ThreeCut
