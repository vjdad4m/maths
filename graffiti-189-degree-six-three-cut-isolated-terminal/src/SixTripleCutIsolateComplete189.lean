import SixTripleCutNonSingletonIsolate189
import SixTripleCutUniversalPort189
import FiveStarCut189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.bad_terminal_low_only from SixTripleCutUniversalPort189
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At threshold six an actual three-cut containing a terminal
isolated inside that cut has at most two deletion components.
In particular this covers independent cuts and one-edge cuts. -/
theorem three_cut_at_most_two_of_isolated_terminal
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S : Finset V} (ss : S.card=3) {t : V} (ts : t∈S)
    (isolate : ∀ a∈S,a≠t → ¬G.Adj t a) :
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
  by_cases one : ∃ i,(A i).card=1
  · obtain ⟨i,h⟩ := one
    obtain ⟨s,eq⟩ := card_eq_one.mp h
    obtain ⟨j,k,ij,ik,jk⟩ :=
      (show ∀ i : Fin 3,∃ j k : Fin 3,i≠j ∧ i≠k ∧ j≠k by decide) i
    exact no_singleton_three_shores_of_isolated_terminal hc cap conn degree ss
      (eq ▸ sh i) (sh j) (sh k) (eq ▸ dis ij) (eq ▸ dis ik) (dis jk) ts isolate
  have a4 (i : Fin 3) : 4≤(A i).card := by
    have pos := card_pos.mpr (sh i).nonempty
    have no : (A i).card≠1 := fun h=>one ⟨i,h⟩
    obtain ⟨a,am,b,bm,ne⟩ := one_lt_card.mp (by omega : 1<(A i).card)
    have l := (sh i).degree_bound am
    have k := (sh i).degree_bound bm
    rw [ss] at l k
    rcases degree a b ne with h|h <;> omega
  have v3 (i : Fin 3) : 3≤(visible G S (A i)).card := (sh i).visible_lower ss conn ((by decide : 3≤4).trans (a4 i))
  have missing : ¬Good G A t :=
    not_three_high_port_shores_at_isolated_terminal hc cap degree ss A sh ac dis ts isolate
  obtain ⟨i,s,si,st,sl,sOnly⟩ := Graffiti189LongestPath.ThresholdSix.ThreeCut.bad_terminal_low_only conn ss A sh ts missing
  have unique {v : V} (vl : G.degree v<6) : v=s := by
    by_cases eq : v=s
    · exact eq
    exfalso
    rcases degree v s eq with h|h <;> omega
  have only (v : V) (vm : v∈A i) (tv : G.Adj t v) : v=s := unique (sOnly v vm tv)
  have high {j : Fin 3} (ji : j≠i) : ∀ v∈A j,6≤G.degree v := by
    intro v vm
    have ne : v≠s := fun e => disjoint_left.mp (dis ji) vm (e.symm ▸ si)
    exact (degree v s ne).resolve_right (by omega)
  obtain ⟨j,x,xj,un⟩ := universal_port_of_three_shores hc cap conn degree ss A sh ac dis
  have ji : j≠i := by
    intro eq
    subst j
    have xs := only x xj (un t ts).symm
    subst x
    obtain ⟨k,l,ik,il,kl⟩ :=
      (show ∀ i : Fin 3,∃ j k : Fin 3,i≠j ∧ i≠k ∧ j≠k by decide) i
    obtain ⟨_,_,inside⟩ := universal_port_saturates_other_shores hc cap
      (sh i) (ac i) (sh k) (sh l) (dis ik) (dis il) (dis kl) (v3 k) (v3 l) si un
    have h := full_degree_of_universal_inside (sh i) si un inside
    have n := a4 i
    omega
  obtain ⟨k,ki,kj⟩ :=
    (show ∀ (i j : Fin 3),i≠j → ∃ k : Fin 3,k≠i ∧ k≠j by decide) i j ji.symm
  have sOff : s∉S := fun h=>disjoint_left.mp (sh i).disjoint si h
  have order4 := card_le_univ (insert s S)
  rw [card_insert_of_not_mem sOff,ss] at order4
  have ms := FiveThreeHook.min_three_degree_of_small_deletion (G:=G) conn (by omega : 4≤Fintype.card V) s
  exact no_nonsingleton_three_shores_of_isolated_terminal hc cap conn ss
    (sh i) (sh k) (sh j) (ac i) (ac k) (ac j) (dis ki.symm) (dis ji.symm) (dis kj)
    (a4 i) (a4 k) (a4 j) (high ki) (high ji) ts isolate si sl ms st only xj un

#print axioms three_cut_at_most_two_of_isolated_terminal
end Graffiti189LongestPath.ThresholdSix.ThreeCut
