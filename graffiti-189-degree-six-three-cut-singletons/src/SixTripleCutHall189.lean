import SixTripleCutUniversalBudget189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.no_invariant_shore from SixTripleCutBasics189

/-- On a nonsingleton shore, two distinct terminals of a three-cut
cannot have a common sole port. Their union of port sets has size at
least two in a 3-connected graph. -/
theorem Shore.hall_two_terminals {S A : Finset V} (sh : Shore G S A)
    (ss : S.card=3) (conn : ThreeConnected G) (aa : 2≤A.card)
    {t u : V} (ts : t∈S) (us : u∈S) (tu : t≠u) :
    2≤(ports G A t∪ports G A u).card := by
  classical
  by_contra! bad
  obtain ⟨w,wa,tw⟩ := sh.hit ss conn ts
  have wp : w∈ports G A t∪ports G A u :=
    mem_union_left _ (mem_filter.mpr ⟨wa,tw⟩)
  have eq : ports G A t∪ports G A u={w} :=
    (eq_of_subset_of_card_le (singleton_subset_iff.mpr wp) (by have h:=bad; simp; omega)).symm
  let D := S\({t,u}:Finset V)
  let R := insert w D
  have di : ({t,u}:Finset V)⊆S := insert_subset ts (singleton_subset_iff.mpr us)
  have dc : D.card=1 := by dsimp [D]; rw [card_sdiff di,ss,card_pair tu]
  have wr : w∉D := fun h=>disjoint_left.mp sh.disjoint wa (mem_sdiff.mp h).1
  have rc : R.card<3 := by dsimp [R]; rw [card_insert_of_not_mem wr,dc]; decide
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<(A.erase w).card by rw [card_erase_of_mem wa]; omega)
  have ta : t∉A.erase w := fun h=>disjoint_left.mp sh.disjoint (mem_erase.mp h).2 ts
  have xr : x∉R := by
    intro h
    rcases mem_insert.mp h with nw|nd
    · exact (mem_erase.mp xm).1 nw
    · exact disjoint_left.mp sh.disjoint (mem_erase.mp xm).2 (mem_sdiff.mp nd).1
  have tr : t∉R := by
    intro h
    rcases mem_insert.mp h with e|hd
    · exact tw.ne e
    · exact (mem_sdiff.mp hd).2 (mem_insert_self _ _)
  apply Graffiti189LongestPath.ThresholdSix.ThreeCut.no_invariant_shore (conn R rc) xm ta xr tr
  intro z zm y zy yr
  obtain ⟨zw,za⟩ := mem_erase.mp zm
  rcases sh.closed z za y zy with ya|ys
  · exact mem_erase.mpr ⟨fun e=>yr (mem_insert.mpr (Or.inl e)),ya⟩
  · exfalso
    have p : y∈({t,u}:Finset V) := by
      by_cases m : y∈({t,u}:Finset V)
      · exact m
      exfalso
      exact yr (mem_insert_of_mem (mem_sdiff.mpr ⟨ys,m⟩))
    simp only [mem_insert,mem_singleton] at p
    rcases p with h|h
    · have zP : z∈ports G A t∪ports G A u := mem_union_left _ (mem_filter.mpr ⟨za,h ▸ zy.symm⟩)
      exact zw (mem_singleton.mp (eq ▸ zP))
    · have zP : z∈ports G A t∪ports G A u := mem_union_right _ (mem_filter.mpr ⟨za,h ▸ zy.symm⟩)
      exact zw (mem_singleton.mp (eq ▸ zP))

#print axioms Shore.hall_two_terminals
end Graffiti189LongestPath.ThresholdSix.ThreeCut
