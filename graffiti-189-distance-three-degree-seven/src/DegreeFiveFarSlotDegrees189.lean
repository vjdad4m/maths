import DegreeFiveFarSideSlots189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private left_boundary from AdjacentCut189
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem bounds_of_local_color_port (far : 3≤G.dist a b) {p : V} (pp : p∈S.localA)
    (noB : ∀ q∈S.L.filter (G.Adj b),¬G.Adj p q) :
    G.neighborFinset p⊆insert a ((S.localA.erase p)∪farNonports S.L a b G) := by
  obtain ⟨pl,ap⟩ := mem_filter.mp pp
  intro q qn
  have pq := (mem_neighborFinset G p q).mp qn
  rcases left_boundary S p pl q pq with e|e|ql
  · exact mem_insert.mpr (.inl e)
  · exact (not_common far ap (e ▸ pq.symm)).elim
  apply mem_insert_of_mem
  by_cases aq : G.Adj a q
  · exact mem_union_left _ (mem_erase.mpr ⟨pq.ne.symm,mem_filter.mpr ⟨ql,aq⟩⟩)
  have bq : ¬G.Adj b q := fun h=>noB q (mem_filter.mpr ⟨ql,h⟩) pq
  exact mem_union_right _ (mem_filter.mpr ⟨ql,aq,bq⟩)

theorem distance_two_charge_from_no_bridge {p q : V} (pA : p∈S.localA)
    (qB : q∈S.L.filter (G.Adj b)) (noBridge : ¬portBridge S) :
    ¬G.Adj p q := by
  obtain ⟨pl,ap⟩ := mem_filter.mp pA
  obtain ⟨ql,bq⟩ := mem_filter.mp qB
  exact fun pq=>noBridge ⟨p,pl,q,ql,ap,pq,bq⟩

/-- If the candidates in a shore consist of a vertex's nominal color and the
nonport pool, this gives the degree lower bound on its real nonport contacts. -/
theorem far_port_nonport_degree_lower {P I : Finset V} {q d : V} (qp : q∈P)
    (bound : G.neighborFinset q⊆insert d ((P.erase q)∪I)) :
    G.degree q≤P.card+(I.filter (G.Adj q)).card := by
  classical
  have sub : G.neighborFinset q⊆insert d ((P.erase q)∪I.filter (G.Adj q)) := by
    intro x xn
    have e := (mem_neighborFinset G q x).mp xn
    rcases mem_insert.mp (bound xn) with xd|h
    · exact mem_insert.mpr (.inl xd)
    exact mem_insert_of_mem ((mem_union.mp h).elim (mem_union_left _) (fun xi=>
      mem_union_right _ (mem_filter.mpr ⟨xi,e⟩)))
  have n := (card_le_card sub).trans (card_insert_le d _)
  have c := card_union_le (P.erase q) (I.filter (G.Adj q))
  have pos := card_pos.mpr ⟨q,qp⟩
  rw [card_neighborFinset_eq_degree] at n
  rw [card_erase_of_mem qp] at c
  omega

theorem far_port_nonport_degree_lower_of_missing_peer {P I : Finset V} {q d p : V}
    (qp : q∈P) (pp : p∈P) (pq : p≠q) (no : ¬G.Adj q p)
    (bound : G.neighborFinset q⊆insert d ((P.erase q)∪I)) :
    G.degree q+1≤P.card+(I.filter (G.Adj q)).card := by
  classical
  have sub : G.neighborFinset q⊆insert d (((P.erase q).erase p)∪I.filter (G.Adj q)) := by
    intro x xn
    have e := (mem_neighborFinset G q x).mp xn
    rcases mem_insert.mp (bound xn) with xd|h
    · exact mem_insert.mpr (.inl xd)
    apply mem_insert_of_mem
    rcases mem_union.mp h with p'|i'
    · exact mem_union_left _ (mem_erase.mpr ⟨fun k=>no (k ▸ e),p'⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨i',e⟩)
  have n := (card_le_card sub).trans (card_insert_le d _)
  have c := card_union_le ((P.erase q).erase p) (I.filter (G.Adj q))
  have p' : p∈P.erase q := mem_erase.mpr ⟨pq,pp⟩
  have pos := card_pos.mpr ⟨p,p'⟩
  rw [card_neighborFinset_eq_degree] at n
  rw [card_erase_of_mem p',card_erase_of_mem qp] at c
  rw [card_erase_of_mem qp] at pos
  omega

theorem far_port_full_at_tight_pool {P I : Finset V} {q d : V} (qp : q∈P)
    (bound : G.neighborFinset q⊆insert d ((P.erase q)∪I))
    (exact5 : P.card+I.card=5) (hi : 5≤G.degree q) :
    (∀ p∈P,q≠p → G.Adj q p) ∧ ∀ i∈I,G.Adj q i := by
  classical
  have cap : (insert d ((P.erase q)∪I)).card≤5 := by
    have n := card_insert_le d ((P.erase q)∪I)
    have c := card_union_le (P.erase q) I
    have pos := card_pos.mpr ⟨q,qp⟩
    rw [card_erase_of_mem qp] at c
    omega
  have eq : G.neighborFinset q=insert d ((P.erase q)∪I) :=
    eq_of_subset_of_card_le bound (by rw [card_neighborFinset_eq_degree]; omega)
  constructor
  · intro p pp ne
    exact (mem_neighborFinset G q p).mp (eq.symm ▸
      mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨ne.symm,pp⟩)))
  intro i ii
  exact (mem_neighborFinset G q i).mp (eq.symm ▸ mem_insert_of_mem (mem_union_right _ ii))

#print axioms bounds_of_local_color_port
#print axioms far_port_nonport_degree_lower_of_missing_peer
#print axioms far_port_full_at_tight_pool
end Graffiti189LongestPath.CrossSaturation.Split.Five
