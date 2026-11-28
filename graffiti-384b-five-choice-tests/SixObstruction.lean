import SixObstructionData
import ChoiceFrame
import ChoiceCompetition
namespace Graffiti384b.FiveChoice.Obstruction
open Finset SimpleGraph Four29 LowSample
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-- The six contacts are the exact smallest simultaneous score carrier, even
if any of the other seventeen pool vertices may be used. -/
theorem carrier_iff (X : Finset V) : supports graph 27 28 X ↔ contacts⊆X := by
  constructor
  · intro win
    obtain ⟨a,ar,maj,forced⟩ := compulsory graph 27 28 X win
    rw [roots_eq] at ar
    have one : a=1 := by
      have tab : ∀v∈({0,1,2,3}:Finset V),13≤scores v → v=1 := by decide
      exact tab a ar (score_table _ ▸ maj)
    subst a
    have atRoot (i : V) (m : i∈({0,1,2,3}:Finset V)) : i∈roots graph 27 28 := roots_eq ▸ m
    have first := forced 0 (atRoot 0 (by decide)) (by rw [score_table]; decide)
    have second := forced 1 (atRoot 1 (by decide)) (by rw [score_table]; decide)
    rw [fixed_partners.1] at first
    rw [fixed_partners.2] at second
    have eq : contacts=({4,5}:Finset V)∪{6,7,8,9} := by decide
    rw [eq]; exact union_subset first second
  · intro inc
    have enough : ∀v∈({0,1,2,3}:Finset V),2≤score graph 27 28 contacts v := by decide
    have big : 13≤score graph 27 28 contacts 1 := by decide
    refine ⟨fun v vm => (enough v (roots_eq ▸ vm)).trans (score_mono graph 27 28 inc _),
      1,roots_eq ▸ (by decide : (1:V)∈({0,1,2,3}:Finset V)),big.trans (score_mono graph 27 28 inc 1)⟩

theorem minimum_carrier : IsLeast {n : ℕ | ∃X⊆pool graph 27 28,X.card=n ∧ supports graph 27 28 X} 6 := by
  have inc : contacts⊆pool graph 27 28 := by decide
  have six : contacts.card=6 := by decide
  refine ⟨⟨contacts,inc,six,(carrier_iff contacts).mpr Subset.rfl⟩,?_⟩
  rintro n ⟨X,_,xn,suff⟩
  exact six ▸ xn ▸ card_le_card ((carrier_iff X).mp suff)

theorem frame_eq : localVertices={0,1,2,3,4,5,6,7,8,9,27,28} := by
  rw [localVertices,roots_eq,contacts_eq]; decide

private theorem local_neighbors :
    localVertices.filter (graph.Adj 27)={0,1} ∧ localVertices.filter (graph.Adj 0)={27,1,4,5} ∧
    localVertices.filter (graph.Adj 4)={0,5} ∧ localVertices.filter (graph.Adj 5)={0,4} := by rw [frame_eq]; decide

private theorem both {v a b : V} {S : Finset V} (sub : S⊆localVertices) (two : 2≤nbr graph v S)
    (eq : localVertices.filter (graph.Adj v)={a,b}) : a∈S ∧ b∈S := by
  have inc := Finset.filter_subset_filter (graph.Adj v) sub
  rw [eq] at inc
  have bound : ({a,b}:Finset V).card≤(S.filter (graph.Adj v)).card :=
    Finset.card_le_two.trans two
  have equal := eq_of_subset_of_card_le inc bound
  exact ⟨(mem_filter.mp (equal.symm ▸ mem_insert_self a {b})).1,
    (mem_filter.mp (equal.symm ▸ mem_insert_of_mem (mem_singleton_self b))).1⟩

private theorem one_side (P Q : Finset V) (pd : P⊆localVertices) (qd : Q⊆localVertices)
    (dis : Disjoint P Q) (pq : ∀v∈P,2≤nbr graph v Q) (qp : ∀v∈Q,2≤nbr graph v P)
    (ear : 27∈P) : False := by
  obtain ⟨a,b⟩ := both qd (pq 27 ear) local_neighbors.1
  have np : (0:V)∉P := fun h => disjoint_left.mp dis h a
  have no4 (i : (4:V)∈P) : False := by
    have five := (both qd (pq 4 i) local_neighbors.2.2.1).2
    exact np (both pd (qp 5 five) local_neighbors.2.2.2).1
  have no5 (i : (5:V)∈P) : False := by
    have four := (both qd (pq 5 i) local_neighbors.2.2.2).2
    exact np (both pd (qp 4 four) local_neighbors.2.2.1).1
  have only : P.filter (graph.Adj 0)⊆{27} := by
    intro i im
    have hm := Finset.filter_subset_filter (graph.Adj 0) pd im
    rw [local_neighbors.2.1] at hm
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl
    · exact mem_singleton_self _
    · exact (disjoint_left.mp dis (mem_filter.mp im).1 b).elim
    · exact (no4 (mem_filter.mp im).1).elim
    · exact (no5 (mem_filter.mp im).1).elim
  have small := card_le_card only
  rw [card_singleton] at small
  exact (by have big := qp 0 a; change 2≤(P.filter (graph.Adj 0)).card at big; omega : False)

/-- No two disjoint pinned sets inside the ears, four anchors and six
triangle contacts can protect every pin and include even the first ear. -/
theorem no_local_cut (P Q : Finset V) (pd : P⊆localVertices) (qd : Q⊆localVertices)
    (dis : Disjoint P Q) (pq : ∀v∈P,2≤nbr graph v Q) (qp : ∀v∈Q,2≤nbr graph v P) :
    (27:V)∉P∪Q := by
  intro em
  exact (mem_union.mp em).elim (one_side P Q pd qd dis pq qp) (one_side Q P qd pd dis.symm qp pq)

theorem outside_pin : IsLeast {n : ℕ | ∃P Q:Finset V,((P∪Q)\localVertices).card=n ∧
    Disjoint P Q ∧ twos graph⊆P∪Q ∧ (∀v∈P,2≤nbr graph v Q) ∧ (∀v∈Q,2≤nbr graph v P)} 1 := by
  constructor
  · refine ⟨{0,1,10,28},{2,3,5,7,27},?_⟩
    rw [frame_eq,degrees.2.2.1]; decide
  · rintro n ⟨P,Q,size,dis,ears,lp,rq⟩
    by_contra! lt
    have zero : ((P∪Q)\localVertices).card=0 := by omega
    have sub := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp zero)
    have ear : (27:V)∈twos graph := degrees.2.2.1 ▸ mem_insert_self ..
    exact no_local_cut P Q (subset_union_left.trans sub) (subset_union_right.trans sub) dis lp rq (ears ear)

/-- A six-cycle through the first ear reaches vertex ten outside all six
contacts. Its even shore supplies the second ear's two anchors. -/
theorem nonlocal_solution : gamma graph≤bound graph := by
  apply frame_solution graph (P:={0,1,10}) (Q:={27,5,7}) (e:=27) (f:=28) (c:=2) (d:=3)
  · unfold EarFrame33.Frame; decide
  · rw [diversity,degrees.1]
  · intro v vm; rwa [degrees.2.2.1,mem_insert,mem_singleton] at vm
  all_goals decide

/-- The obstruction also satisfies the general competition criterion. -/
theorem low_charges : ∀v∈roots graph 27 28,v≠0 →
    (charged graph 27 28 0 v ({4,5}:Finset V)).card≤1 := by rw [roots_eq]; decide

theorem exact_profile : graph.Connected ∧ (types graph).card=29 ∧ (nonleaves graph).card=29 ∧
    (high graph).card=27 ∧ (triangleContacts graph 27 28).card=6 ∧
    (Donor.exposed graph (pool graph 27 28)).card=6 ∧ gamma graph≤14 := by
  refine ⟨connected,diversity,degrees.1,degrees.2.1,?_,exposures.1,feasible.1⟩
  rw [contacts_eq]; decide
end Graffiti384b.FiveChoice.Obstruction
#print axioms Graffiti384b.FiveChoice.Obstruction.carrier_iff
#print axioms Graffiti384b.FiveChoice.Obstruction.minimum_carrier
#print axioms Graffiti384b.FiveChoice.Obstruction.outside_pin
#print axioms Graffiti384b.FiveChoice.Obstruction.exact_profile
#print axioms Graffiti384b.FiveChoice.Obstruction.nonlocal_solution
#print axioms Graffiti384b.FiveChoice.Obstruction.low_charges
