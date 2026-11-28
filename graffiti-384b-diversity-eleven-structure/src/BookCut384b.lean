import PositivePalette384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private TrianglePrune.skeleton TrianglePrune.scores TrianglePrune.triangle_iff from TrianglePrune384b
open private Repair.nbr_mono from Repair384b

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two fixed shores supported twice across the pinned cut can protect
all high vertices and every additional vertex on either shore. -/
theorem pinned_budget {P Q : Finset V} (dis : Disjoint P Q)
    (left : ∀ v∈P, 2≤nbr G v Q) (right : ∀ v∈Q, 2≤nbr G v P) :
    2*gamma G+((high G)∪P∪Q).card≤2*Fintype.card V := by
  apply PositivePalette.count_covered G
  apply PositivePalette.complete G dis _ left right
  intro v hv np nq
  have hi : v∈high G := by
    rcases mem_union.mp hv with hv|h
    · exact (mem_union.mp hv).resolve_right np
    · exact (nq h).elim
  exact (mem_filter.mp hi).2

omit [Fintype V] in
private theorem two_neighbors {v a b : V} (ab : a≠b) (va : G.Adj v a) (vb : G.Adj v b) :
    2≤nbr G v {a,b} := by
  have sub : ({a,b}:Finset V) ⊆ ({a,b}:Finset V).filter (G.Adj v) := by
    intro x hx
    refine mem_filter.mpr ⟨hx,?_⟩
    rcases mem_insert.mp hx with rfl|h
    · exact va
    · simpa only [mem_singleton.mp h] using vb
  simpa [nbr,ab] using card_le_card sub

/-- A pair of genuine degree-two book pages supplies two extra protected
vertices, regardless of the books or cycles elsewhere in the graph. -/
theorem book_budget {e f a b : V} (ef : e≠f) (ab : a≠b)
    (ea : G.Adj e a) (eb : G.Adj e b) (fa : G.Adj f a) (fb : G.Adj f b)
    (de : G.degree e=2) (df : G.degree f=2) :
    2*gamma G+(high G).card+2≤2*Fintype.card V := by
  have dis : Disjoint ({a,b}:Finset V) {e,f} := by
    apply disjoint_left.mpr
    intro x h1 h2
    simp only [mem_insert,mem_singleton] at h1 h2
    rcases h1 with rfl|rfl <;> rcases h2 with h|h
    · exact ea.ne h.symm
    · exact fa.ne h.symm
    · exact eb.ne h.symm
    · exact fb.ne h.symm
  have win := pinned_budget G dis (by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl
    · exact two_neighbors G ef ea.symm fa.symm
    · exact two_neighbors G ef eb.symm fb.symm)
    (by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl
    · exact two_neighbors G ab ea eb
    · exact two_neighbors G ab fa fb)
  have separate : Disjoint (high G) ({e,f}:Finset V) := by
    apply disjoint_left.mpr
    intro v vh vm
    have d := (mem_filter.mp vh).2
    simp only [mem_insert,mem_singleton] at vm
    rcases vm with rfl|rfl <;> omega
  have card : ((high G)∪({e,f}:Finset V)).card=(high G).card+2 := by
    rw [card_union_of_disjoint separate,card_pair ef]
  have sub : (high G)∪({e,f}:Finset V) ⊆ (high G)∪({a,b}:Finset V)∪({e,f}:Finset V) := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_right _ h
  have le := card_le_card sub
  omega

theorem exact_of_book {e f a b : V} (ef : e≠f) (ab : a≠b)
    (ea : G.Adj e a) (eb : G.Adj e b) (fa : G.Adj f a) (fb : G.Adj f b)
    (de : G.degree e=2) (df : G.degree f=2)
    (quota : (types G).card≤(high G).card+2) : gamma G≤bound G := by
  have win := book_budget G ef ab ea eb fa fb de df
  unfold bound
  omega

#print axioms pinned_budget
#print axioms book_budget
#print axioms exact_of_book
end Graffiti384b.DiversityEleven
