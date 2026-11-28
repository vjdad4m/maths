import FiveScores
import FiveLocal
namespace Graffiti384b.Four29.FiveWitness
open Finset SimpleGraph LowSample

/-- A graph with exactly the target profile and five triangle contacts.
Its anchor counts exceed the previous sample cap for this exposure. -/
theorem profile : (types graph).card=29 ∧ (nonleaves graph).card=29 ∧ (high graph).card=27 ∧
    twos graph={27,28} ∧ graph.neighborFinset 27={0,1} ∧ graph.neighborFinset 28={2,3} ∧
    triangleContacts graph 27 28={4,5,6,7,8} ∧
    trianglesAt graph 0=2 ∧ trianglesAt graph 1=8 ∧ trianglesAt graph 2=5 ∧ trianglesAt graph 3=6 := by
  refine ⟨diversity,degrees.1,degrees.2.1,degrees.2.2.1,degrees.2.2.2.1,degrees.2.2.2.2,contacts,?_⟩
  simp only [score_table]
  decide

/-- The minimum number of pins outside the two ears, their anchors and
all anchor-triangle contacts is exactly one. -/
theorem minimum_outside : IsLeast {n : ℕ | ∃P Q:Finset V, ((P∪Q)\localVertices).card=n ∧ Disjoint P Q ∧
    twos graph⊆P∪Q ∧ (∀v∈P,2≤nbr graph v Q) ∧ (∀v∈Q,2≤nbr graph v P)} 1 := by
  refine ⟨one_outside,?_⟩
  rintro n ⟨P,Q,size,dis,ears,lp,rq⟩
  by_contra! zero
  have eq : ((P∪Q)\localVertices).card=0 := by omega
  have sub : P∪Q⊆localVertices := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp eq)
  have e : (27:V)∈twos graph := by rw [degrees.2.2.1]; exact mem_insert_self ..
  exact no_local_cut P Q (subset_union_left.trans sub) (subset_union_right.trans sub) dis lp rq (ears e)

/-- A concrete set of 15 vertices two-dominates the graph. -/
theorem dominated : gamma graph≤bound graph := by
  have good : TwoDominates graph seed := by unfold TwoDominates; decide
  have feasible : seed.card∈{k : ℕ | ∃ d,TwoDominates graph d ∧ d.card=k} := ⟨_,good,rfl⟩
  have win : gamma graph≤seed.card := Nat.sInf_le feasible
  have size : seed.card=15 := by decide
  rw [bound,diversity]
  exact win.trans (by rw [size]; decide)
end Graffiti384b.Four29.FiveWitness
#print axioms Graffiti384b.Four29.FiveWitness.profile
#print axioms Graffiti384b.Four29.FiveWitness.minimum_outside
#print axioms Graffiti384b.Four29.FiveWitness.dominated
