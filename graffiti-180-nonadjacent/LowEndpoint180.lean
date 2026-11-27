import PairClauses180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem cheap_color (G : SimpleGraph V) (v : V) (c : V→Bool) :
    ∃ i,(sideNeighbors G v c i).card≤G.degree v/2 := by
  classical
  obtain ⟨i,cheap⟩ := cheap_side (G.neighborFinset v) c
  rw [card_neighborFinset_eq_degree] at cheap
  change 2*(sideNeighbors G v c i).card≤G.degree v at cheap
  exact ⟨i,by omega⟩

theorem small_sum (G : SimpleGraph V) {a b : V} (pair : TransPair G a b)
    (pay : G.degree a/2+G.degree b/2≤PairBudget G a b) : ¬BothPossible G a b := by
  intro both
  obtain ⟨c,old⟩ := (color_function ..).mp pair.2
  obtain ⟨i,small⟩ := cheap_color G a c
  obtain ⟨j,low⟩ := cheap_color G b c
  have cap := card_union_le (sideNeighbors G a c i) (sideNeighbors G b c j)
  have impossible := both c old i j
  omega

/-- A transversal with one endpoint of degree at most three and its other
endpoint of degree different from four suffices at all roots. The degrees
of all vertices outside the transversal are unrestricted. -/
theorem low_endpoint (G : SimpleGraph V) {a b : V} (pair : TransPair G a b)
    (low : G.degree a≤3) (other : G.degree b≠4) : ∀ K,¬PairCover G K := by
  intro K cover
  have rev : TransPair G b a := ⟨pair.1.symm,by simpa only [pair_comm b a] using pair.2⟩
  have bk := partner_forced G cover pair (fun solo => by have := solo.1;omega)
  have ak := partner_forced G cover rev (fun solo => other solo.1)
  apply small_sum G pair _ ((cover.2 _ _ pair).2.2 ak bk)
  unfold PairBudget
  omega

#print axioms cheap_color
#print axioms small_sum
#print axioms low_endpoint
end Minimal180.PairRepair
