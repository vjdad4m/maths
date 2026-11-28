import FiveEdgeBudget189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.FiveCheapBudget Graffiti189LongestPath.FiveEdgeBudget
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints from SmallSeparator189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
namespace Graffiti189LongestPath.FiveEdgeLayout
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b x y : V} {p : G.Walk a b} {H : Finset V}

theorem left (A : PairData p H x y 1 4 10 16) (hc : G.Connected)
    (hp : IsLongest p) (cap : ∀ v,(DistanceTwo G v).card≤6) : G.degree a≤5 := by
  classical
  have xx := pins_at A
  have d0 : p.getVert 0=a := by simp
  have ep : G.Adj (p.getVert 1) a := by
    have z := (adjacency_on_spine A 0 (by decide)).symm
    simpa only [d0] using z
  have eH : ∀ v∈H, ¬ G.Adj a v := fun v h ev =>
    (Graffiti189LongestPath.no_endpoints hp (A.off _ h)).1 ev.symm
  have self : ¬G.Adj a (p.getVert 0) := by rw [d0]; exact G.irrefl
  have noA : ¬G.Adj a (p.getVert 2) := start_not_adj_pin_successor hp (A.off _ A.xH) xx.1
  have noB : ¬G.Adj a (p.getVert 5) := start_not_adj_pin_successor hp (A.off _ A.xH) xx.2.1
  let U : Finset V := {p.getVert 1,p.getVert 4,p.getVert 3}
  apply at_endpoint A hc hp cap (Or.inl rfl) a ep eH (U := U)
  · simp [U]
  · have z := card_insert_le (p.getVert 1) ({p.getVert 4,p.getVert 3} : Finset V)
    have w := card_insert_le (p.getVert 4) ({p.getVert 3} : Finset V)
    rw [card_singleton] at w
    dsimp [U]
    omega
  · intro v ev adj
    rcases cheap_neighbors A hc hp cap (Or.inl rfl) adj with eq|mem
    · exact (eH x A.xH (eq ▸ ev)).elim
    obtain ⟨m,ma,rfl⟩ := mem_image.mp mem
    simp only [allowed,targets,flanks,mem_insert,mem_singleton] at ma
    rcases ma with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact (self ev).elim | exact (noA ev).elim | exact (noB ev).elim |
      exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inl (by simp [U])
  · intro m hm
    rcases hm with rfl|rfl
    · exact Or.inr (start_not_adj_pin_successor hp (A.off _ A.yH) xx.2.2.1)
    · exact Or.inr (start_not_adj_pin_successor hp (A.off _ A.yH) xx.2.2.2)
#print axioms left

theorem right (A : PairData p H x y 13 16 1 7) (hc : G.Connected)
    (hp : IsLongest p) (cap : ∀ v,(DistanceTwo G v).card≤6) : G.degree b≤5 := by
  classical
  have xx := pins_at A
  have d0 : p.getVert 17=b := by rw [←A.pathLen,Walk.getVert_length]
  have ep : G.Adj (p.getVert 16) b := by
    have z := adjacency_on_spine A 16 (by decide)
    simpa only [d0] using z
  have eH : ∀ v∈H, ¬ G.Adj b v := fun v h ev =>
    (Graffiti189LongestPath.no_endpoints hp (A.off _ h)).2 ev.symm
  have self : ¬G.Adj b (p.getVert 17) := by rw [d0]; exact G.irrefl
  have noA : ¬G.Adj b (p.getVert 12) := end_not_adj_pin_predecessor hp (A.off _ A.xH) xx.1
  have noB : ¬G.Adj b (p.getVert 15) := end_not_adj_pin_predecessor hp (A.off _ A.xH) xx.2.1
  let U : Finset V := {p.getVert 16,p.getVert 13,p.getVert 14}
  apply at_endpoint A hc hp cap (Or.inr rfl) b ep eH (U := U)
  · simp [U]
  · have z := card_insert_le (p.getVert 16) ({p.getVert 13,p.getVert 14} : Finset V)
    have w := card_insert_le (p.getVert 13) ({p.getVert 14} : Finset V)
    rw [card_singleton] at w
    dsimp [U]
    omega
  · intro v ev adj
    rcases cheap_neighbors A hc hp cap (Or.inr rfl) adj with eq|mem
    · exact (eH x A.xH (eq ▸ ev)).elim
    obtain ⟨m,ma,rfl⟩ := mem_image.mp mem
    simp only [allowed,targets,flanks,mem_insert,mem_singleton] at ma
    rcases ma with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact (self ev).elim | exact (noA ev).elim | exact (noB ev).elim |
      exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | exact Or.inl (by simp [U])
  · intro m hm
    rcases hm with rfl|rfl
    · exact Or.inl (end_not_adj_pin_predecessor hp (A.off _ A.yH) xx.2.2.1)
    · exact Or.inl (end_not_adj_pin_predecessor hp (A.off _ A.yH) xx.2.2.2)
#print axioms right
end Graffiti189LongestPath.FiveEdgeLayout
