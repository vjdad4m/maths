import DepletedGraphLift

namespace Graffiti199Depleted

open Graffiti199K2.NearPacking.Depleted
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

abbrev Survives (D : Finset V) := {v : V // v ∉ D}

/-- Small deletions preserve reachability. At exactly three deletions
the remaining graph may also have a single isolated vertex outside
a component containing every other remaining vertex. -/
theorem edgeReach_of_singleton_cuts
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (three : ∀ D : Finset V, D.card = 3 →
      (G.induce {v | v ∉ D}).Preconnected ∨
        ∃ s : Survives D, (∀ t : Survives D, ¬ G.Adj s.val t.val) ∧
          ∀ x y : Survives D, x ≠ s → y ≠ s → (G.induce {v | v ∉ D}).Reachable x y) :
    EdgeReachAfterSmallDeletion G := by
  intro D small a b c d ab cd
  by_cases fewer : D.card < 3
  · exact below D fewer a c
  · rcases three D (by omega) with pc|⟨s,iso,connected⟩
    · exact pc a c
    · exact connected a c (fun e => iso b (e ▸ ab)) (fun e => iso d (e ▸ cd))

variable [Fintype V] {loss : Bool}

/-- The graph layout has order 15 with one terminal loss and order 16
with no terminal loss. -/
theorem NormalizedDepleted.order (L : NormalizedDepleted G loss) :
    Fintype.card V = if loss then 15 else 16 := by
  classical
  let A := (Finset.univ : Finset K).map L.inner
  let B := ((Finset.univ : Finset O).filter fun i => terminalKept loss i = true).map L.terminal
  have memA (v : V) : v ∈ A ↔ v ∈ innerRegion L.inner := by simp [A,innerRegion]
  have memB (v : V) : v ∈ B ↔ v ∈ terminalRegion L.terminal loss := by
    simp [B,terminalRegion,Finset.mem_map,Finset.mem_filter]
  have dis : Disjoint A B := Finset.disjoint_left.mpr fun v a b =>
    Set.disjoint_left.mp L.separate ((memA v).mp a) ((memB v).mp b)
  have full : A ∪ B = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    exact Finset.mem_union.mpr ((L.cover v).imp (memA v).mpr (memB v).mpr)
  have ac : A.card = 10 := by simp [A]
  have bc : B.card = if loss then 5 else 6 := by
    dsimp [B]
    rw [Finset.card_map]
    cases loss <;> decide
  have sum := Finset.card_union_of_disjoint dis
  rw [full,Finset.card_univ,ac,bc] at sum
  cases loss <;> simpa using sum

variable [DecidableRel G.Adj]

/-- The normalized order-15 or order-16 block layout yields a Hamiltonian
path under the corresponding connectivity and degree properties. -/
theorem normalized_depleted_order_and_path (L : NormalizedDepleted G loss)
    (reach : EdgeReachAfterSmallDeletion G)
    (minDegree : 3 ≤ G.degree (L.inner 3)) (highDegree : G.degree (L.inner 3) ≠ 3) :
    (Fintype.card V = if loss then 15 else 16) ∧ Nonempty (PathOn G Set.univ) :=
  ⟨L.order,traceable_of_normalized_depleted L reach (by omega)⟩

#print axioms edgeReach_of_singleton_cuts
#print axioms NormalizedDepleted.order
#print axioms normalized_depleted_order_and_path

end Graffiti199Depleted
