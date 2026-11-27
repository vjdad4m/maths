import NormalizedDepleted

namespace Graffiti199Depleted

open Graffiti199K2.NearPacking.Depleted
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {loss : Bool} (L : NormalizedDepleted G loss)

private theorem no_low_back_to_loose (off : 3 ∉ chosenHighs L.row) :
    ¬ G.Adj (L.inner 3) (L.inner 4) ∧
    ¬ G.Adj (L.inner 3) (L.inner 8) ∧
    ¬ G.Adj (L.inner 3) (L.inner 9) := by
  have outsideChoice : (3 : K) ∉ (chosenHighs L.row).map inside := by
    intro h
    obtain ⟨a,am,eq⟩ := List.mem_map.mp h
    have ae : a = 3 := Fin.ext (congrArg (fun v : K => v.val) eq)
    exact off (ae ▸ am)
  have excludes {i : K} {ns : List K} (eq : innerLowNeighbors L.row i = some ns)
      (notMem : 3 ∉ ns) : ¬ G.Adj (L.inner 3) (L.inner i) := by
    intro h
    obtain ⟨u,um,ue⟩ := L.innerLow i ns eq (L.inner 3) h.symm
    exact notMem (L.inner.injective ue ▸ um)
  refine ⟨excludes (i := 4) rfl (by decide), excludes (i := 8) rfl ?_,
    excludes (i := 9) rfl ?_⟩
  · simp only [chosenHighs,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at outsideChoice
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    exact fun h => h.elim (by decide) (fun h => outsideChoice (h.elim Or.inl (fun h => Or.inr (Or.inl h))))
  · simp only [chosenHighs,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at outsideChoice
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    exact fun h => h.elim (by decide) (fun h => outsideChoice (Or.inr (Or.inr h)))

variable [Fintype V] [DecidableRel G.Adj]

/-- In the exceptional table row, the loose port is an available endpoint.
Four neighbors force some edge to the terminal region. -/
theorem NormalizedDepleted.traceable_of_sparse_loose
    (degree : 4 ≤ G.degree (L.inner 3))
    (off : 3 ∉ chosenHighs L.row)
    (noEdge : ¬ G.Adj (L.inner 3) (L.inner 7))
    (ok : paths L.row false 3 ≠ []) : Nonempty (PathOn G Set.univ) := by
  classical
  by_contra notTrace
  obtain ⟨p,last⟩ := L.inner_path (fun e => by cases e) ok
  have outside (v : V) (vo : v ∈ terminalRegion L.terminal loss) :
      ¬ G.Adj (L.inner 3) v := fun e =>
    notTrace (L.finish_with_contact p vo (last.symm ▸ e))
  have missA : ¬ G.Adj (L.inner 3) (L.inner 1) := fun e => L.innerNonedges 1 3 (by decide) e.symm
  have missB : ¬ G.Adj (L.inner 3) (L.inner 2) := fun e => L.innerNonedges 2 3 (by decide) e.symm
  obtain ⟨miss4,miss8,miss9⟩ := no_low_back_to_loose L off
  let W : Finset V := {L.inner 0,L.inner 5,L.inner 6}
  have sub : G.neighborFinset (L.inner 3) ⊆ W := by
    intro v vn
    have adj := (G.mem_neighborFinset _ _).mp vn
    rcases L.cover v with hi|ho
    · obtain ⟨i,rfl⟩ := hi
      fin_cases i
      · simp [W]
      · exact (missA adj).elim
      · exact (missB adj).elim
      · exact (G.loopless _ adj).elim
      · exact (miss4 adj).elim
      · simp [W]
      · simp [W]
      · exact (noEdge adj).elim
      · exact (miss8 adj).elim
      · exact (miss9 adj).elim
    · exact (outside v ho adj).elim
  have small : W.card ≤ 3 := by
    have a := Finset.card_insert_le (L.inner 0) ({L.inner 5,L.inner 6} : Finset V)
    have b := Finset.card_insert_le (L.inner 5) ({L.inner 6} : Finset V)
    simp only [Finset.card_singleton] at b
    change (insert (L.inner 0) ({L.inner 5,L.inner 6} : Finset V)).card ≤ 3
    omega
  have cap := (Finset.card_le_card sub).trans small
  rw [G.card_neighborFinset_eq_degree] at cap
  omega

/-- A normalized depleted layout is traceable for both terminal loss modes.
The only global inputs are the edge-to-edge small-deletion property and
the degree bound at the first loose port. -/
theorem traceable_of_normalized_depleted
    (reach : EdgeReachAfterSmallDeletion G)
    (degree : 4 ≤ G.degree (L.inner 3)) : Nonempty (PathOn G Set.univ) := by
  classical
  by_cases edge : G.Adj (L.inner 3) (L.inner 7)
  · rcases choices L.row true L.possible with small|bad
    · exact L.traceable_of_small_blocked reach (fun _ => edge) small
    · cases bad.1
  · rcases choices L.row false L.possible with small|⟨_,off,ok⟩
    · exact L.traceable_of_small_blocked reach (fun e => by cases e) small
    · exact L.traceable_of_sparse_loose degree off edge ok

#print axioms NormalizedDepleted.traceable_of_sparse_loose
#print axioms traceable_of_normalized_depleted

end Graffiti199Depleted
