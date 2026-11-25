import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

namespace Graffiti394

open Finset

/-- Every vertex outside the set has two distinct neighbors in the set. -/
def IsTwoDominating {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, v ∈ D ∨ ∃ x y, x ∈ D ∧ y ∈ D ∧ x ≠ y ∧ G.Adj v x ∧ G.Adj v y

noncomputable def twoDominationNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = k}

/-- The two endpoints of each of the indexed edges, all pairwise distinct. -/
def HasMatching {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ endpoints : Fin k × Bool → V, Function.Injective endpoints ∧
    ∀ i, G.Adj (endpoints (i, false)) (endpoints (i, true))

noncomputable def matchingNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {k | HasMatching G k}

def DegreeTwo {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Set V :=
  {v | G.degree v = 2}

noncomputable def degreeTwoEdges {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] : ℕ :=
  (G.induce (DegreeTwo G)).edgeSet.ncard

noncomputable def localIndependence {V : Type*} (G : SimpleGraph V) (v : V) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

noncomputable def minLocalCount {V : Type*} (G : SimpleGraph V) : ℕ :=
  ({v | ∀ w, localIndependence G v ≤ localIndependence G w} : Set V).ncard

def Conjecture394 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → 2 < Fintype.card V →
    twoDominationNumber G ≤ matchingNumber G + degreeTwoEdges G + minLocalCount G

abbrev Vertex := Fin 15

/-- One copy of the subdivided K₄, with the smaller endpoint listed first. -/
def pieceEdges : List (Fin 7 × Fin 7) :=
  [(0, 3), (0, 4), (0, 6), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (3, 5)]

def pieceAdj (u v : Fin 7) : Prop :=
  (u, v) ∈ pieceEdges ∨ (v, u) ∈ pieceEdges

instance (u v : Fin 7) : Decidable (pieceAdj u v) := by
  unfold pieceAdj
  infer_instance

def copy (i : Fin 2) (v : Fin 7) : Vertex :=
  ⟨7 * i.val + v.val, by have := i.isLt; have := v.isLt; omega⟩

def edges : List (Vertex × Vertex) :=
  pieceEdges.map (fun (v, w) => (copy 0 v, copy 0 w)) ++
  pieceEdges.map (fun (v, w) => (copy 1 v, copy 1 w)) ++ [(0, 7), (0, 14)]

def adj (v w : Vertex) : Prop :=
  (v, w) ∈ edges ∨ (w, v) ∈ edges

instance (v w : Vertex) : Decidable (adj v w) := by
  unfold adj
  infer_instance

def graph : SimpleGraph Vertex where
  Adj := adj
  symm := fun _ _ => Or.symm
  loopless := by
    change ∀ v : Vertex, ¬ adj v v
    decide

instance : DecidableRel graph.Adj := fun v w => inferInstanceAs (Decidable (adj v w))

theorem graph_connected : graph.Connected := by
  have v1 : graph.Reachable 0 1 :=
    (show graph.Adj 0 4 by decide).reachable.trans (show graph.Adj 4 1 by decide).reachable
  have v6 : graph.Reachable 0 6 := (show graph.Adj 0 6 by decide).reachable
  have v7 : graph.Reachable 0 7 := (show graph.Adj 0 7 by decide).reachable
  have v11 : graph.Reachable 0 11 := v7.trans (show graph.Adj 7 11 by decide).reachable
  have v13 : graph.Reachable 0 13 := v7.trans (show graph.Adj 7 13 by decide).reachable
  have v8 : graph.Reachable 0 8 := v11.trans (show graph.Adj 11 8 by decide).reachable
  apply (SimpleGraph.connected_iff_exists_forall_reachable graph).mpr
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact .rfl
  · exact v1
  · exact v6.trans (show graph.Adj 6 2 by decide).reachable
  · exact (show graph.Adj 0 3 by decide).reachable
  · exact (show graph.Adj 0 4 by decide).reachable
  · exact v1.trans (show graph.Adj 1 5 by decide).reachable
  · exact v6
  · exact v7
  · exact v8
  · exact v13.trans (show graph.Adj 13 9 by decide).reachable
  · exact v7.trans (show graph.Adj 7 10 by decide).reachable
  · exact v11
  · exact v8.trans (show graph.Adj 8 12 by decide).reachable
  · exact v13
  · exact (show graph.Adj 0 14 by decide).reachable

private theorem matching_upper {k : ℕ} (h : HasMatching graph k) : k ≤ 7 := by
  obtain ⟨f, hf, -⟩ := h
  have hcard := Fintype.card_le_of_injective f hf
  simp at hcard
  omega

private def matchingPairs : Fin 7 → Vertex × Vertex
  | 0 => (0, 14)
  | 1 => (1, 4)
  | 2 => (2, 6)
  | 3 => (3, 5)
  | 4 => (7, 10)
  | 5 => (8, 11)
  | 6 => (9, 12)

private def matchingEndpoints (p : Fin 7 × Bool) : Vertex :=
  if p.2 then (matchingPairs p.1).2 else (matchingPairs p.1).1

theorem matching_eq : matchingNumber graph = 7 := by
  have lower : HasMatching graph 7 := by
    refine ⟨matchingEndpoints, ?_, by decide⟩
    change ∀ a b : Fin 7 × Bool, matchingEndpoints a = matchingEndpoints b → a = b
    decide
  have upper : ∀ k ∈ {k | HasMatching graph k}, k ≤ 7 := fun _ hk => matching_upper hk
  apply le_antisymm
  · exact csSup_le ⟨7, lower⟩ upper
  · exact le_csSup ⟨7, upper⟩ lower

private theorem degree_two_nonadjacent :
    ∀ v w : Vertex, graph.degree v = 2 → graph.degree w = 2 → ¬ graph.Adj v w := by
  decide

theorem degree_two_edges_eq : degreeTwoEdges graph = 0 := by
  have h : graph.induce (DegreeTwo graph) = ⊥ := by
    ext v w
    exact iff_false_intro (degree_two_nonadjacent v.val w.val v.property w.property)
  unfold degreeTwoEdges
  rw [h, SimpleGraph.edgeSet_bot, Set.ncard_empty]

private theorem triangle_free :
    ∀ v x y : Vertex, graph.Adj v x → graph.Adj v y → ¬ graph.Adj x y := by
  decide

private theorem local_eq_degree (v : Vertex) : localIndependence graph v = graph.degree v := by
  let H := graph.induce (graph.neighborSet v)
  have hH : ∀ x y : graph.neighborSet v, ¬ H.Adj x y :=
    fun x y => triangle_free v x.val y.val x.property y.property
  change H.indepNum = graph.degree v
  have hcard : Fintype.card (graph.neighborSet v) = graph.degree v :=
    graph.card_neighborSet_eq_degree v
  obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
  apply le_antisymm
  · rw [← hcard, ← hs.2]
    exact s.card_le_univ
  · rw [← hcard]
    exact SimpleGraph.IsIndepSet.card_le_indepNum (t := univ) (fun _ _ _ _ _ => hH _ _)

theorem min_local_count_eq : minLocalCount graph = 1 := by
  have only_min :
      ∀ v : Vertex, (∀ w : Vertex, graph.degree v ≤ graph.degree w) ↔ v = 14 := by
    decide
  have h : ({v | ∀ w, localIndependence graph v ≤ localIndependence graph w} : Set Vertex) =
      {14} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, local_eq_degree]
    exact only_min v
  rw [minLocalCount, h, Set.ncard_singleton]

/-- Every nonroot vertex has its entire neighborhood in its own copy. -/
private theorem nonroot_neighbors :
    ∀ (i : Fin 2) (v : Fin 7) (u : Vertex), v ≠ 0 → graph.Adj (copy i v) u →
      ∃ w : Fin 7, u = copy i w ∧ pieceAdj v w := by
  decide

private def GoodInPiece (D : Finset (Fin 7)) (v : Fin 7) : Prop :=
  v ∈ D ∨ ∃ x y : Fin 7, x ∈ D ∧ y ∈ D ∧ x ≠ y ∧ pieceAdj v x ∧ pieceAdj v y

instance (D : Finset (Fin 7)) (v : Fin 7) : Decidable (GoodInPiece D v) := by
  unfold GoodInPiece
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem piece_lower :
    ∀ D : Finset (Fin 7), (∀ v : Fin 7, v ≠ 0 → GoodInPiece D v) → 4 ≤ D.card := by
  decide

private theorem piece_restriction {D : Finset Vertex} (hD : IsTwoDominating graph D)
    (i : Fin 2) :
    4 ≤ (univ.filter fun v : Fin 7 => copy i v ∈ D).card := by
  apply piece_lower
  intro v hv
  rcases hD (copy i v) with h | ⟨x, y, hx, hy, hxy, hvx, hvy⟩
  · exact Or.inl (by simpa using h)
  · obtain ⟨a, rfl, ha⟩ := nonroot_neighbors i v x hv hvx
    obtain ⟨b, rfl, hb⟩ := nonroot_neighbors i v y hv hvy
    exact Or.inr ⟨a, b, by simpa using hx, by simpa using hy, fun e => hxy (congrArg _ e), ha, hb⟩

private theorem copy_injective (i : Fin 2) : Function.Injective (copy i) := by
  intro a b h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [copy] at hval
  omega

private def copyVertices (D : Finset Vertex) (i : Fin 2) : Finset Vertex :=
  (univ.filter fun v : Fin 7 => copy i v ∈ D).map ⟨copy i, copy_injective i⟩

private theorem copyVertices_subset (D : Finset Vertex) (i : Fin 2) : copyVertices D i ⊆ D := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_map.mp hv
  exact (mem_filter.mp hw).2

private theorem all_dom_sets_large (D : Finset Vertex) (hD : IsTwoDominating graph D) :
    9 ≤ D.card := by
  have hleaf : (14 : Vertex) ∈ D := by
    rcases hD 14 with h | ⟨x, y, -, -, hxy, hx, hy⟩
    · exact h
    · have only_neighbor : ∀ v : Vertex, graph.Adj 14 v → v = 0 := by decide
      exact (hxy ((only_neighbor x hx).trans (only_neighbor y hy).symm)).elim
  have range0 : ∀ v ∈ copyVertices D 0, v.val < 7 := by
    intro v hv
    obtain ⟨w, -, rfl⟩ := mem_map.mp hv
    change 7 * (0 : Fin 2).val + w.val < 7
    simp [w.isLt]
  have range1 : ∀ v ∈ copyVertices D 1, 7 ≤ v.val ∧ v.val < 14 := by
    intro v hv
    obtain ⟨w, -, rfl⟩ := mem_map.mp hv
    have := w.isLt
    change 7 ≤ 7 + w.val ∧ 7 + w.val < 14
    omega
  have disjoint_copies : Disjoint (copyVertices D 0) (copyVertices D 1) :=
    Finset.disjoint_left.mpr (fun v h0 h1 => (Nat.not_lt_of_ge (range1 v h1).1) (range0 v h0))
  have leaf_out : (14 : Vertex) ∉ copyVertices D 0 ∪ copyVertices D 1 := by
    simp only [mem_union, not_or]
    exact ⟨fun h => (by decide : ¬ (14 : Vertex).val < 7) (range0 14 h),
           fun h => (by decide : ¬ (14 : Vertex).val < 14) (range1 14 h).2⟩
  have hsub : insert (14 : Vertex) (copyVertices D 0 ∪ copyVertices D 1) ⊆ D :=
    Finset.insert_subset_iff.mpr ⟨hleaf,
      Finset.union_subset (copyVertices_subset D 0) (copyVertices_subset D 1)⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_not_mem leaf_out, Finset.card_union_of_disjoint disjoint_copies] at hcard
  have h0 : 4 ≤ (copyVertices D 0).card := by simpa [copyVertices] using piece_restriction hD 0
  have h1 : 4 ≤ (copyVertices D 1).card := by simpa [copyVertices] using piece_restriction hD 1
  omega

private def witness : Finset Vertex := {0, 1, 2, 3, 7, 8, 9, 10, 14}

theorem two_domination_eq : twoDominationNumber graph = 9 := by
  have hw : IsTwoDominating graph witness := by
    unfold IsTwoDominating
    decide
  have wc : witness.card = 9 := by decide
  have h : 9 ∈ {k | ∃ D : Finset Vertex, IsTwoDominating graph D ∧ D.card = k} :=
    ⟨witness, hw, wc⟩
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) h
  · apply le_csInf ⟨9, h⟩
    rintro _ ⟨D, hD, rfl⟩
    exact all_dom_sets_large D hD

theorem not_conjecture394 : ¬ Conjecture394 := by
  intro h
  have bound := h Vertex graph graph_connected (by decide)
  rw [two_domination_eq, matching_eq, degree_two_edges_eq, min_local_count_eq] at bound
  omega

#print axioms not_conjecture394

end Graffiti394
