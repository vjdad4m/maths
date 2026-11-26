import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Counterexample to Written on the Wall II #354

Join two centers by an edge. Place one branch vertex on one side and
two on the other, and give the first center one direct leaf.
At each branch vertex b, attach two copies of b-v-x-u-y and give
each x an additional private leaf. The result has 36 vertices.

The open neighborhood of the degree-two vertices induces 15 isolated
vertices. The two centers and the six pairs x,u form a minimum total
dominating set of size 14. Thus the exact bound would require 14 ≥ 15.

Gebendorfer's earlier example in Closed-Neighborhood Components, Open
Packings, and Total Domination in Trees (2026), section 6, rejects a
coefficient-1 variant and gives equality for the catalogue's 1/2.
No claim of minimum order is made here.
Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti354

open Finset SimpleGraph
open scoped BigOperators

section Definitions
variable {V : Type*} (G : SimpleGraph V)

def TotalDominates (D : Finset V) : Prop := ∀ v, ∃ w ∈ D, G.Adj v w

noncomputable def totalDominationNumber : ℕ :=
  sInf {k : ℕ | ∃ D, TotalDominates G D ∧ D.card = k}

noncomputable def componentCount : ℕ := Nat.card G.ConnectedComponent

variable [Fintype V]

/-- Definition 64 uses the maximum of the ordinary graph distances on connected graphs. -/
noncomputable def eccentricity (v : V) : ℕ := univ.sup (G.dist v)

noncomputable def centers : Finset V :=
  @Finset.filter V (fun v => ∀ w, eccentricity G v ≤ eccentricity G w)
    (fun _ => Classical.propDecidable _) univ

theorem mem_centers {v : V} :
    v ∈ centers G ↔ ∀ w, eccentricity G v ≤ eccentricity G w := by
  unfold centers
  exact (@Finset.mem_filter V _ (fun _ => Classical.propDecidable _) univ v).trans
    ⟨And.right, fun h => ⟨mem_univ v,h⟩⟩

variable [DecidableRel G.Adj]

/-- The open union of the neighborhoods of vertices of degree two. -/
def openTwoNeighborhood : Finset V :=
  univ.filter (fun v => ∃ w, G.Adj v w ∧ G.degree w = 2)

noncomputable def openNeighborhoodComponents : ℕ :=
  componentCount (G.induce (openTwoNeighborhood G : Set V))

end Definitions

abbrev Vertex := Fin 36

/-- Vertex 0 is the root. Vertices 0 and 1 form the central edge.
The three branching vertices 3, 14 and 25 carry two copies each
of a four-edge path with an extra leaf on its middle vertex. -/
def parent (v : Vertex) : Vertex :=
  ![0, 0, 0, 0, 3, 4, 5, 6, 5, 3, 9, 10, 11, 10,
    1, 14, 15, 16, 17, 16, 14, 20, 21, 22, 21,
    1, 25, 26, 27, 28, 27, 25, 31, 32, 33, 32] v

private theorem parent_lt : ∀ v : Vertex, v ≠ 0 → parent v < v := by decide

def witnessAdj (u v : Vertex) : Prop :=
  (u ≠ 0 ∧ parent u = v) ∨ (v ≠ 0 ∧ parent v = u)

def witness : SimpleGraph Vertex where
  Adj := witnessAdj
  symm := fun _ _ h => h.symm
  loopless := by
    intro v h
    obtain h | h := h
    · exact (ne_of_lt (parent_lt v h.1)) h.2
    · exact (ne_of_lt (parent_lt v h.1)) h.2

instance : DecidableRel witness.Adj := by
  intro u v
  change Decidable ((u ≠ 0 ∧ parent u = v) ∨ (v ≠ 0 ∧ parent v = u))
  infer_instance

private def up (next : Vertex → Vertex) : ℕ → Vertex → Vertex
  | 0, v => v
  | k + 1, v => up next k (next v)

private theorem upWalk {next : Vertex → Vertex} {r : Vertex}
    (hEdge : ∀ v, v ≠ r → witness.Adj v (next v)) (k : ℕ) (v : Vertex)
    (h : up next k v = r) : ∃ p : witness.Walk v r, p.length ≤ k := by
  induction k generalizing v with
  | zero =>
    change v = r at h
    subst v
    exact ⟨.nil, by simp⟩
  | succ k ih =>
    by_cases hv : v = r
    · subst v
      exact ⟨.nil, by simp⟩
    · obtain ⟨p,hp⟩ := ih (next v) h
      exact ⟨.cons (hEdge v hv) p, by simpa⟩

private theorem up0 : ∀ v : Vertex, up parent 6 v = 0 := by decide

private def parentFrom1 (v : Vertex) : Vertex :=
  if v = 0 ∨ v = 1 then 1 else parent v

private theorem up1 : ∀ v : Vertex, up parentFrom1 6 v = 1 := by decide

private theorem parentFrom1_adj :
    ∀ v : Vertex, v ≠ 1 → witness.Adj v (parentFrom1 v) := by decide

theorem witness_connected : witness.Connected := by
  apply (connected_iff_exists_forall_reachable witness).mpr
  refine ⟨0,fun v => ?_⟩
  obtain ⟨p,_⟩ := upWalk (r := 0) (next := parent) (fun v hv => Or.inl ⟨hv,rfl⟩) 6 v (up0 v)
  exact ⟨p.reverse⟩

theorem witness_order : Fintype.card Vertex = 36 := by decide

set_option maxHeartbeats 5000000 in
private theorem degree_sum : ∑ v : Vertex, witness.degree v = 70 := by decide

theorem witness_tree : witness.IsTree := by
  apply (isTree_iff_connected_and_card).2
  refine ⟨witness_connected,?_⟩
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, witness_order]
  have hsum := witness.sum_degrees_eq_twice_card_edges
  have he : (∑ v : Vertex, witness.degree v) = 70 := degree_sum
  rw [he] at hsum
  omega

/-- Coordinates along the axis from a left terminal leaf to a right terminal leaf. -/
private def layer (v : Vertex) : ℕ :=
  ![5, 6, 4, 4, 3, 2, 1, 0, 1, 3, 2, 1, 0, 1,
    7, 8, 9, 10, 11, 10, 8, 9, 10, 11, 10,
    7, 8, 9, 10, 11, 10, 8, 9, 10, 11, 10] v

private theorem layerParent :
    ∀ v : Vertex, layer v ≤ layer (parent v) + 1 ∧
      layer (parent v) ≤ layer v + 1 := by decide

private theorem layer_le_of_walk {u v : Vertex} (p : witness.Walk u v) :
    layer v ≤ layer u + p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have h : layer b ≤ layer a + 1 := by
      obtain h | h := hab
      · rw [← h.2]
        exact (layerParent a).2
      · rw [← h.2]
        exact (layerParent b).1
    simp only [Walk.length_cons]
    omega

private theorem layer_le_of_dist (u v : Vertex) :
    layer v ≤ layer u + witness.dist u v := by
  obtain ⟨p,hp⟩ := witness_connected.exists_walk_length_eq_dist u v
  exact hp ▸ layer_le_of_walk p

private theorem ecc_bounds_dist (u v : Vertex) : witness.dist u v ≤ eccentricity witness u :=
  le_sup (f := witness.dist u) (mem_univ v)

private theorem ecc_ge_six (v : Vertex) : 6 ≤ eccentricity witness v := by
  have ha := layer_le_of_dist 7 18
  change 11 ≤ 0 + witness.dist 7 18 at ha
  have ht : witness.dist 7 18 ≤ witness.dist 7 v + witness.dist v 18 :=
    witness_connected.dist_triangle
  rw [witness.dist_comm (u := 7) (v := v)] at ht
  have h₀ := ecc_bounds_dist v 7
  have h₁ := ecc_bounds_dist v 18
  omega

private theorem ecc0 : eccentricity witness 0 ≤ 6 := by
  apply Finset.sup_le
  intro v _
  obtain ⟨p,hp⟩ := upWalk (r := 0) (next := parent) (fun v hv => Or.inl ⟨hv,rfl⟩) 6 v (up0 v)
  exact (witness.dist_le p.reverse).trans (by simpa using hp)

private theorem ecc1 : eccentricity witness 1 ≤ 6 := by
  apply Finset.sup_le
  intro v _
  obtain ⟨p,hp⟩ := upWalk parentFrom1_adj 6 v (up1 v)
  exact (witness.dist_le p.reverse).trans (by simpa using hp)

private theorem ecc_other : ∀ v : Vertex, v ≠ 0 → v ≠ 1 → 7 ≤ eccentricity witness v := by
  have hLayer : ∀ v : Vertex, v ≠ 0 → v ≠ 1 → layer v ≤ 4 ∨ 7 ≤ layer v := by decide
  intro v h0 h1
  obtain h | h := hLayer v h0 h1
  · have hd := layer_le_of_dist v 18
    change 11 ≤ layer v + witness.dist v 18 at hd
    have hb := ecc_bounds_dist v 18
    omega
  · have hd := layer_le_of_dist 7 v
    change layer v ≤ 0 + witness.dist 7 v at hd
    rw [witness.dist_comm (u := 7) (v := v)] at hd
    exact h.trans (by simpa using hd) |>.trans (ecc_bounds_dist v 7)

theorem centers_eq : centers witness = {0,1} := by
  ext v
  simp only [mem_centers, mem_insert, mem_singleton]
  constructor
  · intro hc
    by_contra hn
    have h0 : v ≠ 0 := fun h => hn (Or.inl h)
    have h1 : v ≠ 1 := fun h => hn (Or.inr h)
    have hi := ecc_other v h0 h1
    have hl := (hc 0).trans ecc0
    omega
  · rintro (rfl | rfl) w
    · exact ecc0.trans (ecc_ge_six w)
    · exact ecc1.trans (ecc_ge_six w)

private def knownTwo : Finset Vertex :=
  {4,6,9,11,15,17,20,22,26,28,31,33}

set_option maxHeartbeats 7000000 in
private theorem knownTwo_exact : ∀ v : Vertex, witness.degree v = 2 ↔ v ∈ knownTwo := by decide

def knownOpen : Finset Vertex :=
  {3,5,7,10,12,14,16,18,21,23,25,27,29,32,34}

set_option maxHeartbeats 7000000 in
private theorem open_check : ∀ v : Vertex, (∃ w, witness.Adj v w ∧ w ∈ knownTwo) ↔
    v ∈ knownOpen := by decide

theorem openNeighborhood_eq : openTwoNeighborhood witness = knownOpen := by
  ext v
  simp only [openTwoNeighborhood, mem_filter, mem_univ, true_and, knownTwo_exact]
  exact open_check v

set_option maxHeartbeats 5000000 in
private theorem knownOpen_independent :
    ∀ u v : Vertex, u ∈ knownOpen → v ∈ knownOpen → ¬ witness.Adj u v := by decide

private theorem induced_open_bot : witness.induce (knownOpen : Set Vertex) = ⊥ := by
  ext u v
  exact ⟨fun h => (knownOpen_independent u v u.property v.property h).elim,
    fun h => h.elim⟩

private theorem components_bot {W : Type*} :
    componentCount (⊥ : SimpleGraph W) = Nat.card W := by
  symm
  apply Nat.card_congr
  apply Equiv.ofBijective (⊥ : SimpleGraph W).connectedComponentMk
  exact ⟨fun _ _ h => reachable_bot.mp (ConnectedComponent.exact h),
    fun c => c.exists_rep⟩

theorem openNeighborhoodComponents_eq : openNeighborhoodComponents witness = 15 := by
  rw [openNeighborhoodComponents, openNeighborhood_eq, induced_open_bot, components_bot]
  change Nat.card ↥knownOpen = 15
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

def totalSet : Finset Vertex :=
  {0,1,5,6,10,11,16,17,21,22,27,28,32,33}

set_option maxHeartbeats 5000000 in
theorem totalSet_dominates : TotalDominates witness totalSet := by
  unfold TotalDominates
  decide

theorem totalSet_card : totalSet.card = 14 := by decide

private def packing (i : Fin 14) : Vertex :=
  ![0,1,7,8,12,13,18,19,23,24,29,30,34,35] i

set_option maxHeartbeats 7000000 in
/-- Every vertex has at most one neighbor in the packing. -/
private theorem packing_neighbor_unique :
    ∀ v : Vertex, (univ.filter (fun i : Fin 14 => witness.Adj (packing i) v)).card ≤ 1 := by decide

theorem totalDomination_eq : totalDominationNumber witness = 14 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨totalSet, totalSet_dominates,totalSet_card⟩
  · have hn : {k : ℕ | ∃ D, TotalDominates witness D ∧ D.card = k}.Nonempty :=
      ⟨14,totalSet,totalSet_dominates,totalSet_card⟩
    obtain ⟨D,hD,hcard⟩ := Nat.sInf_mem hn
    change 14 ≤ sInf _
    rw [← hcard]
    choose f hf ha using fun i : Fin 14 => hD (packing i)
    let e (i : Fin 14) : D := ⟨f i,hf i⟩
    have he : Function.Injective e := by
      intro i j h
      have heq : f i = f j := congrArg Subtype.val h
      have hi : i ∈ univ.filter (fun k : Fin 14 => witness.Adj (packing k) (f i)) :=
        mem_filter.mpr ⟨mem_univ _,ha i⟩
      have hj : j ∈ univ.filter (fun k : Fin 14 => witness.Adj (packing k) (f i)) :=
        mem_filter.mpr ⟨mem_univ _,heq ▸ ha j⟩
      by_contra hne
      have hl := card_le_card (show {i,j} ⊆ _ from insert_subset hi (singleton_subset_iff.mpr hj))
      rw [card_pair hne] at hl
      exact (by decide : ¬ 2 ≤ 1) (hl.trans (packing_neighbor_unique (f i)))
    simpa using Fintype.card_le_of_injective e he

/-- The doubled inequality is the exact negation of the catalogue lower bound. -/
theorem counterexample354 :
    witness.IsTree ∧ 2 < Fintype.card Vertex ∧
      2 * totalDominationNumber witness <
        (centers witness).card * openNeighborhoodComponents witness := by
  refine ⟨witness_tree, by decide, ?_⟩
  rw [totalDomination_eq, centers_eq, openNeighborhoodComponents_eq]
  decide

theorem counterexample354_rational :
    witness.IsTree ∧ 2 < Fintype.card Vertex ∧
      (totalDominationNumber witness : ℚ) <
        (1 / 2 : ℚ) * ((centers witness).card : ℚ) * (openNeighborhoodComponents witness : ℚ) := by
  refine ⟨witness_tree, by decide, ?_⟩
  rw [totalDomination_eq, centers_eq, openNeighborhoodComponents_eq]
  have h : ({0,1} : Finset Vertex).card = 2 := by decide
  rw [h]
  norm_num

#print axioms witness_tree
#print axioms centers_eq
#print axioms openNeighborhoodComponents_eq
#print axioms totalDomination_eq
#print axioms counterexample354
#print axioms counterexample354_rational

end Graffiti354
