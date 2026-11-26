import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Rat.Floor
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.NormNum

/-!
# Written on the Wall II, conjecture 267

A 19-vertex, girth-five graph has total domination number 5, while the
mean positive distance from the minimum-degree set is 46/9, with ceiling 6.
This certificate independently gives a different witness from the prior
AI Village disproof credited to Claude Opus 5, reported August 24, 2026:
https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-conj267-false-one-hundred-sixty-seven

Use disprove267_finite_girth for the original claim, independent of any
convention for acyclic graphs. The separate tree example applies only to
the convention that acyclic graphs have infinite girth.

Official catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti267

open Finset SimpleGraph
open scoped BigOperators

def IsTotalDominating {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w, w ∈ D ∧ G.Adj v w

noncomputable def totalDominationNumber {V : Type*} (G : SimpleGraph V)
    (_ : ∃ D, IsTotalDominating G D) : ℕ :=
  sInf {k | ∃ D, IsTotalDominating G D ∧ D.card = k}

def minimumDegreeVertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree v ≤ G.degree w

/-- Definition 95, with all positive distances from minimum-degree sources. -/
noncomputable def minimumDegreePairs {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset (V × V) := by
  classical
  exact univ.filter fun p => p.1 ∈ minimumDegreeVertices G ∧ 0 < G.dist p.1 p.2

noncomputable def minimumDegreeMean {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℚ :=
  (↑(∑ p ∈ minimumDegreePairs G, G.dist p.1 p.2) : ℚ) / ↑(minimumDegreePairs G).card

/-- This formulation includes a graph with no cycles under infinite girth. -/
def GirthAtLeastFive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length

/-- This formulation requires an actual (finite) girth. -/
def FiniteGirthAtLeastFive {V : Type*} (G : SimpleGraph V) : Prop :=
  (∃ (v : V) (p : G.Walk v v), p.IsCycle) ∧ GirthAtLeastFive G

def Conjecture267 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → GirthAtLeastFive G →
    ∀ h : ∃ D, IsTotalDominating G D,
      ⌈minimumDegreeMean G⌉ ≤ (totalDominationNumber G h : ℤ)

def Conjecture267FiniteGirth : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → FiniteGirthAtLeastFive G →
    ∀ h : ∃ D, IsTotalDominating G D,
      ⌈minimumDegreeMean G⌉ ≤ (totalDominationNumber G h : ℤ)

abbrev Vertex := Fin 19

/-- The ends 1 and 2 have one length-two branch via 0 and six length-three
branches. A length-four path runs from 0 to the leaf 6. -/
private def edges : List (Vertex × Vertex) :=
  [(0,1), (0,2), (0,3), (3,4), (4,5), (5,6),
   (1,7), (7,8), (8,2), (1,9), (9,10), (10,2),
   (1,11), (11,12), (12,2), (1,13), (13,14), (14,2),
   (1,15), (15,16), (16,2), (1,17), (17,18), (18,2)]

private def edge (u v : Vertex) : Prop := (u,v) ∈ edges ∨ (v,u) ∈ edges

private instance : DecidableRel edge := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

def graph : SimpleGraph Vertex where
  Adj := edge
  symm := fun _ _ h => h.symm
  loopless := by
    change ∀ u, ¬edge u u
    decide

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel edge)

def dominatingSet : Finset Vertex := {0, 1, 2, 4, 5}

theorem dominatingSet_total : IsTotalDominating graph dominatingSet := by
  unfold IsTotalDominating
  decide

theorem totalDomination_exists : ∃ D, IsTotalDominating graph D :=
  ⟨dominatingSet, dominatingSet_total⟩

theorem total_domination_le_five :
    totalDominationNumber graph totalDomination_exists ≤ 5 := by
  exact Nat.sInf_le ⟨dominatingSet, dominatingSet_total, by decide⟩

private def leftBranchVertices : Finset Vertex := {7, 9, 11, 13, 15}

private def rightBranchVertices : Finset Vertex := {8, 10, 12, 14, 16}

private theorem forced_support (D : Finset Vertex) (hD : IsTotalDominating graph D)
    (small : D.card < 5) (u : Vertex) (S : Finset Vertex) (size : S.card = 5)
    (branches : ∀ v ∈ S, ∃ a, ∀ w, graph.Adj a w → w = u ∨ w = v) : u ∈ D := by
  by_contra hu
  have hsub : S ⊆ D := by
    intro v hv
    obtain ⟨a, ha⟩ := branches v hv
    obtain ⟨w, hw, haw⟩ := hD a
    exact (ha w haw).elim (fun he => (hu (he ▸ hw)).elim) (fun he => he ▸ hw)
  have hc := card_le_card hsub
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem total_domination_eq_five :
    totalDominationNumber graph totalDomination_exists = 5 := by
  apply le_antisymm total_domination_le_five
  change 5 ≤ sInf {k : ℕ | ∃ D, IsTotalDominating graph D ∧ D.card = k}
  have hnon : {k : ℕ | ∃ D, IsTotalDominating graph D ∧ D.card = k}.Nonempty :=
    ⟨5, dominatingSet, dominatingSet_total, by decide⟩
  obtain ⟨D, hD, hc⟩ := Nat.sInf_mem hnon
  rw [← hc]
  by_contra! small
  have hleft : (1 : Vertex) ∈ D :=
    forced_support D hD small 1 rightBranchVertices (by decide) (by decide)
  have hright : (2 : Vertex) ∈ D :=
    forced_support D hD small 2 leftBranchVertices (by decide) (by decide)
  obtain ⟨w, hw, h6w⟩ := hD 6
  have hw5 : w = 5 := (show ∀ v, graph.Adj 6 v → v = 5 by decide) w h6w
  have h5 : (5 : Vertex) ∈ D := hw5 ▸ hw
  obtain ⟨d, hd, h5d⟩ := hD 5
  have ht : d = 4 ∨ d = 6 :=
    (show ∀ v, graph.Adj 5 v → v = 4 ∨ v = 6 by decide) d h5d
  let firstFour : Finset Vertex := {1, 2, 5, d}
  have hfour : firstFour.card = 4 := by
    rcases ht with rfl | rfl <;> decide
  obtain ⟨z, hz, h1z⟩ := hD 1
  have hz' : z ∉ firstFour := by
    rcases ht with rfl | rfl
    · exact (show ∀ v, graph.Adj 1 v → v ∉ ({1, 2, 5, 4} : Finset Vertex) by decide) z h1z
    · exact (show ∀ v, graph.Adj 1 v → v ∉ ({1, 2, 5, 6} : Finset Vertex) by decide) z h1z
  have hsub : insert z firstFour ⊆ D := by
    intro v hv
    simp only [firstFour, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcard := card_le_card hsub
  rw [card_insert_of_not_mem hz', hfour] at hcard
  omega

/- The common-neighbor lemmas adapt the generic no-short-cycle checks in
graff252-codex/Counterexample253.lean. -/
private def common {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : Finset V :=
  univ.filter fun w => G.Adj u w ∧ G.Adj v w

private theorem mem_common {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w : V) : w ∈ common G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [common]

private theorem no_four_cycle {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : ∀ u v, u ≠ v → (common G u v).card ≤ 1) :
    (∀ v (w : G.Walk v v), w.IsCycle → w.length ≠ 4) := by
  intro v w hc hw
  have he : w.getVert 4 = w.getVert 0 := by
    rw [← hw, w.getVert_length, w.getVert_zero]
  have h02 : w.getVert 0 ≠ w.getVert 2 := by
    intro heq
    have heq' := hc.getVert_injOn' (by simp [hw]) (by simp [hw]) heq
    omega
  have h13 : w.getVert 1 ≠ w.getVert 3 := by
    intro heq
    have heq' := hc.getVert_injOn' (by simp [hw]) (by simp [hw]) heq
    omega
  have a := w.adj_getVert_succ (i := 0) (by omega)
  have b := w.adj_getVert_succ (i := 1) (by omega)
  have c := w.adj_getVert_succ (i := 2) (by omega)
  have d := w.adj_getVert_succ (i := 3) (by omega)
  change G.Adj (w.getVert 3) (w.getVert 4) at d
  rw [he] at d
  have v1 := (mem_common G _ _ _).mpr ⟨a, b.symm⟩
  have v3 := (mem_common G _ _ _).mpr ⟨d.symm, c⟩
  exact h13 (Finset.card_le_one.mp (h _ _ h02) _ v1 _ v3)

private theorem no_three_cycle {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : ∀ u v, G.Adj u v → (common G u v).card = 0) :
    ∀ v (w : G.Walk v v), w.IsCycle → w.length ≠ 3 := by
  intro v w _ hw
  have he : w.getVert 3 = w.getVert 0 := by
    rw [← hw, w.getVert_length, w.getVert_zero]
  have a := w.adj_getVert_succ (i := 0) (by omega)
  have b := w.adj_getVert_succ (i := 1) (by omega)
  have c := w.adj_getVert_succ (i := 2) (by omega)
  change G.Adj (w.getVert 2) (w.getVert 3) at c
  rw [he] at c
  have hv := (mem_common G _ _ _).mpr ⟨c.symm, b⟩
  rw [Finset.card_eq_zero.mp (h _ _ a)] at hv
  simp at hv


set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem girth_at_least_five : GirthAtLeastFive graph := by
  have h₃ : ∀ v (p : graph.Walk v v), p.IsCycle → p.length ≠ 3 := by
    apply no_three_cycle
    decide
  have h₄ : ∀ v (p : graph.Walk v v), p.IsCycle → p.length ≠ 4 := by
    apply no_four_cycle
    decide
  intro v p hp
  have hlow := hp.three_le_length
  have h3 := h₃ v p hp
  have h4 := h₄ v p hp
  omega

private def cycle : graph.Walk 0 0 :=
  .cons (show graph.Adj 0 1 by decide)
    (.cons (show graph.Adj 1 7 by decide)
      (.cons (show graph.Adj 7 8 by decide)
        (.cons (show graph.Adj 8 2 by decide)
          (.cons (show graph.Adj 2 0 by decide) .nil))))

theorem has_girth_five : GirthAtLeastFive graph ∧
    ∃ (v : Vertex) (p : graph.Walk v v), p.IsCycle ∧ p.length = 5 := by
  refine ⟨girth_at_least_five, 0, cycle, (Walk.isCycle_def _).mpr ⟨?_, ?_, ?_⟩, by decide⟩
  · rw [Walk.isTrail_def]
    decide
  · simp [cycle]
  · decide

/-- A certificate for the distances from the tail leaf. -/
private def level (v : Vertex) : ℕ :=
  #[4,5,5,3,2,1,0,6,6,6,6,6,6,6,6,6,6,6,6][v.val]!

private theorem level_step : ∀ u v, graph.Adj u v → level v ≤ level u + 1 := by
  decide

private theorem level_parent :
    ∀ v : Vertex, v ≠ 6 → ∃ w : Vertex, graph.Adj w v ∧ level w + 1 = level v := by
  decide

/-- Edge differences give a lower bound on distance. Parents with label one
smaller supply walks attaining the bound and also certify connectivity. -/
private theorem certified_distances {V : Type*} {G : SimpleGraph V} (r : V) (label : V → ℕ)
    (root_zero : label r = 0)
    (step : ∀ u v, G.Adj u v → label v ≤ label u + 1)
    (parent : ∀ v, v ≠ r → ∃ w, G.Adj w v ∧ label w + 1 = label v) :
    G.Connected ∧ ∀ v, G.dist r v = label v := by
  have routes (v : V) : ∃ p : G.Walk r v, p.length = label v := by
    generalize h : label v = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = r
      · subst v
        exact ⟨.nil, by simpa [root_zero] using h⟩
      · obtain ⟨w, hAdj, hw⟩ := parent v hv
        obtain ⟨p, hp⟩ := ih (label w) (by omega) w rfl
        exact ⟨p.append hAdj.toWalk, by simpa [Adj.toWalk, hp] using hw.trans h⟩
  have hconn : G.Connected := (connected_iff_exists_forall_reachable G).mpr
    ⟨r, fun v => by obtain ⟨p, _⟩ := routes v; exact p.reachable⟩
  have label_bound {u v : V} (p : G.Walk u v) : label v ≤ label u + p.length := by
    induction p with
    | nil => simp
    | @cons a b c h p ih =>
      have hs := step a b h
      simp only [Walk.length_cons]
      omega
  refine ⟨hconn, fun v => ?_⟩
  obtain ⟨p, hp⟩ := routes v
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist r v
  have hl := G.dist_le p
  have hr := label_bound q
  omega

theorem connected : graph.Connected :=
  (certified_distances 6 level (by decide) level_step level_parent).1

private theorem dist_eq_level (v : Vertex) : graph.dist 6 v = level v :=
  (certified_distances 6 level (by decide) level_step level_parent).2 v

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem unique_minimum_degree : minimumDegreeVertices graph = {6} := by
  decide

private theorem pairs_eq :
    minimumDegreePairs graph = (univ.erase (6 : Vertex)).image (fun v => (6,v)) := by
  classical
  ext ⟨u, v⟩
  simp only [minimumDegreePairs, mem_filter, mem_univ, true_and, unique_minimum_degree,
    mem_singleton, mem_image, mem_erase, and_true, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, hpos⟩
    have hne : v ≠ 6 := by
      intro h
      subst v
      simp [dist_self] at hpos
    exact ⟨v, hne, rfl, rfl⟩
  · rintro ⟨w, hne, rfl, rfl⟩
    exact ⟨rfl, connected.pos_dist_of_ne (Ne.symm hne)⟩

private theorem left_fixed_injective : Function.Injective (fun v : Vertex => ((6 : Vertex), v)) :=
  fun _ _ h => congrArg Prod.snd h

theorem exact_sum_and_count :
    (∑ p ∈ minimumDegreePairs graph, graph.dist p.1 p.2) = 92 ∧
      (minimumDegreePairs graph).card = 18 := by
  rw [pairs_eq, card_image_of_injective _ left_fixed_injective]
  rw [sum_image (fun _ _ _ _ h => left_fixed_injective h)]
  change (∑ v ∈ univ.erase (6 : Vertex), graph.dist 6 v) = 92 ∧
    (univ.erase (6 : Vertex)).card = 18
  simp only [dist_eq_level]
  decide

theorem mean_eq : minimumDegreeMean graph = (46 / 9 : ℚ) := by
  rw [minimumDegreeMean, exact_sum_and_count.1, exact_sum_and_count.2]
  norm_num

theorem ceil_mean_eq_six : ⌈minimumDegreeMean graph⌉ = 6 := by
  rw [mean_eq, Int.ceil_eq_iff]
  norm_num

theorem counterexample :
    (totalDominationNumber graph totalDomination_exists : ℤ) < ⌈minimumDegreeMean graph⌉ := by
  rw [ceil_mean_eq_six, total_domination_eq_five]
  decide

theorem disprove267 : ¬ Conjecture267 := by
  intro h
  exact (not_le_of_gt counterexample) (h Vertex graph connected girth_at_least_five
    totalDomination_exists)

theorem disprove267_finite_girth : ¬ Conjecture267FiniteGirth := by
  intro h
  obtain ⟨hl, v, p, hp, _⟩ := has_girth_five
  exact (not_le_of_gt counterexample) (h Vertex graph connected ⟨⟨v, p, hp⟩, hl⟩
    totalDomination_exists)

namespace TreeConvention

abbrev Vertex := Fin 5

private def treeEdges : List (Vertex × Vertex) := [(0,1), (0,2), (0,3), (3,4)]

private def treeEdge (u v : Vertex) : Prop := (u,v) ∈ treeEdges ∨ (v,u) ∈ treeEdges

private instance : DecidableRel treeEdge := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def graph : SimpleGraph Vertex where
  Adj := treeEdge
  symm := fun _ _ h => h.symm
  loopless := by
    change ∀ u, ¬ treeEdge u u
    decide

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel treeEdge)

private def label (u v : Vertex) : ℕ :=
  let row : Array ℕ := #[#[0,1,1,1,2], #[1,0,2,2,3], #[1,2,0,2,3], #[1,2,2,0,1],
    #[2,3,3,1,0]][u.val]!
  row[v.val]!

private theorem label_zero : ∀ u : Vertex, label u u = 0 := by decide

private theorem label_step :
    ∀ r u v : Vertex, graph.Adj u v → label r v ≤ label r u + 1 := by decide

private theorem label_parent : ∀ r v : Vertex,
    v ≠ r → ∃ w : Vertex, graph.Adj w v ∧ label r w + 1 = label r v := by decide

private theorem distance_cert (r : Vertex) : graph.Connected ∧
    ∀ v, graph.dist r v = label r v :=
  certified_distances r (label r) (label_zero r) (label_step r) (label_parent r)

theorem is_tree : graph.IsTree := by
  rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card, ← edgeFinset_card,
    Nat.card_eq_fintype_card]
  exact ⟨(distance_cert 0).1, by decide⟩

private def leaves : Finset Vertex := {1, 2, 4}

private theorem minimum_degree : minimumDegreeVertices graph = leaves := by decide

private def pairs : Finset (Vertex × Vertex) :=
  univ.filter fun p => p.1 ∈ leaves ∧ 0 < label p.1 p.2

private theorem pairs_eq : minimumDegreePairs graph = pairs := by
  classical
  ext p
  simp [minimumDegreePairs, minimum_degree, pairs, (distance_cert p.1).2 p.2]

theorem exact_sum_and_count :
    (∑ p ∈ minimumDegreePairs graph, graph.dist p.1 p.2) = 25 ∧
      (minimumDegreePairs graph).card = 12 := by
  rw [pairs_eq]
  have hdist (p : Vertex × Vertex) : graph.dist p.1 p.2 = label p.1 p.2 :=
    (distance_cert p.1).2 p.2
  simp only [hdist]
  decide

private def domSet : Finset Vertex := {0,3}

private theorem domSet_total : IsTotalDominating graph domSet := by
  unfold IsTotalDominating
  decide

theorem totalDomination_exists : ∃ D, IsTotalDominating graph D := ⟨domSet, domSet_total⟩

theorem counterexample : GirthAtLeastFive graph ∧
    (totalDominationNumber graph totalDomination_exists : ℤ) < ⌈minimumDegreeMean graph⌉ := by
  refine ⟨fun _ p hp => (is_tree.IsAcyclic p hp).elim, ?_⟩
  have htd : totalDominationNumber graph totalDomination_exists ≤ 2 :=
    Nat.sInf_le ⟨domSet, domSet_total, by decide⟩
  have hceil : ⌈minimumDegreeMean graph⌉ = 3 := by
    rw [minimumDegreeMean, exact_sum_and_count.1, exact_sum_and_count.2, Int.ceil_eq_iff]
    norm_num
  rw [hceil]
  omega

end TreeConvention

#print axioms has_girth_five
#print axioms exact_sum_and_count
#print axioms total_domination_eq_five
#print axioms disprove267
#print axioms disprove267_finite_girth
#print axioms TreeConvention.counterexample

end Graffiti267
