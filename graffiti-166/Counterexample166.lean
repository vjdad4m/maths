import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Sqrt

/-!
# Written on the Wall II, conjecture 166

A connected 20-vertex counterexample: radius 5, fourteen vertices outside
the maximum-degree set adjacent to that set, and at most six leaves in a
spanning tree. The claimed lower bound is 14 / sqrt(5) > 6. An explicit
spanning tree attains six leaves. The radius-zero caveat is independent.

The construction adapts Craig Foster's square gadget from the catalogue
discussion of the distinct neighboring conjecture #165:
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/foster165.jpg
Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti166

open SimpleGraph Finset
open scoped BigOperators
set_option maxRecDepth 4096

section Definitions
variable {W : Type*} [Fintype W]

noncomputable def eccentricity (H : SimpleGraph W) (v : W) : ℕ := univ.sup (H.dist v)

noncomputable def radius (H : SimpleGraph W) : ℕ := sInf (Set.range (eccentricity H))

noncomputable def leaves (T : SimpleGraph W) : Finset W := by
  classical
  exact univ.filter (fun v => ∃! w, T.Adj v w)

noncomputable def maxLeaves (H : SimpleGraph W) : ℕ :=
  sSup {k | ∃ T : SimpleGraph W, T ≤ H ∧ T.IsTree ∧ (leaves T).card = k}

/-- Catalogue definition 46 followed by the set difference in entry 166. -/
def maxDegreeSet (H : SimpleGraph W) [DecidableRel H.Adj] : Finset W :=
  univ.filter (fun v => H.degree v = H.maxDegree)

noncomputable def maxBoundary (H : SimpleGraph W) [DecidableRel H.Adj] : Finset W := by
  classical
  exact univ.filter (fun v => v ∉ maxDegreeSet H ∧ ∃ u ∈ maxDegreeSet H, H.Adj u v)

noncomputable def Claim166 (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  ((maxBoundary H).card : ℝ) / Real.sqrt (radius H) ≤ (maxLeaves H : ℝ)

private theorem dist_le_eccentricity (H : SimpleGraph W) (v w : W) :
    H.dist v w ≤ eccentricity H v :=
  Finset.le_sup (f := H.dist v) (mem_univ w)

private theorem radius_le_eccentricity (H : SimpleGraph W) (v : W) :
    radius H ≤ eccentricity H v := Nat.sInf_le ⟨v, rfl⟩

private theorem radius_lower (H : SimpleGraph W) [Nonempty W] (k : ℕ)
    (h : ∀ v, k ≤ eccentricity H v) : k ≤ radius H := by
  obtain ⟨v, hv⟩ := Nat.sInf_mem (Set.range_nonempty (f := eccentricity H))
  change eccentricity H v = radius H at hv
  exact hv ▸ h v

private theorem leafCounts_bdd (H : SimpleGraph W) :
    BddAbove {k | ∃ T : SimpleGraph W, T ≤ H ∧ T.IsTree ∧ (leaves T).card = k} := by
  refine ⟨Fintype.card W, ?_⟩
  rintro _ ⟨T, _, _, rfl⟩
  exact card_le_univ _

private theorem leaves_mem (T : SimpleGraph W) [DecidableRel T.Adj] (v : W) :
    v ∈ leaves T ↔ T.degree v = 1 := by
  classical
  simp only [leaves, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, hn⟩
    have h : T.neighborFinset v = {w} := by
      ext z
      simp only [T.mem_neighborFinset, mem_singleton]
      exact ⟨hn z, fun he => he ▸ hw⟩
    rw [← T.card_neighborFinset_eq_degree, h, card_singleton]
  · intro hd
    obtain ⟨w, hw⟩ := card_eq_one.mp hd
    refine ⟨w, (T.mem_neighborFinset v w).1 (hw.symm ▸ mem_singleton_self _), ?_⟩
    intro z hz
    exact mem_singleton.mp (hw ▸ (T.mem_neighborFinset v z).2 hz)

end Definitions

section DistanceCertificate
variable {W : Type*} (H : SimpleGraph W) (label : W → W → ℕ)
variable (diag : ∀ r, label r r = 0)
variable (step : ∀ r u v, H.Adj u v → label r v ≤ label r u + 1)
variable (descent : ∀ r v, v ≠ r → ∃ w, H.Adj v w ∧ label r w + 1 = label r v)

include label descent in
private theorem reachable_from_descent (r v : W) : H.Reachable v r := by
  generalize he : label r v = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v = r
    · subst v
      exact ⟨.nil⟩
    · obtain ⟨w, hw, hstep⟩ := descent r v hv
      exact hw.reachable.trans (ih _ (by omega) w rfl)

include label descent in
private theorem certificate_connected [Nonempty W] : H.Connected := by
  obtain ⟨r⟩ := ‹Nonempty W›
  apply (connected_iff_exists_forall_reachable _).mpr
  exact ⟨r, fun v => (reachable_from_descent H label descent r v).symm⟩

include step in
private theorem label_le_length (r : W) {v w : W} (p : H.Walk v w) :
    label r w ≤ label r v + p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
    have hs := step r _ _ h
    simp only [Walk.length_cons]
    omega

include diag step descent in
theorem dist_eq_certificate [Nonempty W] (r v : W) : H.dist r v = label r v := by
  have hc := certificate_connected H label descent
  apply le_antisymm
  · generalize he : label r v = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = r
      · subst v
        rw [SimpleGraph.dist_self]
        exact Nat.zero_le _
      · obtain ⟨w, hw, hstep⟩ := descent r v hv
        have hl := ih (label r w) (by omega) w rfl
        have ht := hc.dist_triangle (u := r) (v := w) (w := v)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hw.symm] at ht
        omega
  · obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist r v
    simpa [hp, diag] using label_le_length H label step r p

end DistanceCertificate

abbrev V := Fin 20

/-- Two squares, vertices 0–3 and 4–7, and two junctions, 8 and 9.
The five connections outside the squares have length three. -/
def edges : List (V × V) :=
  [(0,2),(0,3),(1,2),(1,3), (4,6),(4,7),(5,6),(5,7),
   (0,14),(14,15),(8,15), (1,12),(12,13),(9,13),
   (4,10),(10,11),(9,11), (5,16),(16,17),(8,17),
   (8,18),(18,19),(9,19)]

def G : SimpleGraph V where
  Adj u v := (u,v) ∈ edges ∨ (v,u) ∈ edges
  symm _ _ := Or.symm
  loopless := by
    intro v h
    have h' : ∀ v : V, (v,v) ∉ edges := by decide +kernel
    exact h' v (h.elim id id)

instance : DecidableRel G.Adj := fun u v =>
  inferInstanceAs (Decidable ((u,v) ∈ edges ∨ (v,u) ∈ edges))

def maxVertices : Finset V := {0,1,4,5,8,9}

def degreeG (v : V) : ℕ := if v ∈ maxVertices then 3 else 2

private theorem degree_G (v : V) : G.degree v = degreeG v := by
  fin_cases v <;> decide +kernel

theorem maxDegree_G : G.maxDegree = 3 := by
  apply le_antisymm
  · apply G.maxDegree_le_of_forall_degree_le
    intro v
    rw [degree_G]
    exact (show ∀ w : V, degreeG w ≤ 3 by decide +kernel) v
  · exact (show 3 ≤ G.degree (0 : V) by decide +kernel).trans (G.degree_le_maxDegree 0)

theorem maxDegreeSet_eq : maxDegreeSet G = maxVertices := by
  ext v
  simp only [maxDegreeSet, mem_filter, mem_univ, true_and, maxDegree_G, degree_G]
  exact (show ∀ w : V, degreeG w = 3 ↔ w ∈ maxVertices by decide +kernel) v

theorem boundary_eq : maxBoundary G = univ \ maxVertices := by
  ext v
  simp only [maxBoundary, mem_filter, mem_univ, true_and, maxDegreeSet_eq, mem_sdiff]
  have h : ∀ v : V, v ∉ maxVertices → ∃ u ∈ maxVertices, G.Adj u v := by decide +kernel
  exact ⟨And.left, fun hv => ⟨hv,h v hv⟩⟩

theorem boundary_card : (maxBoundary G).card = 14 := by
  rw [boundary_eq]
  decide +kernel

def matrix : Array (Array ℕ) := #[
  #[0, 2, 1, 1, 8, 6, 7, 7, 3, 5, 7, 6, 3, 4, 1, 2, 5, 4, 4, 5],
  #[2, 0, 1, 1, 6, 8, 7, 7, 5, 3, 5, 4, 1, 2, 3, 4, 7, 6, 5, 4],
  #[1, 1, 0, 2, 7, 7, 8, 8, 4, 4, 6, 5, 2, 3, 2, 3, 6, 5, 5, 5],
  #[1, 1, 2, 0, 7, 7, 8, 8, 4, 4, 6, 5, 2, 3, 2, 3, 6, 5, 5, 5],
  #[8, 6, 7, 7, 0, 2, 1, 1, 5, 3, 1, 2, 5, 4, 7, 6, 3, 4, 5, 4],
  #[6, 8, 7, 7, 2, 0, 1, 1, 3, 5, 3, 4, 7, 6, 5, 4, 1, 2, 4, 5],
  #[7, 7, 8, 8, 1, 1, 0, 2, 4, 4, 2, 3, 6, 5, 6, 5, 2, 3, 5, 5],
  #[7, 7, 8, 8, 1, 1, 2, 0, 4, 4, 2, 3, 6, 5, 6, 5, 2, 3, 5, 5],
  #[3, 5, 4, 4, 5, 3, 4, 4, 0, 3, 5, 4, 5, 4, 2, 1, 2, 1, 1, 2],
  #[5, 3, 4, 4, 3, 5, 4, 4, 3, 0, 2, 1, 2, 1, 5, 4, 5, 4, 2, 1],
  #[7, 5, 6, 6, 1, 3, 2, 2, 5, 2, 0, 1, 4, 3, 7, 6, 4, 5, 4, 3],
  #[6, 4, 5, 5, 2, 4, 3, 3, 4, 1, 1, 0, 3, 2, 6, 5, 5, 5, 3, 2],
  #[3, 1, 2, 2, 5, 7, 6, 6, 5, 2, 4, 3, 0, 1, 4, 5, 7, 6, 4, 3],
  #[4, 2, 3, 3, 4, 6, 5, 5, 4, 1, 3, 2, 1, 0, 5, 5, 6, 5, 3, 2],
  #[1, 3, 2, 2, 7, 5, 6, 6, 2, 5, 7, 6, 4, 5, 0, 1, 4, 3, 3, 4],
  #[2, 4, 3, 3, 6, 4, 5, 5, 1, 4, 6, 5, 5, 5, 1, 0, 3, 2, 2, 3],
  #[5, 7, 6, 6, 3, 1, 2, 2, 2, 5, 4, 5, 7, 6, 4, 3, 0, 1, 3, 4],
  #[4, 6, 5, 5, 4, 2, 3, 3, 1, 4, 5, 5, 6, 5, 3, 2, 1, 0, 2, 3],
  #[4, 5, 5, 5, 5, 4, 5, 5, 1, 2, 4, 3, 4, 3, 3, 2, 3, 2, 0, 1],
  #[5, 4, 5, 5, 4, 5, 5, 5, 2, 1, 3, 2, 3, 2, 4, 3, 4, 3, 1, 0]
]
-- The first vertex of eccentricity 5 is 8.
def label (v w : V) : ℕ := (matrix[v.val]?.getD #[])[w.val]?.getD 0
def labelEcc (v : V) : ℕ := univ.sup (label v)

private theorem diag : ∀ v : V, label v v = 0 := by decide +kernel

set_option maxHeartbeats 10000000 in
private theorem step : ∀ r u v, G.Adj u v → label r v ≤ label r u + 1 := by
  decide +kernel

set_option maxHeartbeats 10000000 in
private theorem descent : ∀ r v, v ≠ r → ∃ w, G.Adj v w ∧ label r w + 1 = label r v := by
  decide +kernel

theorem G_connected : G.Connected := certificate_connected G label descent

private theorem ecc_eq (v : V) : eccentricity G v = labelEcc v := by
  unfold eccentricity labelEcc
  congr 1
  funext w
  exact dist_eq_certificate G label diag step descent v w

theorem radius_G : radius G = 5 := by
  apply le_antisymm
  · have h : ∃ v : V, labelEcc v ≤ 5 := by decide +kernel
    obtain ⟨v, hv⟩ := h
    have hh := radius_le_eccentricity G v
    rw [ecc_eq] at hh
    exact hh.trans hv
  · apply radius_lower
    intro v
    rw [ecc_eq]
    exact (show ∀ w : V, 5 ≤ labelEcc w by decide +kernel) v


private theorem connected_has_neighbor {T : SimpleGraph V} (hc : T.Connected) (v : V) :
    ∃ w, T.Adj v w := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by decide : 1 < Fintype.card V) v
  obtain ⟨p⟩ := hc v w
  cases p with
  | nil => exact (hw rfl).elim
  | cons ha _ => exact ⟨_, ha⟩

private theorem retained_at_degree_three {T : SimpleGraph V} [DecidableRel T.Adj]
    (hsub : T ≤ G) {v w : V} (ht : T.degree v = 3) (h : G.Adj v w) :
    T.Adj v w := by
  have hn : T.neighborFinset v ⊆ G.neighborFinset v := by
    intro u hu
    exact (G.mem_neighborFinset v u).mpr (hsub ((T.mem_neighborFinset v u).mp hu))
  have he : T.neighborFinset v = G.neighborFinset v := by
    apply eq_of_subset_of_card_le hn
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, ht]
    simpa [maxDegree_G] using G.degree_le_maxDegree v
  apply (T.mem_neighborFinset v w).mp
  rw [he]
  exact (G.mem_neighborFinset v w).mpr h

private theorem square_forces_loss {T : SimpleGraph V} [DecidableRel T.Adj]
    (hsub : T ≤ G) (ht : T.IsTree) {a b x y : V}
    (hab : a ≠ b) (hxy : x ≠ y)
    (hax : G.Adj a x) (hbx : G.Adj b x) (hay : G.Adj a y) (hby : G.Adj b y) :
    ¬ (T.degree a = 3 ∧ T.degree b = 3) := by
  rintro ⟨da, db⟩
  have ax := retained_at_degree_three hsub da hax
  have bx := retained_at_degree_three hsub db hbx
  have ay := retained_at_degree_three hsub da hay
  have by' := retained_at_degree_three hsub db hby
  let p : T.Walk a b := .cons ax (.cons bx.symm .nil)
  let q : T.Walk a b := .cons ay (.cons by'.symm .nil)
  have hp : p.IsPath := (Walk.IsPath.of_adj bx.symm).cons (by simp [ax.ne, hab])
  have hq : q.IsPath := (Walk.IsPath.of_adj by'.symm).cons (by simp [ay.ne, hab])
  have eq : (⟨p,hp⟩ : T.Path a b) = ⟨q,hq⟩ := ht.IsAcyclic.path_unique _ _
  have eq' := congrArg (fun t : T.Path a b => t.val.getVert 1) eq
  exact hxy (by simpa [p,q] using eq')

private theorem tree_leaf_count_eq_degree_three (T : SimpleGraph V) [DecidableRel T.Adj]
    (ht : T.IsTree) (hdeg : ∀ v, T.degree v ≤ 3) :
    (leaves T).card = (univ.filter (fun v => T.degree v = 3)).card + 2 := by
  classical
  let D : Finset V := univ.filter (fun v => T.degree v = 3)
  have eq_point (v : V) :
      T.degree v + (if v ∈ leaves T then 1 else 0) = 2 + (if v ∈ D then 1 else 0) := by
    have hpos := (T.degree_pos_iff_exists_adj v).mpr (connected_has_neighbor ht.isConnected v)
    have hle := hdeg v
    simp only [D, leaves_mem, mem_filter, mem_univ, true_and]
    split <;> split <;> omega
  have heq := Finset.sum_congr (rfl : (univ : Finset V) = univ) (fun v _ => eq_point v)
  have ind (s : Finset V) : (∑ v : V, if v ∈ s then (1 : ℕ) else 0) = s.card := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ind, ind,
    T.sum_degrees_eq_twice_card_edges] at heq
  have hconstant : (∑ _v : V, (2 : ℕ)) = 40 := by simp
  rw [hconstant] at heq
  have hcard := ht.card_edgeFinset
  rw [Fintype.card_fin] at hcard
  change (leaves T).card = D.card + 2
  omega

/-- In each square, at least one of its two degree-three ports loses a tree edge. -/
theorem every_spanningTree_at_most_six_leaves (T : SimpleGraph V)
    (hsub : T ≤ G) (ht : T.IsTree) : (leaves T).card ≤ 6 := by
  classical
  have hupper (v : V) : T.degree v ≤ 3 :=
    (T.degree_le_of_le hsub).trans (maxDegree_G ▸ G.degree_le_maxDegree v)
  have hl := tree_leaf_count_eq_degree_three T ht hupper
  let D : Finset V := univ.filter (fun v => T.degree v = 3)
  have hd (v : V) : v ∈ D ↔ T.degree v = 3 := by simp [D]
  have left := square_forces_loss hsub ht (a := 0) (b := 1) (x := 2) (y := 3)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have right := square_forces_loss hsub ht (a := 4) (b := 5) (x := 6) (y := 7)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hexL : ∃ a ∈ ({0,1} : Finset V), a ∉ D := by
    by_cases h : (0 : V) ∈ D
    · exact ⟨1, by simp, fun h' => left ⟨(hd _).mp h,(hd _).mp h'⟩⟩
    · exact ⟨0, by simp, h⟩
  have hexR : ∃ b ∈ ({4,5} : Finset V), b ∉ D := by
    by_cases h : (4 : V) ∈ D
    · exact ⟨5, by simp, fun h' => right ⟨(hd _).mp h,(hd _).mp h'⟩⟩
    · exact ⟨4, by simp, h⟩
  obtain ⟨a, ha, hDa⟩ := hexL
  obtain ⟨b, hb, hDb⟩ := hexR
  have hData : ∀ a b : V, a ∈ ({0,1} : Finset V) → b ∈ ({4,5} : Finset V) →
      a ≠ b ∧ a ∈ maxVertices ∧ b ∈ maxVertices := by decide +kernel
  obtain ⟨hab, haM, hbM⟩ := hData a b ha hb
  have hsubD : D ⊆ (maxVertices \ {a,b}) := by
    intro v hv
    apply mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · have hTd := (hd v).mp hv
      have hGd : G.degree v = 3 := by
        have lo := T.degree_le_of_le (v := v) hsub
        have hi := G.degree_le_maxDegree v
        rw [maxDegree_G] at hi
        omega
      rw [← maxDegreeSet_eq]
      simpa [maxDegreeSet, maxDegree_G] using hGd
    · intro hm
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with rfl | rfl
      · exact hDa hv
      · exact hDb hv
  have hmcount : maxVertices.card = 6 := by decide +kernel
  have hsubAB : ({a,b} : Finset V) ⊆ maxVertices := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact haM
    · exact hbM
  have hAB : ({a,b} : Finset V).card = 2 := by simp [hab]
  have hcap := card_le_card hsubD
  rw [card_sdiff hsubAB, hmcount, hAB] at hcap
  change (leaves T).card = D.card + 2 at hl
  omega

def removedEdges : List (V × V) := [(1,3),(5,7),(12,13),(16,17)]

def treeEdges : List (V × V) := edges.filter (fun e => decide (e ∉ removedEdges))

def T0 : SimpleGraph V where
  Adj u v := (u,v) ∈ treeEdges ∨ (v,u) ∈ treeEdges
  symm _ _ := Or.symm
  loopless := by
    intro v h
    have h' : ∀ v : V, (v,v) ∉ treeEdges := by decide +kernel
    exact h' v (h.elim id id)

instance : DecidableRel T0.Adj := fun u v =>
  inferInstanceAs (Decidable ((u,v) ∈ treeEdges ∨ (v,u) ∈ treeEdges))

private theorem T0_le : T0 ≤ G := by
  have h : ∀ v w, T0.Adj v w → G.Adj v w := by decide +kernel
  exact h

def treeLevel (v : V) : ℕ := (#[3, 5, 4, 4, 6, 8, 7, 7, 0, 3, 5, 4, 6, 4, 2, 1, 9, 1, 1, 2] : Array ℕ)[v.val]?.getD 0
def treeDegree (v : V) : ℕ := (#[3, 2, 2, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2] : Array ℕ)[v.val]?.getD 0

private theorem T0_connected : T0.Connected := by
  have step : ∀ v : V, v ≠ 8 → ∃ u, T0.Adj v u ∧ treeLevel u + 1 = treeLevel v :=
    by decide +kernel
  have hr (v : V) : T0.Reachable v 8 := by
    generalize e : treeLevel v = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = 8
      · subst v
        exact ⟨.nil⟩
      · obtain ⟨u, hu, hs⟩ := step v hv
        exact hu.reachable.trans (ih _ (by omega) u rfl)
  exact (connected_iff_exists_forall_reachable _).mpr ⟨8, fun v => (hr v).symm⟩

private theorem degree_T0 (v : V) : T0.degree v = treeDegree v := by
  fin_cases v <;> decide +kernel

private theorem T0_tree : T0.IsTree := by
  have hs := T0.sum_degrees_eq_twice_card_edges
  have hg : (∑ v, T0.degree v) = 38 := by
    simp only [degree_T0]
    decide +kernel
  rw [hg] at hs
  apply isTree_iff_connected_and_card.mpr
  refine ⟨T0_connected, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, Fintype.card_fin]
  omega

private theorem T0_six : (leaves T0).card = 6 := by
  have h : leaves T0 = {3,7,12,13,16,17} := by
    ext v
    rw [leaves_mem, degree_T0]
    exact (show ∀ v : V, treeDegree v = 1 ↔
      v ∈ ({3,7,12,13,16,17} : Finset V) by decide +kernel) v
  rw [h]
  decide +kernel

theorem maxLeaves_G : maxLeaves G = 6 := by
  have hfit : 6 ∈ {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ (leaves T).card = k} :=
    ⟨T0, T0_le, T0_tree, T0_six⟩
  apply le_antisymm
  · apply csSup_le ⟨6, hfit⟩
    rintro _ ⟨T, hsub, ht, rfl⟩
    exact every_spanningTree_at_most_six_leaves T hsub ht
  · exact le_csSup (leafCounts_bdd G) hfit

theorem nontrivial_counterexample :
    G.Connected ∧ radius G = 5 ∧ (maxBoundary G).card = 14 ∧
      maxLeaves G = 6 ∧ ¬ Claim166 G := by
  refine ⟨G_connected, radius_G, boundary_card, maxLeaves_G, ?_⟩
  unfold Claim166
  rw [radius_G, boundary_card, maxLeaves_G]
  norm_cast
  intro h
  have hs : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hm := (div_le_iff₀ hs).mp h
  have hsquare := mul_le_mul hm hm (by norm_num) (mul_nonneg (by norm_num) hs.le)
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

/-- The boundary is empty when a connected graph has radius zero. The resulting 0/0
is undefined as an ordinary real quotient. Lean totalizes it to zero. -/
theorem radius_zero_totalized {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hc : H.Connected) (hr : radius H = 0) :
    (maxBoundary H).card = 0 ∧ Claim166 H := by
  classical
  haveI := hc.nonempty
  obtain ⟨r, h⟩ := Nat.sInf_mem (Set.range_nonempty (f := eccentricity H))
  change eccentricity H r = radius H at h
  rw [hr] at h
  have he (v : W) : r = v := by
    have hd := dist_le_eccentricity H r v
    rw [h] at hd
    exact hc.dist_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hd)
  have hno (u v : W) : ¬ H.Adj u v := fun hadj => hadj.ne ((he u).symm.trans (he v))
  have hem : maxBoundary H = ∅ := by
    ext v
    simp [maxBoundary, hno]
  have hc' : (maxBoundary H).card = 0 := by simp [hem]
  refine ⟨hc', ?_⟩
  simp [Claim166, hc']

#print axioms nontrivial_counterexample
#print axioms radius_zero_totalized

end Graffiti166
