import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.FinCases

/-!
# Written on the Wall II, Conjecture 154

The statement is false, even outside the singleton convention. A full binary
tree of depth three has eight terminals. Attach a private pendant to each
terminal. Join terminal 7 to each other terminal by its own two-edge path.
The radius is four; the largest and smallest center spheres have orders
15 and 1, and the maximum leaf count of a spanning tree is 15, not 16.

For the leaf upper bound, a spanning tree omits seven edges. If k added
two-edge-path vertices are leaves, they account for k distinct omissions.
If f vertices in the first three binary-tree levels are leaves, they use
at least 2f - 1 omitted incidences and hence f + k ≤ 7. The eight
terminals cannot be leaves because each has a forced pendant edge.
The eight pendant leaves then give at most 15 in total, attained by
retaining the binary tree, pendant edges, and one edge per connector.

The formalization uses the center's radius-distance sphere, not an
arbitrary BFS layer. This is different from the spectral conjecture
numbered 154 in the original Written on the Wall.

Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Definitions: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json
Checked with Lean 4.19.0 / Mathlib v4.19.0. No priority or minimality claimed.
-/

namespace Graffiti154

open SimpleGraph Finset
open scoped BigOperators
set_option maxRecDepth 4096

section Definitions
variable {W : Type*} [Fintype W]

noncomputable def eccentricity (H : SimpleGraph W) (v : W) : ℕ := univ.sup (H.dist v)

noncomputable def radius (H : SimpleGraph W) : ℕ := sInf (Set.range (eccentricity H))

def IsCenter (H : SimpleGraph W) (v : W) : Prop := eccentricity H v = radius H

/-- The radius-distance sphere, used as a radial circle only at a center. -/
noncomputable def circle (H : SimpleGraph W) (v : W) : Finset W := by
  classical
  exact univ.filter (fun w => H.dist v w = radius H)

noncomputable def largestCircle (H : SimpleGraph W) : ℕ :=
  sSup {(circle H v).card | v ∈ {v | IsCenter H v}}

noncomputable def smallestCircle (H : SimpleGraph W) : ℕ :=
  sInf {(circle H v).card | v ∈ {v | IsCenter H v}}

noncomputable def leaves (T : SimpleGraph W) : Finset W := by
  classical
  exact univ.filter (fun v => ∃! w, T.Adj v w)

noncomputable def maxLeaves (H : SimpleGraph W) : ℕ :=
  sSup {k | ∃ T : SimpleGraph W, T ≤ H ∧ T.IsTree ∧ (leaves T).card = k}

/-- Cross-multiplication of the catalogue ratio when the smallest circle is nonempty. -/
def Claim154 (H : SimpleGraph W) : Prop :=
  1 + largestCircle H ≤ maxLeaves H * smallestCircle H

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

private theorem circleCounts_bdd (H : SimpleGraph W) :
    BddAbove {(circle H v).card | v ∈ {v | IsCenter H v}} := by
  refine ⟨Fintype.card W, ?_⟩
  rintro _ ⟨v, _, rfl⟩
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

abbrev V := Fin 30

/-- Edges listed from smaller label to larger label. -/
def edge (x y : V) : Prop :=
  x.val < y.val ∧
    ((y.val < 15 ∧ x.val = (y.val-1)/2) ∨
     (15 ≤ y.val ∧ y.val < 23 ∧ x.val = y.val-8) ∨
     (23 ≤ y.val ∧ (x.val = 7 ∨ x.val = y.val-15)))

instance (x y : V) : Decidable (edge x y) := by unfold edge; infer_instance

def G : SimpleGraph V where
  Adj x y := edge x y ∨ edge y x
  symm _ _ := Or.symm
  loopless := fun _ h => (h.elim And.left And.left).false

instance : DecidableRel G.Adj := fun x y =>
  inferInstanceAs (Decidable (edge x y ∨ edge y x))

def parent (v : V) : V :=
  if v.val < 15 then ⟨(v.val-1)/2, by omega⟩
  else if v.val < 23 then ⟨v.val-8, by omega⟩ else 7

def T0 : SimpleGraph V where
  Adj v w := (v ≠ 0 ∧ parent v = w) ∨ (w ≠ 0 ∧ parent w = v)
  symm _ _ := Or.symm
  loopless := by
    intro v hv
    have h : ∀ v : V, ¬(v ≠ 0 ∧ parent v = v) := by decide +kernel
    exact h v (hv.elim id id)

instance : DecidableRel T0.Adj := fun x y =>
  inferInstanceAs (Decidable ((x ≠ 0 ∧ parent x = y) ∨ (y ≠ 0 ∧ parent y = x)))

private theorem T0_le : T0 ≤ G := by
  have h : ∀ v w, T0.Adj v w → G.Adj v w := by decide +kernel
  exact h

private theorem T0_connected : T0.Connected := by
  have step : ∀ v : V, v ≠ 0 → (parent v).val < v.val ∧ T0.Adj v (parent v) := by
    decide +kernel
  have hr (v : V) : T0.Reachable v 0 := by
    generalize e : v.val = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = 0
      · subst v
        exact ⟨.nil⟩
      · obtain ⟨hl, ha⟩ := step v hv
        exact ha.reachable.trans (ih _ (e ▸ hl) _ rfl)
  exact (connected_iff_exists_forall_reachable _).mpr ⟨0, fun v => (hr v).symm⟩

theorem G_connected : G.Connected := T0_connected.mono T0_le

/-- A certificate for the distances. The following lemmas check it against the graph. -/
def labels : Array (Array ℕ) := #[
  #[0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
  #[1, 0, 2, 1, 1, 3, 3, 2, 2, 2, 2, 4, 4, 4, 4, 3, 3, 3, 3, 5, 5, 5, 5, 3, 3, 3, 3, 3, 3, 3],
  #[1, 2, 0, 3, 3, 1, 1, 4, 4, 4, 4, 2, 2, 2, 2, 5, 5, 5, 5, 3, 3, 3, 3, 5, 5, 5, 3, 3, 3, 3],
  #[2, 1, 3, 0, 2, 4, 4, 1, 1, 3, 3, 3, 3, 3, 3, 2, 2, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2],
  #[2, 1, 3, 2, 0, 4, 4, 3, 3, 1, 1, 5, 5, 5, 5, 4, 4, 2, 2, 6, 6, 6, 6, 4, 2, 2, 4, 4, 4, 4],
  #[2, 3, 1, 4, 4, 0, 2, 3, 5, 5, 5, 1, 1, 3, 3, 4, 6, 6, 6, 2, 2, 4, 4, 4, 4, 4, 2, 2, 4, 4],
  #[2, 3, 1, 4, 4, 2, 0, 3, 5, 5, 5, 3, 3, 1, 1, 4, 6, 6, 6, 4, 4, 2, 2, 4, 4, 4, 4, 4, 2, 2],
  #[3, 2, 4, 1, 3, 3, 3, 0, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1],
  #[3, 2, 4, 1, 3, 5, 5, 2, 0, 4, 4, 4, 4, 4, 4, 3, 1, 5, 5, 5, 5, 5, 5, 1, 3, 3, 3, 3, 3, 3],
  #[3, 2, 4, 3, 1, 5, 5, 2, 4, 0, 2, 4, 4, 4, 4, 3, 5, 1, 3, 5, 5, 5, 5, 3, 1, 3, 3, 3, 3, 3],
  #[3, 2, 4, 3, 1, 5, 5, 2, 4, 2, 0, 4, 4, 4, 4, 3, 5, 3, 1, 5, 5, 5, 5, 3, 3, 1, 3, 3, 3, 3],
  #[3, 4, 2, 3, 5, 1, 3, 2, 4, 4, 4, 0, 2, 4, 4, 3, 5, 5, 5, 1, 3, 5, 5, 3, 3, 3, 1, 3, 3, 3],
  #[3, 4, 2, 3, 5, 1, 3, 2, 4, 4, 4, 2, 0, 4, 4, 3, 5, 5, 5, 3, 1, 5, 5, 3, 3, 3, 3, 1, 3, 3],
  #[3, 4, 2, 3, 5, 3, 1, 2, 4, 4, 4, 4, 4, 0, 2, 3, 5, 5, 5, 5, 5, 1, 3, 3, 3, 3, 3, 3, 1, 3],
  #[3, 4, 2, 3, 5, 3, 1, 2, 4, 4, 4, 4, 4, 2, 0, 3, 5, 5, 5, 5, 5, 3, 1, 3, 3, 3, 3, 3, 3, 1],
  #[4, 3, 5, 2, 4, 4, 4, 1, 3, 3, 3, 3, 3, 3, 3, 0, 4, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2],
  #[4, 3, 5, 2, 4, 6, 6, 3, 1, 5, 5, 5, 5, 5, 5, 4, 0, 6, 6, 6, 6, 6, 6, 2, 4, 4, 4, 4, 4, 4],
  #[4, 3, 5, 4, 2, 6, 6, 3, 5, 1, 3, 5, 5, 5, 5, 4, 6, 0, 4, 6, 6, 6, 6, 4, 2, 4, 4, 4, 4, 4],
  #[4, 3, 5, 4, 2, 6, 6, 3, 5, 3, 1, 5, 5, 5, 5, 4, 6, 4, 0, 6, 6, 6, 6, 4, 4, 2, 4, 4, 4, 4],
  #[4, 5, 3, 4, 6, 2, 4, 3, 5, 5, 5, 1, 3, 5, 5, 4, 6, 6, 6, 0, 4, 6, 6, 4, 4, 4, 2, 4, 4, 4],
  #[4, 5, 3, 4, 6, 2, 4, 3, 5, 5, 5, 3, 1, 5, 5, 4, 6, 6, 6, 4, 0, 6, 6, 4, 4, 4, 4, 2, 4, 4],
  #[4, 5, 3, 4, 6, 4, 2, 3, 5, 5, 5, 5, 5, 1, 3, 4, 6, 6, 6, 6, 6, 0, 4, 4, 4, 4, 4, 4, 2, 4],
  #[4, 5, 3, 4, 6, 4, 2, 3, 5, 5, 5, 5, 5, 3, 1, 4, 6, 6, 6, 6, 6, 4, 0, 4, 4, 4, 4, 4, 4, 2],
  #[4, 3, 5, 2, 4, 4, 4, 1, 1, 3, 3, 3, 3, 3, 3, 2, 2, 4, 4, 4, 4, 4, 4, 0, 2, 2, 2, 2, 2, 2],
  #[4, 3, 5, 2, 2, 4, 4, 1, 3, 1, 3, 3, 3, 3, 3, 2, 4, 2, 4, 4, 4, 4, 4, 2, 0, 2, 2, 2, 2, 2],
  #[4, 3, 5, 2, 2, 4, 4, 1, 3, 3, 1, 3, 3, 3, 3, 2, 4, 4, 2, 4, 4, 4, 4, 2, 2, 0, 2, 2, 2, 2],
  #[4, 3, 3, 2, 4, 2, 4, 1, 3, 3, 3, 1, 3, 3, 3, 2, 4, 4, 4, 2, 4, 4, 4, 2, 2, 2, 0, 2, 2, 2],
  #[4, 3, 3, 2, 4, 2, 4, 1, 3, 3, 3, 3, 1, 3, 3, 2, 4, 4, 4, 4, 2, 4, 4, 2, 2, 2, 2, 0, 2, 2],
  #[4, 3, 3, 2, 4, 4, 2, 1, 3, 3, 3, 3, 3, 1, 3, 2, 4, 4, 4, 4, 4, 2, 4, 2, 2, 2, 2, 2, 0, 2],
  #[4, 3, 3, 2, 4, 4, 2, 1, 3, 3, 3, 3, 3, 3, 1, 2, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 0]
]

def label (r v : V) : ℕ := (labels[r.val]?.getD #[])[v.val]?.getD 0

set_option maxHeartbeats 10000000 in
private theorem label_step (r u v : V) (h : G.Adj u v) :
    label r v ≤ label r u + 1 := by
  have h' : ∀ r u v, G.Adj u v → label r v ≤ label r u + 1 := by decide +kernel
  exact h' r u v h

set_option maxHeartbeats 10000000 in
private theorem label_descent : ∀ r v : V, v ≠ r →
    ∃ w : V, G.Adj v w ∧ label r w + 1 = label r v := by
  decide +kernel

private theorem label_zero (r : V) : label r r = 0 := by
  have h : ∀ r, label r r = 0 := by decide +kernel
  exact h r

private theorem label_le_length (r : V) {v w : V} (p : G.Walk v w) :
    label r w ≤ label r v + p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
    have hs := label_step r _ _ h
    simp only [Walk.length_cons]
    omega

theorem dist_eq_label (r v : V) : G.dist r v = label r v := by
  apply le_antisymm
  · generalize he : label r v = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = r
      · subst v
        rw [SimpleGraph.dist_self]
        exact Nat.zero_le _
      · obtain ⟨w, hw, hstep⟩ := label_descent r v hv
        have hl := ih (label r w) (by omega) w rfl
        have ht := G_connected.dist_triangle (u := r) (v := w) (w := v)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hw.symm] at ht
        omega
  · obtain ⟨p, hp⟩ := G_connected.exists_walk_length_eq_dist r v
    simpa [hp, label_zero] using label_le_length r p

def labelEcc (r : V) : ℕ := univ.sup (label r)

private theorem ecc_eq_labelEcc (r : V) : eccentricity G r = labelEcc r := by
  unfold eccentricity labelEcc
  congr 1
  funext v
  exact dist_eq_label r v

theorem radius_eq : radius G = 4 := by
  apply le_antisymm
  · have h := radius_le_eccentricity G 0
    rw [ecc_eq_labelEcc] at h
    exact h.trans (by decide +kernel : labelEcc 0 ≤ 4)
  · apply radius_lower
    intro v
    rw [ecc_eq_labelEcc]
    have h : ∀ v, 4 ≤ labelEcc v := by decide +kernel
    exact h v

def labelCircle (v : V) : Finset V := univ.filter (fun w => label v w = 4)

private theorem circle_eq (v : V) : circle G v = labelCircle v := by
  classical
  ext w
  simp [circle, labelCircle, dist_eq_label, radius_eq]

private theorem center0 : IsCenter G 0 := by
  unfold IsCenter
  rw [ecc_eq_labelEcc, radius_eq]
  decide +kernel

private theorem center7 : IsCenter G 7 := by
  unfold IsCenter
  rw [ecc_eq_labelEcc, radius_eq]
  decide +kernel

theorem largestCircle_eq : largestCircle G = 15 := by
  have h0 : (circle G 0).card = 15 := by rw [circle_eq]; decide +kernel
  have hfit : 15 ∈ {(circle G v).card | v ∈ {v | IsCenter G v}} := ⟨0, center0, h0⟩
  apply le_antisymm
  · apply csSup_le ⟨15, hfit⟩
    rintro _ ⟨v, hv, rfl⟩
    have h : ∀ v, labelEcc v = 4 → (labelCircle v).card ≤ 15 := by decide +kernel
    rw [circle_eq]
    apply h
    change eccentricity G v = radius G at hv
    simpa only [ecc_eq_labelEcc, radius_eq] using hv
  · exact le_csSup (circleCounts_bdd G) hfit

theorem smallestCircle_eq : smallestCircle G = 1 := by
  have h7 : (circle G 7).card = 1 := by rw [circle_eq]; decide +kernel
  have hfit : 1 ∈ {(circle G v).card | v ∈ {v | IsCenter G v}} := ⟨7, center7, h7⟩
  apply le_antisymm (Nat.sInf_le hfit)
  obtain ⟨v, hv, he⟩ := Nat.sInf_mem (s := {(circle G v).card | v ∈ {v | IsCenter G v}})
    ⟨1, hfit⟩
  change (circle G v).card = smallestCircle G at he
  change 1 ≤ smallestCircle G
  rw [← he, circle_eq]
  have h : ∀ v, labelEcc v = 4 → 1 ≤ (labelCircle v).card := by decide +kernel
  apply h
  change eccentricity G v = radius G at hv
  simpa only [ecc_eq_labelEcc, radius_eq] using hv


def gDegree (v : V) : ℕ :=
  if v = 0 then 2 else if v = 7 then 9 else if v.val < 15 then 3
  else if v.val < 23 then 1 else 2

def t0Degree (v : V) : ℕ :=
  if v = 0 then 2 else if v = 7 then 9 else if v.val < 7 then 3
  else if v.val < 15 then 2 else 1

private theorem degree_G (v : V) : G.degree v = gDegree v := by
  fin_cases v <;> decide +kernel

private theorem degree_T0 (v : V) : T0.degree v = t0Degree v := by
  fin_cases v <;> decide +kernel

theorem edgeCount_G : G.edgeFinset.card = 36 := by
  have hs := G.sum_degrees_eq_twice_card_edges
  have hg : (∑ v, G.degree v) = 72 := by
    simp only [degree_G]
    decide +kernel
  rw [hg] at hs
  omega

private theorem T0_tree : T0.IsTree := by
  have hs := T0.sum_degrees_eq_twice_card_edges
  have hg : (∑ v, T0.degree v) = 58 := by
    simp only [degree_T0]
    decide +kernel
  rw [hg] at hs
  apply isTree_iff_connected_and_card.mpr
  refine ⟨T0_connected, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, Fintype.card_fin]
  omega

def pendantVertices : Finset V := univ.filter (fun v => 15 ≤ v.val ∧ v.val < 23)

private theorem T0_leaf_count : (leaves T0).card = 15 := by
  have h : leaves T0 = univ.filter (fun v => 15 ≤ v.val) := by
    ext v
    rw [leaves_mem, degree_T0]
    have hh : ∀ v : V, t0Degree v = 1 ↔ 15 ≤ v.val := by decide +kernel
    simpa using hh v
  rw [h]
  decide +kernel

private theorem degree_one_neighbor {T : SimpleGraph V} [DecidableRel T.Adj]
    {v x y : V} (h : T.degree v = 1) (hx : T.Adj v x) (hy : T.Adj v y) : x = y := by
  obtain ⟨z, hz⟩ := card_eq_one.mp h
  have hx' := (T.mem_neighborFinset v x).2 hx
  have hy' := (T.mem_neighborFinset v y).2 hy
  rw [hz] at hx' hy'
  exact (mem_singleton.mp hx').trans (mem_singleton.mp hy').symm

def pendant (v : V) : V := ⟨(v.val + 8) % 30, Nat.mod_lt _ (by decide)⟩

private theorem connected_has_neighbor {T : SimpleGraph V} (hc : T.Connected) (v : V) :
    ∃ w, T.Adj v w := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by decide : 1 < Fintype.card V) v
  obtain ⟨p⟩ := hc v w
  cases p with
  | nil => exact (hw rfl).elim
  | cons h _ => exact ⟨_, h⟩

private theorem closed_along_walk {T : SimpleGraph V} {P : V → Prop}
    (step : ∀ x y, P x → T.Adj x y → P y) {u v : V} (p : T.Walk u v) (hu : P u) : P v := by
  induction p with
  | nil => exact hu
  | cons h _ ih => exact ih (step _ _ hu h)

private theorem support_not_leaf {T : SimpleGraph V} [DecidableRel T.Adj]
    (hsub : T ≤ G) (hc : T.Connected) {v : V} (hv : 7 ≤ v.val ∧ v.val < 15) :
    T.degree v ≠ 1 := by
  intro hleaf
  have hdata : ∀ v : V, 7 ≤ v.val ∧ v.val < 15 →
      v ≠ 0 ∧ pendant v ≠ 0 ∧ ∀ w : V, G.Adj (pendant v) w → w = v := by decide +kernel
  obtain ⟨v0, p0, hp⟩ := hdata v hv
  obtain ⟨x, hx⟩ := connected_has_neighbor hc (pendant v)
  have hvp : T.Adj (pendant v) v := hp x (hsub hx) ▸ hx
  have hstep (a b : V) (ha : a = v ∨ a = pendant v) (hab : T.Adj a b) :
      b = v ∨ b = pendant v := by
    rcases ha with rfl | ha
    · exact Or.inr (degree_one_neighbor hleaf hab hvp.symm)
    · exact Or.inl (hp b (hsub (ha ▸ hab)))
  obtain ⟨p⟩ := hc v 0
  rcases closed_along_walk hstep p (Or.inl rfl) with e | e
  · exact v0 e.symm
  · exact p0 e.symm

private theorem connector_neighbors (x y : V) (hx : 23 ≤ x.val) (hxy : G.Adj x y) :
    7 ≤ y.val ∧ y.val < 15 := by
  have h : ∀ x y : V, 23 ≤ x.val → G.Adj x y → 7 ≤ y.val ∧ y.val < 15 :=
    by decide +kernel
  exact h x y hx hxy

/-- Every spanning tree has at most the fifteen leaves of the radial circle at 0. -/
theorem spanning_tree_leaf_upper (T : SimpleGraph V) (hsub : T ≤ G) (ht : T.IsTree) :
    (leaves T).card ≤ 15 := by
  classical
  let D := G \ T
  let H : SimpleGraph V :=
    { Adj := fun v w => D.Adj v w ∧ (v.val < 7 ∨ w.val < 7)
      symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
      loopless := fun _ h => D.loopless _ h.1 }
  let F := (leaves T).filter (fun v => v.val < 7)
  let K := (leaves T).filter (fun v => 23 ≤ v.val)
  have hD : D.edgeFinset.card = 7 := by
    have hTcount := ht.card_edgeFinset
    rw [Fintype.card_fin] at hTcount
    change (G \ T).edgeFinset.card = 7
    rw [edgeFinset_sdiff, card_sdiff (edgeFinset_mono hsub), edgeCount_G]
    omega
  have hdeg (v : V) : D.degree v + T.degree v = G.degree v := by
    have he : D.neighborFinset v = G.neighborFinset v \ T.neighborFinset v := by
      ext w
      simp [D, sdiff_adj]
    simp only [← card_neighborFinset_eq_degree, he]
    apply card_sdiff_add_card_eq_card
    intro w hw
    exact (G.mem_neighborFinset v w).2 (hsub ((T.mem_neighborFinset v w).1 hw))
  have hlocal (v : V) (hv : v.val < 7) : H.degree v = D.degree v := by
    have he : H.neighborFinset v = D.neighborFinset v := by
      ext w
      rw [H.mem_neighborFinset, D.mem_neighborFinset]
      change (D.Adj v w ∧ (v.val < 7 ∨ w.val < 7)) ↔ D.Adj v w
      simp [hv]
    simp only [← card_neighborFinset_eq_degree, he]
  have hmissing (v : V) (hv : v ∈ K) : ∃ w, D.Adj v w := by
    have hl := Finset.mem_filter.mp hv
    have htdeg := (leaves_mem T v).1 hl.1
    have hg := degree_G v
    have hv0 : v ≠ 0 := by
      intro e
      have h : (0 : V).val = v.val := congrArg Fin.val e.symm
      simp at h
      omega
    have hv7 : v ≠ 7 := by
      intro e
      have h : (7 : V).val = v.val := congrArg Fin.val e.symm
      simp at h
      omega
    simp [gDegree, hv0, hv7, show ¬v.val < 15 by omega,
      show ¬v.val < 23 by omega] at hg
    apply (D.degree_pos_iff_exists_adj v).1
    have he := hdeg v
    omega
  let f (v : V) : V := if h : v ∈ K then (hmissing v h).choose else v
  have hf (v : V) (hv : v ∈ K) : D.Adj v (f v) := by
    simpa [f, hv] using (hmissing v hv).choose_spec
  have hHsub : H.edgeFinset ⊆ D.edgeFinset := edgeFinset_mono (fun _ _ h => h.1)
  have hK : K.card ≤ (D.edgeFinset \ H.edgeFinset).card := by
    apply card_le_card_of_injOn (fun v => s(v, f v))
    · intro v hv
      have hv23 := (mem_filter.mp hv).2
      have hff := hf v hv
      have hfin := connector_neighbors v (f v) hv23 hff.1
      apply mem_sdiff.mpr
      refine ⟨(mem_edgeFinset).2 (D.mem_edgeSet.2 hff), ?_⟩
      intro he
      have ha : H.Adj v (f v) := H.mem_edgeSet.1 ((mem_edgeFinset).1 he)
      have hlt : v.val < 7 ∨ (f v).val < 7 := ha.2
      omega
    · intro u hu v hv huv
      rcases Sym2.eq_iff.mp huv with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · have hu23 := (mem_filter.mp hu).2
        have hv23 := (mem_filter.mp hv).2
        have hfv := connector_neighbors v (f v) hv23 (hf v hv).1
        have he := congrArg Fin.val h
        omega
  have hbudget : H.edgeFinset.card + K.card ≤ 7 := by
    have he := card_sdiff_add_card_eq_card hHsub
    omega
  have hpoint : ∀ v ∈ F, 2 ≤ H.degree v + (if v = 0 then 1 else 0) := by
    intro v hv
    obtain ⟨hvL, hvI⟩ := mem_filter.mp hv
    have hTdeg := (leaves_mem T v).1 hvL
    have he := hdeg v
    rw [← hlocal v hvI, hTdeg, degree_G] at he
    by_cases h0 : v = 0
    · simp [gDegree, h0] at he ⊢
      omega
    · have h7 : v ≠ 7 := by
        intro e
        have h := congrArg Fin.val e
        simp at h
        omega
      simp [gDegree, h0, h7, hvI.trans (by decide : 7 < 15)] at he ⊢
      omega
  have hFs : 2 * F.card ≤ (∑ v ∈ F, H.degree v) + 1 := by
    have e := Finset.sum_le_sum hpoint
    have hconstant : (∑ _v ∈ F, (2 : ℕ)) = 2 * F.card := by simp [Nat.mul_comm]
    rw [hconstant, Finset.sum_add_distrib] at e
    have e₁ : (∑ v ∈ F, if v = 0 then (1 : ℕ) else 0) ≤ 1 := by
      rw [Finset.sum_ite_eq']
      split <;> omega
    omega
  have htot := H.sum_degrees_eq_twice_card_edges
  have hfs' : (∑ v ∈ F, H.degree v) ≤ ∑ v, H.degree v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ F)
  have hFK : F.card + K.card ≤ 7 := by omega
  have hcover : leaves T ⊆ F ∪ K ∪ pendantVertices := by
    intro v hv
    by_cases hI : v.val < 7
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hv, hI⟩))
    by_cases hC : 23 ≤ v.val
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hv, hC⟩))
    by_cases hP : 15 ≤ v.val
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hP, by omega⟩)
    · exact (support_not_leaf hsub ht.isConnected (by omega) ((leaves_mem T v).1 hv)).elim
  have hPcard : pendantVertices.card = 8 := by decide +kernel
  have hcard := card_le_card hcover
  have hu₁ := card_union_le F K
  have hu₂ := card_union_le (F ∪ K) pendantVertices
  omega

theorem maxLeaves_eq : maxLeaves G = 15 := by
  have hfit : 15 ∈ {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ (leaves T).card = k} :=
    ⟨T0, T0_le, T0_tree, T0_leaf_count⟩
  apply le_antisymm
  · apply csSup_le ⟨15, hfit⟩
    rintro _ ⟨T, hsub, ht, rfl⟩
    exact spanning_tree_leaf_upper T hsub ht
  · exact le_csSup (leafCounts_bdd G) hfit

/-- A counterexample of positive radius with 30 vertices, under the catalogue definitions. -/
theorem nontrivial_counterexample :
    G.Connected ∧ radius G = 4 ∧ largestCircle G = 15 ∧ smallestCircle G = 1 ∧
      maxLeaves G = 15 ∧ ¬ Claim154 G := by
  refine ⟨G_connected, radius_eq, largestCircle_eq, smallestCircle_eq, maxLeaves_eq, ?_⟩
  simp [Claim154, largestCircle_eq, smallestCircle_eq, maxLeaves_eq]

/-- The one-vertex case under the degree-one leaf convention. -/
theorem singleton_values {W : Type*} [Fintype W] [Subsingleton W] [Nonempty W]
    (H : SimpleGraph W) : radius H = 0 ∧ largestCircle H = 1 ∧ smallestCircle H = 1 ∧
      maxLeaves H = 0 := by
  classical
  obtain ⟨r⟩ := ‹Nonempty W›
  have hd (u v : W) : H.dist u v = 0 := by
    rw [Subsingleton.elim u v, SimpleGraph.dist_self]
  have he (v : W) : eccentricity H v = 0 := by
    apply Nat.eq_zero_of_le_zero
    unfold eccentricity
    apply Finset.sup_le
    intro w _
    exact (hd v w).le
  have hr : radius H = 0 :=
    Nat.eq_zero_of_le_zero ((radius_le_eccentricity H r).trans (he r).le)
  have heq (v : W) : circle H v = univ := by
    ext w
    simp [circle, hr, hd]
  have hn : Fintype.card W = 1 := Fintype.card_eq_one_iff.2 ⟨r, fun _ => Subsingleton.elim _ _⟩
  have count (v : W) : (circle H v).card = 1 := by rw [heq, card_univ, hn]
  have hset : {(circle H v).card | v ∈ {v | IsCenter H v}} = ({1} : Set ℕ) := by
    ext n
    constructor
    · rintro ⟨v, _, rfl⟩
      exact Set.mem_singleton_iff.2 (count v)
    · intro hn'
      have hn'' := Set.mem_singleton_iff.1 hn'
      exact ⟨r, (he r).trans hr.symm, (count r).trans hn''.symm⟩
  refine ⟨hr, ?_, ?_, ?_⟩
  · rw [largestCircle, hset, csSup_singleton]
  · rw [smallestCircle, hset, csInf_singleton]
  have hNoAdj (T : SimpleGraph W) (v w : W) : ¬ T.Adj v w :=
    fun h => h.ne (Subsingleton.elim _ _)
  have hEmpty (T : SimpleGraph W) : leaves T = ∅ := by
    ext v
    simp [leaves, hNoAdj]
  have hb : H = ⊥ := by
    ext u v
    simp [hNoAdj]
  have hc : H.Connected := by
    refine ⟨?_⟩
    intro u v
    rw [Subsingleton.elim u v]
  have ht : H.IsTree := ⟨hc, hb.symm ▸ SimpleGraph.isAcyclic_bot⟩
  have hfit : 0 ∈ {k | ∃ T : SimpleGraph W, T ≤ H ∧ T.IsTree ∧ (leaves T).card = k} :=
    ⟨H, le_rfl, ht, by simp [hEmpty]⟩
  apply Nat.eq_zero_of_le_zero
  apply csSup_le ⟨0, hfit⟩
  rintro _ ⟨T, _, _, rfl⟩
  simp [hEmpty]

/-- The singleton fails both with its degree-one leaf count and with a convention that
counts the sole vertex as one leaf. The thirty-vertex witness uses neither convention. -/
theorem singleton_both_conventions {W : Type*} [Fintype W] [Subsingleton W] [Nonempty W]
    (H : SimpleGraph W) :
    ¬ Claim154 H ∧ ¬ (1 + largestCircle H ≤ 1 * smallestCircle H) := by
  obtain ⟨_, hM, hm, hL⟩ := singleton_values H
  simp [Claim154, hM, hm, hL]

#print axioms nontrivial_counterexample
#print axioms singleton_both_conventions

end Graffiti154
