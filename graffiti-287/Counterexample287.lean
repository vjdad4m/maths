import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Lattice

/-!
A standalone certificate for the 45-vertex member of Claude Opus 5's
previously published spider counterexample family to Written on the Wall II #287.
The witness gives 30 > 6 + 22, or 30 > 7 + 22 with the other row indexing.

Prior work: Claude Opus 5 / AI Village, section 8a and tip 2562.
Attribution audit: https://grok-ai-village-news-496089.gitlab.io/articles/opus5-standing-retraction-174-to-171-reannounce-audit
Original verifier: ai-village-agents/village/graffiti-verification, verify/verify_conj287.py.
Official catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti287

open Finset SimpleGraph

def IsTotalDominating {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

noncomputable def totalDominationNumber {V : Type*} (G : SimpleGraph V)
    (_ : ∃ D, IsTotalDominating G D) : ℕ :=
  sInf {k | ∃ D, IsTotalDominating G D ∧ D.card = k}

/-- The indexed endpoints are all distinct, so the k edges are disjoint. -/
def HasMatching {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ endpoints : Fin k × Bool → V, Function.Injective endpoints ∧
    ∀ i, G.Adj (endpoints (i, false)) (endpoints (i, true))

noncomputable def matchingNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {k | HasMatching G k}

theorem exists_total_domination_of_connected {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (hn : 1 < Fintype.card V) : ∃ D, IsTotalDominating G D := by
  refine ⟨univ, fun v => ?_⟩
  obtain ⟨w, hne⟩ := Fintype.exists_ne_of_one_lt_card hn v
  obtain ⟨p⟩ := hc.preconnected v w
  exact ⟨p.snd, mem_univ _, p.adj_snd (Walk.not_nil_of_ne hne.symm)⟩

private theorem matching_le_half {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : HasMatching G k) : k ≤ Fintype.card V / 2 := by
  obtain ⟨f, hf, _⟩ := h
  have hb := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hb
  omega

private theorem matching_bounded {V : Type*} [Fintype V] (G : SimpleGraph V) :
    BddAbove {k : ℕ | HasMatching G k} :=
  ⟨Fintype.card V / 2, fun _ h => matching_le_half h⟩

private theorem matching_nonempty {V : Type*} (G : SimpleGraph V) :
    {k : ℕ | HasMatching G k}.Nonempty := by
  refine ⟨0, fun x => x.1.elim0, ?_, ?_⟩
  · intro x
    exact x.1.elim0
  · intro i
    exact i.elim0

/-- Non-increasing order. -/
private def sortList (s : List ℕ) : List ℕ := List.insertionSort (· ≥ ·) s

/-- A multiset has a unique non-increasing listing. The quotient construction
does not depend on any choice of vertex ordering. -/
private def sortMultiset (s : Multiset ℕ) : List ℕ :=
  Quot.liftOn s sortList (fun l₁ l₂ h =>
    List.eq_of_perm_of_sorted
      ((List.perm_insertionSort _ _).trans (h.trans (List.perm_insertionSort _ _).symm))
      (List.sorted_insertionSort (· ≥ ·) l₁) (List.sorted_insertionSort (· ≥ ·) l₂))

def degreeSequence {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : List ℕ :=
  sortMultiset ((univ : Finset V).val.map (fun v => G.degree v))

/-- A step deletes the largest entry of an already sorted row, decrements
the next entries, and sorts the remainder. -/
def hhStep : List ℕ → List ℕ
  | [] => []
  | d :: rest => sortList ((rest.take d).map (· - 1) ++ rest.drop d)

/-- Row 0 is the initial sequence. Row k follows exactly k reductions. -/
def hhRow (s : List ℕ) : ℕ → List ℕ
  | 0 => s
  | k + 1 => hhStep (hhRow s k)

def FirstZero (s : List ℕ) (k : ℕ) : Prop :=
  0 ∈ hhRow s k ∧ ∀ j < k, 0 ∉ hhRow s j

def Conjecture287 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : 2 < Fintype.card V) (k : ℕ),
    FirstZero (degreeSequence G) k →
    totalDominationNumber G (exists_total_domination_of_connected hc (by omega)) ≤
      k + matchingNumber Gᶜ

private theorem sort_replicate (n d : ℕ) : sortList (List.replicate n d) = List.replicate n d := by
  unfold sortList
  apply List.eq_of_perm_of_sorted (List.perm_insertionSort _ _) (List.sorted_insertionSort _ _)
  change List.Pairwise (fun a b : ℕ => b ≤ a) (List.replicate n d)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.pairwise_cons]
    exact ⟨fun x hx => by simp [List.eq_of_mem_replicate hx], ih⟩

private theorem sort_constant_map {V : Type*} (s : Multiset V) (d : ℕ) :
    sortMultiset (s.map (fun _ => d)) = List.replicate s.card d := by
  induction s using Quot.inductionOn with
  | _ l =>
    change sortList (l.map (fun _ => d)) = List.replicate l.length d
    rw [List.map_const', sort_replicate]

theorem complete_degree_sequence {V : Type*} [Fintype V] [DecidableEq V] :
    degreeSequence (⊤ : SimpleGraph V) =
      List.replicate (Fintype.card V) (Fintype.card V - 1) := by
  unfold degreeSequence
  simp only [complete_graph_degree, sort_constant_map, ← Finset.card_def, card_univ]

private theorem hhStep_uniform (m : ℕ) :
    hhStep (List.replicate (m+1) m) = List.replicate m (m-1) := by
  rw [List.replicate_succ, hhStep]
  have hlength : (List.replicate m m).length ≤ m := by simp
  rw [List.take_of_length_le hlength, List.drop_of_length_le hlength]
  simp only [List.append_nil, List.map_replicate, sort_replicate]

private theorem hhRow_uniform (n k : ℕ) :
    hhRow (List.replicate n (n-1)) k = List.replicate (n-k) (n-k-1) := by
  induction k with
  | zero => simp [hhRow]
  | succ k ih =>
    rw [hhRow, ih]
    by_cases h : k < n
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show n-k ≠ 0 by omega)
      have hm' : n - (k+1) = m := by omega
      simpa only [hm, hm', Nat.succ_sub_one] using hhStep_uniform m
    · have hz : n-k = 0 := by omega
      have hz' : n-(k+1) = 0 := by omega
      simp [hz, hz', hhStep]

theorem complete_row {V : Type*} [Fintype V] [DecidableEq V] (j : ℕ) :
    hhRow (degreeSequence (⊤ : SimpleGraph V)) j =
      List.replicate (Fintype.card V-j) (Fintype.card V-j-1) := by
  rw [complete_degree_sequence, hhRow_uniform]

theorem complete_first_zero {V : Type*} [Fintype V] [DecidableEq V]
    (hn : 0 < Fintype.card V) :
    FirstZero (degreeSequence (⊤ : SimpleGraph V)) (Fintype.card V-1) := by
  constructor
  · rw [complete_row]
    have h : Fintype.card V - (Fintype.card V - 1) = 1 := by omega
    simp [h]
  · intro j hj
    rw [complete_row]
    simp only [List.mem_replicate, not_and]
    intros _ h
    omega

theorem complete_satisfies_bound {V : Type*} [Fintype V] [DecidableEq V]
    (hn : 2 < Fintype.card V) (h : ∃ D, IsTotalDominating (⊤ : SimpleGraph V) D) :
    totalDominationNumber (⊤ : SimpleGraph V) h ≤
      Fintype.card V - 1 + matchingNumber (⊤ : SimpleGraph V)ᶜ := by
  have hv : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hv
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
  have hD : IsTotalDominating (⊤ : SimpleGraph V) {v,w} := by
    intro u
    by_cases e : u = v
    · exact ⟨w, by simp, (top_adj u w).mpr (e ▸ hw.symm)⟩
    · exact ⟨v, by simp, (top_adj u v).mpr e⟩
  have htwo : totalDominationNumber (⊤ : SimpleGraph V) h ≤ 2 :=
    Nat.sInf_le ⟨{v,w}, hD, card_pair hw.symm⟩
  omega

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

abbrev Vertex := Fin 45

/-- Vertex 0 is the hub. The short leg is 0–1–2, and each triple
3+3i, 4+3i, 5+3i gives a length-three leg. -/
private def row (v : Vertex) : ℕ :=
  #[5026338869834, 5, 2, 17, 40, 16, 129, 320, 128, 1025, 2560, 1024, 8193, 20480, 8192, 65537, 163840, 65536, 524289, 1310720, 524288, 4194305, 10485760, 4194304, 33554433, 83886080, 33554432, 268435457, 671088640, 268435456, 2147483649, 5368709120, 2147483648, 17179869185, 42949672960, 17179869184, 137438953473, 343597383680, 137438953472, 1099511627777, 2748779069440, 1099511627776, 8796093022209, 21990232555520, 8796093022208][v.val]!

private def edge (u v : Vertex) : Prop := (row u).testBit v.val = true

private instance : DecidableRel edge := fun _ _ =>
  inferInstanceAs (Decidable (_ = (true : Bool)))

def graph : SimpleGraph Vertex where
  Adj := edge
  symm := by
    change ∀ u v, edge u v → edge v u
    decide
  loopless := by
    change ∀ u, ¬ edge u u
    decide

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel edge)

instance : DecidableRel graphᶜ.Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ¬graph.Adj x y))

def dominatingSet : Finset Vertex := {0, 1, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16, 18, 19, 21, 22, 24, 25, 27, 28, 30, 31, 33, 34, 36, 37, 39, 40, 42, 43}

private theorem dominatingSet_total : IsTotalDominating graph dominatingSet := by
  unfold IsTotalDominating
  decide

theorem totalDomination_exists : ∃ D, IsTotalDominating graph D :=
  ⟨dominatingSet, dominatingSet_total⟩

theorem connected : graph.Connected := by
  have hcert : ∀ w ∈ dominatingSet, w = 0 ∨ graph.Adj 0 w ∨
      ∃ r : Vertex, graph.Adj 0 r ∧ graph.Adj r w := by decide
  apply (connected_iff_exists_forall_reachable graph).mpr
  refine ⟨0, fun v => ?_⟩
  obtain ⟨w, hw, ha⟩ := dominatingSet_total v
  have hr : graph.Reachable 0 w := by
    rcases hcert w hw with rfl | hd | ⟨r, hr, hd⟩
    · exact .rfl
    · exact hd.reachable
    · exact hr.reachable.trans hd.reachable
  exact hr.trans ha.symm.reachable

private def packing (i : Fin 30) : Vertex := #[1, 2, 4, 5, 7, 8, 10, 11, 13, 14, 16, 17, 19, 20, 22, 23, 25, 26, 28, 29, 31, 32, 34, 35, 37, 38, 40, 41, 43, 44][i.val]!

private theorem packing_disjoint :
    ∀ i j, i ≠ j → ∀ u, ¬ (graph.Adj (packing i) u ∧ graph.Adj (packing j) u) := by
  decide

theorem totalDomination_eq_thirty : totalDominationNumber graph totalDomination_exists = 30 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨dominatingSet, dominatingSet_total, by decide⟩
  · change 30 ≤ sInf {k : ℕ | ∃ D, IsTotalDominating graph D ∧ D.card = k}
    have he : {k : ℕ | ∃ D, IsTotalDominating graph D ∧ D.card = k}.Nonempty :=
      ⟨30, dominatingSet, dominatingSet_total, by decide⟩
    obtain ⟨D, hD, hcard⟩ := Nat.sInf_mem he
    rw [← hcard]
    choose f hf hAdj using fun i => hD (packing i)
    let toDom (i : Fin 30) : ↥D := ⟨f i, hf i⟩
    have hinj : Function.Injective toDom := by
      intro i j hij
      by_contra hne
      have heq : f i = f j := congrArg Subtype.val hij
      exact packing_disjoint i j hne (f i) ⟨hAdj i, heq.symm ▸ hAdj j⟩
    simpa using Fintype.card_le_of_injective toDom hinj

private def matchingEdges (i : Fin 22) : Vertex × Vertex := #[(0, 2), (3, 7), (4, 8), (5, 6), (9, 13), (10, 14), (11, 12), (15, 19), (16, 20), (17, 18), (21, 25), (22, 26), (23, 24), (27, 31), (28, 32), (29, 30), (33, 37), (34, 38), (35, 36), (39, 43), (40, 44), (41, 42)][i.val]!

private def matchingEndpoints (p : Fin 22 × Bool) : Vertex :=
  if p.2 then (matchingEdges p.1).2 else (matchingEdges p.1).1

theorem complement_matching_eq_twenty_two : matchingNumber graphᶜ = 22 := by
  apply le_antisymm
  · apply csSup_le (matching_nonempty graphᶜ)
    intro k hk
    have h := matching_le_half (show HasMatching graphᶜ k from hk)
    simpa using h
  · apply le_csSup (matching_bounded graphᶜ)
    refine ⟨matchingEndpoints, ?_, by decide⟩
    change ∀ a b, matchingEndpoints a = matchingEndpoints b → a = b
    decide

theorem witness_degree_sequence :
    degreeSequence graph = 15 :: (List.replicate 29 2 ++ List.replicate 15 1) := by
  decide

theorem witness_first_zero_row : hhRow (degreeSequence graph) 6 =
    List.replicate 38 1 ++ [0] := by
  rw [witness_degree_sequence]
  decide

theorem first_zero_six : FirstZero (degreeSequence graph) 6 := by
  constructor
  · rw [witness_first_zero_row]
    simp
  · intro j hj
    rw [witness_degree_sequence]
    have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem disprove287 : ¬ Conjecture287 := by
  intro h
  have hbound := h Vertex graph connected (by decide) 6 first_zero_six
  rw [totalDomination_eq_thirty, complement_matching_eq_twenty_two] at hbound
  omega

/-- This witness fails even if the initial row is labeled 1. -/
theorem witness_fails_with_initial_row_one :
    6 + 1 + matchingNumber graphᶜ < totalDominationNumber graph totalDomination_exists := by
  rw [complement_matching_eq_twenty_two, totalDomination_eq_thirty]
  decide

#print axioms complete_first_zero
#print axioms complete_satisfies_bound
#print axioms witness_degree_sequence
#print axioms witness_first_zero_row
#print axioms first_zero_six
#print axioms totalDomination_eq_thirty
#print axioms complement_matching_eq_twenty_two
#print axioms disprove287
#print axioms witness_fails_with_initial_row_one

end Graffiti287
