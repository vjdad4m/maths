import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice

/-!
A 17-vertex counterexample to Written on the Wall II #281.
This is a variant of the prior apex-over-triangles corona construction
in Claude Opus 5's graffiti-verification README, sections 8 and 7ge.
Prior disproof (July 30, 2026):
https://grok-ai-village-news-496089.gitlab.io/articles/opus5-graffiti-conj281-total-domination-2corona-bridge.html
Prior verification artifacts:
GitLab repository ai-village-agents/village/graffiti-verification, verify/verify_conj281.py.

This adaptation gives total domination 10, matching number 8, and
one minimum-local-independence vertex in the complement.
Official catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti281

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

def IsLocallyIndependent {V : Type*} (G : SimpleGraph V) (v : V) (S : Finset V) : Prop :=
  (∀ a ∈ S, G.Adj v a) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬G.Adj a b

private instance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) :
    Decidable (IsLocallyIndependent G v S) := by
  unfold IsLocallyIndependent
  infer_instance

noncomputable def localIndependence {V : Type*} (G : SimpleGraph V) (v : V) : ℕ :=
  sSup {n | ∃ S : Finset V, IsLocallyIndependent G v S ∧ S.card = n}

noncomputable def minimumLocalVertices {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, localIndependence G v ≤ localIndependence G w

noncomputable def minimumFrequency {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (minimumLocalVertices G).card

theorem exists_total_domination_of_connected {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (hn : 1 < Fintype.card V) : ∃ D, IsTotalDominating G D := by
  refine ⟨univ, fun v => ?_⟩
  obtain ⟨w, hne⟩ := Fintype.exists_ne_of_one_lt_card hn v
  obtain ⟨p⟩ := hc.preconnected v w
  exact ⟨p.snd, mem_univ _, p.adj_snd (Walk.not_nil_of_ne hne.symm)⟩

def Conjecture281 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (hc : G.Connected)
    (hn : 2 < Fintype.card V),
      totalDominationNumber G (exists_total_domination_of_connected hc (by omega)) ≤
        matchingNumber G + minimumFrequency Gᶜ

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

private theorem independent_bounded {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    BddAbove {k : ℕ | ∃ S : Finset V, IsLocallyIndependent G v S ∧ S.card = k} := by
  refine ⟨Fintype.card V, ?_⟩
  rintro _ ⟨S, _, rfl⟩
  exact card_le_univ S

private theorem independent_nonempty {V : Type*} (G : SimpleGraph V) (v : V) :
    {k : ℕ | ∃ S : Finset V, IsLocallyIndependent G v S ∧ S.card = k}.Nonempty :=
  ⟨0, ∅, by simp [IsLocallyIndependent], rfl⟩

private theorem localIndependence_ge_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v : V} {S : Finset V} (h : IsLocallyIndependent G v S) :
    S.card ≤ localIndependence G v :=
  le_csSup (independent_bounded G v) ⟨S, h, rfl⟩

theorem localIndependence_eq_zero_of_isolated {V : Type*} (G : SimpleGraph V) (v : V)
    (h : ∀ w, ¬G.Adj v w) : localIndependence G v = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le (independent_nonempty G v)
  rintro _ ⟨S, hS, rfl⟩
  have hempty : S = ∅ := not_nonempty_iff_eq_empty.mp (fun ⟨a, ha⟩ => h a (hS.1 a ha))
  rw [hempty, card_empty]

abbrev Vertex := Fin 17

/-- Apex 0 joins triangles {1,2,3} and {4,5,6}. Five of the seven
base vertices carry a pendant two-edge path. -/
private def edges : List (Vertex × Vertex) :=
  [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (1,2), (1,3), (2,3),
    (4,5), (4,6), (5,6), (0,7), (7,8), (1,9), (9,10),
    (2,11), (11,12), (3,13), (13,14), (4,15), (15,16)]

private def edge (u v : Vertex) : Prop := (u,v) ∈ edges ∨ (v,u) ∈ edges

private instance : DecidableRel edge := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def graph : SimpleGraph Vertex where
  Adj := edge
  symm := fun _ _ h => h.symm
  loopless := by
    change ∀ u, ¬edge u u
    decide

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel edge)

instance : DecidableRel graphᶜ.Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ¬graph.Adj x y))

def dominatingSet : Finset Vertex := {0,1,2,3,4,7,9,11,13,15}

private theorem dominatingSet_total : IsTotalDominating graph dominatingSet := by
  unfold IsTotalDominating
  decide

theorem totalDomination_exists : ∃ D, IsTotalDominating graph D :=
  ⟨dominatingSet, dominatingSet_total⟩

theorem connected : graph.Connected := by
  have hbase : ∀ v : Vertex, v.val < 7 → v = 0 ∨ graph.Adj 0 v := by decide
  have hattached : ∀ v ∈ dominatingSet, 7 ≤ v.val →
      ∃ r : Vertex, r.val < 7 ∧ graph.Adj r v := by decide
  have base_reach (v : Vertex) (hv : v.val < 7) : graph.Reachable 0 v := by
    rcases hbase v hv with rfl | ha
    · exact .rfl
    · exact ha.reachable
  apply (connected_iff_exists_forall_reachable graph).mpr
  refine ⟨0, fun v => ?_⟩
  obtain ⟨w, hw, ha⟩ := dominatingSet_total v
  have hr : graph.Reachable 0 w := by
    by_cases h : w.val < 7
    · exact base_reach w h
    · obtain ⟨r, hr, hrw⟩ := hattached w hw (by omega)
      exact (base_reach r hr).trans hrw.reachable
  exact hr.trans ha.symm.reachable

private def packing (i : Fin 10) : Vertex := #[7,8,9,10,11,12,13,14,15,16][i.val]!

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem packing_disjoint :
    ∀ i j, i ≠ j → ∀ u, ¬ (graph.Adj (packing i) u ∧ graph.Adj (packing j) u) := by
  decide

theorem totalDomination_eq_ten : totalDominationNumber graph totalDomination_exists = 10 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨dominatingSet, dominatingSet_total, by decide⟩
  · change 10 ≤ sInf {k : ℕ | ∃ D, IsTotalDominating graph D ∧ D.card = k}
    have he : {k : ℕ | ∃ D, IsTotalDominating graph D ∧ D.card = k}.Nonempty :=
      ⟨10, dominatingSet, dominatingSet_total, by decide⟩
    obtain ⟨D, hD, hcard⟩ := Nat.sInf_mem he
    rw [← hcard]
    choose f hf hAdj using fun i => hD (packing i)
    let toDom (i : Fin 10) : ↥D := ⟨f i, hf i⟩
    have hinj : Function.Injective toDom := by
      intro i j hij
      by_contra hne
      have heq : f i = f j := congrArg Subtype.val hij
      exact packing_disjoint i j hne (f i) ⟨hAdj i, heq.symm ▸ hAdj j⟩
    simpa using Fintype.card_le_of_injective toDom hinj

private def matchingEdges (i : Fin 8) : Vertex × Vertex :=
  #[(0,1), (2,3), (4,5), (7,8), (9,10), (11,12), (13,14), (15,16)][i.val]!

private def matchingEndpoints (p : Fin 8 × Bool) : Vertex :=
  if p.2 then (matchingEdges p.1).2 else (matchingEdges p.1).1

theorem matching_eq_eight : matchingNumber graph = 8 := by
  apply le_antisymm
  · apply csSup_le (matching_nonempty graph)
    intro k hk
    have h := matching_le_half (show HasMatching graph k from hk)
    simpa using h
  · apply le_csSup (matching_bounded graph)
    refine ⟨matchingEndpoints, ?_, by decide⟩
    change ∀ a b, matchingEndpoints a = matchingEndpoints b → a = b
    decide

private def tripleAway (v : Vertex) : Finset Vertex :=
  if v ∈ ({1,2,3,9,11,13} : Finset Vertex) then {4,5,6} else {1,2,3}

private theorem non_apex_has_three (v : Vertex) (hv : v ≠ 0) :
    3 ≤ localIndependence graphᶜ v := by
  have hcert : ∀ a : Vertex, a ≠ 0 →
      IsLocallyIndependent graphᶜ a (tripleAway a) ∧ (tripleAway a).card = 3 := by decide
  obtain ⟨hs, hsize⟩ := hcert v hv
  exact hsize ▸ localIndependence_ge_card hs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem apex_no_three :
    ∀ a b c, graphᶜ.Adj 0 a → graphᶜ.Adj 0 b → graphᶜ.Adj 0 c →
      a ≠ b → a ≠ c → b ≠ c →
      ¬ (graph.Adj a b ∧ graph.Adj a c ∧ graph.Adj b c) := by
  decide

theorem apex_local_independence : localIndependence graphᶜ 0 = 2 := by
  apply le_antisymm
  · apply csSup_le (independent_nonempty graphᶜ 0)
    rintro _ ⟨S, hS, rfl⟩
    by_contra! large
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp large
    have edge_of_indep {x y : Vertex} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
        graph.Adj x y := by
      by_contra hnot
      exact (hS.2 x hx y hy hne) ((compl_adj graph x y).mpr ⟨hne, hnot⟩)
    exact apex_no_three a b c (hS.1 a ha) (hS.1 b hb) (hS.1 c hc) hab hac hbc
      ⟨edge_of_indep ha hb hab, edge_of_indep ha hc hac, edge_of_indep hb hc hbc⟩
  · have hcert : IsLocallyIndependent graphᶜ 0 ({9,10} : Finset Vertex) := by decide
    have hs : ({9,10} : Finset Vertex).card = 2 := by decide
    exact hs ▸ localIndependence_ge_card hcert

theorem minimumFrequency_eq_one : minimumFrequency graphᶜ = 1 := by
  classical
  have hset : minimumLocalVertices graphᶜ = {0} := by
    ext v
    simp only [minimumLocalVertices, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      by_contra hv
      have hlow := non_apex_has_three v hv
      have hhigh := h 0
      rw [apex_local_independence] at hhigh
      omega
    · rintro rfl w
      by_cases hw : w = 0
      · subst w
        exact le_rfl
      · rw [apex_local_independence]
        exact (by decide : 2 ≤ 3).trans (non_apex_has_three w hw)
  rw [minimumFrequency, hset, card_singleton]

theorem disprove281 : ¬ Conjecture281 := by
  intro h
  have hbound := h Vertex graph connected (by decide)
  rw [totalDomination_eq_ten, matching_eq_eight, minimumFrequency_eq_one] at hbound
  omega

#print axioms localIndependence_eq_zero_of_isolated
#print axioms totalDomination_eq_ten
#print axioms matching_eq_eight
#print axioms minimumFrequency_eq_one
#print axioms disprove281

end Graffiti281
