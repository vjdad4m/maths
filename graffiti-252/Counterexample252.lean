/- Independent Lean verification of Graffiti.pc #252 using a different graph.
Jonas Gebendorfer previously refuted the conjecture: https://www.researchgate.net/publication/414086193_A_30-vertex_C_4_-free_counterexample_to_WOWII_Conjecture_252
No priority claim. Replay with Lean and Mathlib v4.19.0. -/
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.FinCases

namespace Graffiti252

open Finset SimpleGraph

def IsTotalDominating {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w, w ∈ D ∧ G.Adj v w

noncomputable def totalDominationNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, IsTotalDominating G D ∧ D.card = k}

def degreeFrequency {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  (univ.filter fun v => G.degree v = d).card

noncomputable def smallestModalDegree {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] : ℕ :=
  sInf {d | ∀ k, degreeFrequency G k ≤ degreeFrequency G d}

def FourCycleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v (w : G.Walk v v), w.IsCycle → w.length ≠ 4

/-- In the convention that acyclic graphs have infinite girth. -/
def GirthAtLeastFive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length

def Conjecture252 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    1 < Fintype.card V → G.Connected → FourCycleFree G →
    smallestModalDegree G ≤ totalDominationNumber G

def Conjecture253 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    1 < Fintype.card V → G.Connected → GirthAtLeastFive G →
    smallestModalDegree G + 1 ≤ totalDominationNumber G

abbrev Vertex := Fin 30

/-- Bit v of row u is one exactly when vertices u and v are adjacent. -/
private def rowAdj (rows : Vertex → ℕ) (u v : Vertex) : Prop :=
  (rows u).testBit v.val = true

private instance (rows : Vertex → ℕ) : DecidableRel (rowAdj rows) :=
  fun _ _ => inferInstanceAs (Decidable (_ = (true : Bool)))

private def rows252 (v : Vertex) : ℕ :=
  #[857346, 3285633, 12733448, 50430148, 201333344, 805363984,
    69271576, 268435978, 272695329, 138412178, 8388613, 20,
    17, 35668002, 8228, 40, 329, 6,
    1, 67108865, 2, 8396866, 772, 404751364,
    8, 134225928, 524368, 41943568, 8389024, 32][v.val]!

private def rows253 (v : Vertex) : ℕ :=
  #[62466, 68417, 1966344, 6294660, 58720928, 1006633040,
    4194338, 24, 6, 2097170, 9, 150994954,
    1, 558366721, 1, 170917889, 570425346, 536870916,
    33554436, 134225924, 16809988, 536904200, 33562696, 16,
    1058832, 4554768, 32, 559136, 32, 2301984][v.val]!

def graph252 : SimpleGraph Vertex where
  Adj := rowAdj rows252
  symm := by
    change ∀ u v, rowAdj rows252 u v → rowAdj rows252 v u
    decide
  loopless := by
    change ∀ u, ¬ rowAdj rows252 u u
    decide

def graph253 : SimpleGraph Vertex where
  Adj := rowAdj rows253
  symm := by
    change ∀ u v, rowAdj rows253 u v → rowAdj rows253 v u
    decide
  loopless := by
    change ∀ u, ¬ rowAdj rows253 u u
    decide

instance : DecidableRel graph252.Adj := inferInstanceAs (DecidableRel (rowAdj rows252))
instance : DecidableRel graph253.Adj := inferInstanceAs (DecidableRel (rowAdj rows253))

private def roots : Finset Vertex := {0, 1, 2, 3, 4, 5}

private theorem roots252 : IsTotalDominating graph252 roots := by
  unfold IsTotalDominating
  decide

private theorem roots253 : IsTotalDominating graph253 roots := by
  unfold IsTotalDominating
  decide

private theorem connected_of_roots {G : SimpleGraph Vertex}
    (h : IsTotalDominating G roots) (hr : ∀ w ∈ roots, G.Reachable 0 w) :
    G.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable G).mpr
  refine ⟨0, fun w => ?_⟩
  obtain ⟨u, hu, hwu⟩ := h w
  exact (hr u hu).trans hwu.symm.reachable

theorem connected252 : graph252.Connected := by
  apply connected_of_roots roots252
  intro v hv
  simp only [roots, mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .rfl
  · exact (show graph252.Adj 0 1 by decide).reachable
  · exact (show graph252.Adj 0 10 by decide).reachable.trans
      (show graph252.Adj 10 2 by decide).reachable
  · exact (show graph252.Adj 0 16 by decide).reachable.trans
      (show graph252.Adj 16 3 by decide).reachable
  · exact (show graph252.Adj 0 12 by decide).reachable.trans
      (show graph252.Adj 12 4 by decide).reachable
  · exact (show graph252.Adj 0 8 by decide).reachable.trans
      (show graph252.Adj 8 5 by decide).reachable

theorem connected253 : graph253.Connected := by
  apply connected_of_roots roots253
  intro v hv
  simp only [roots, mem_insert, mem_singleton] at hv
  have edge01 := (show graph253.Adj 0 1 by decide).reachable
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .rfl
  · exact edge01
  · exact edge01.trans ((show graph253.Adj 1 8 by decide).reachable.trans
      (show graph253.Adj 8 2 by decide).reachable)
  · exact (show graph253.Adj 0 10 by decide).reachable.trans
      (show graph253.Adj 10 3 by decide).reachable
  · exact edge01.trans ((show graph253.Adj 1 9 by decide).reachable.trans
      (show graph253.Adj 9 4 by decide).reachable)
  · exact edge01.trans ((show graph253.Adj 1 6 by decide).reachable.trans
      (show graph253.Adj 6 5 by decide).reachable)

private def common {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : Finset V :=
  univ.filter fun w => G.Adj u w ∧ G.Adj v w

private theorem mem_common {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w : V) : w ∈ common G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [common]

private theorem no_four_cycle {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : ∀ u v, u ≠ v → (common G u v).card ≤ 1) :
    FourCycleFree G := by
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
set_option maxHeartbeats 5000000 in
theorem four_cycle_free252 : FourCycleFree graph252 := by
  apply no_four_cycle
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem girth_ge_five253 : GirthAtLeastFive graph253 := by
  have h4 : FourCycleFree graph253 := by
    apply no_four_cycle
    decide
  have h3 : ∀ v (w : graph253.Walk v v), w.IsCycle → w.length ≠ 3 := by
    apply no_three_cycle
    decide
  intro v w hc
  have h := hc.three_le_length
  have h' := h3 v w hc
  have h'' := h4 v w hc
  omega

private def cycle253 : graph253.Walk 0 0 :=
  .cons (show graph253.Adj 0 1 by decide)
    (.cons (show graph253.Adj 1 11 by decide)
      (.cons (show graph253.Adj 11 3 by decide)
        (.cons (show graph253.Adj 3 10 by decide)
          (.cons (show graph253.Adj 10 0 by decide) .nil))))

theorem five_cycle253 : ∃ w : graph253.Walk 0 0, w.IsCycle ∧ w.length = 5 := by
  refine ⟨cycle253, (Walk.isCycle_def _).mpr ⟨?_, ?_, ?_⟩, by decide⟩
  · rw [Walk.isTrail_def]
    decide
  · simp [cycle253]
  · decide

private theorem total_domination_eq_six {G : SimpleGraph Vertex} (h : IsTotalDominating G roots)
    (test : Fin 6 → Vertex)
    (hdis : ∀ i j, i ≠ j → ∀ u, ¬ (G.Adj (test i) u ∧ G.Adj (test j) u)) :
    totalDominationNumber G = 6 := by
  have hex : 6 ∈ {k | ∃ D : Finset Vertex, IsTotalDominating G D ∧ D.card = k} :=
    ⟨roots, h, by decide⟩
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) hex
  · apply le_csInf ⟨6, hex⟩
    rintro _ ⟨D, hD, rfl⟩
    choose f hm ha using fun i : Fin 6 => hD (test i)
    let g (i : Fin 6) : ↥D := ⟨f i, hm i⟩
    have hg : Function.Injective g := by
      intro i j he
      by_contra hij
      have hf : f i = f j := congrArg Subtype.val he
      exact hdis i j hij (f i) ⟨ha i, hf.symm ▸ ha j⟩
    simpa using Fintype.card_le_of_injective g hg

private def tests252 (i : Fin 6) : Vertex := #[(18 : Vertex), 20, 24, 29, 22, 26][i.val]!
private def tests253 (i : Fin 6) : Vertex := #[(12 : Vertex), 23, 26, 0, 2, 17][i.val]!

theorem total_domination252 : totalDominationNumber graph252 = 6 :=
  total_domination_eq_six roots252 tests252 (by decide)

theorem total_domination253 : totalDominationNumber graph253 = 6 :=
  total_domination_eq_six roots253 tests253 (by decide)

private theorem frequency_zero_of_ge_order {G : SimpleGraph Vertex} [DecidableRel G.Adj]
    {k : ℕ} (hk : 30 ≤ k) : degreeFrequency G k = 0 := by
  unfold degreeFrequency
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro v hv
  have he := (Finset.mem_filter.mp hv).2
  have hlt := G.degree_lt_card_verts v
  simp only [Vertex, Fintype.card_fin] at hlt
  omega

private theorem modal_degree_eq {G : SimpleGraph Vertex} [DecidableRel G.Adj]
    {d : ℕ} (hd : d < 30)
    (h : ∀ k : Vertex, degreeFrequency G k.val ≤ degreeFrequency G d ∧
      (k.val < d → degreeFrequency G k.val < degreeFrequency G d)) :
    smallestModalDegree G = d := by
  have hm : d ∈ {j | ∀ k, degreeFrequency G k ≤ degreeFrequency G j} := by
    intro k
    by_cases hk : k < 30
    · exact (h ⟨k, hk⟩).1
    · rw [frequency_zero_of_ge_order (by omega)]
      exact Nat.zero_le _
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) hm
  · apply le_csInf ⟨d, hm⟩
    intro k hk
    by_contra hnk
    have hlt : k < d := by omega
    exact (Nat.not_le_of_gt ((h ⟨k, hlt.trans hd⟩).2 hlt)) (hk d)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem smallest_mode252 : smallestModalDegree graph252 = 7 :=
  modal_degree_eq (by decide) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem smallest_mode253 : smallestModalDegree graph253 = 6 :=
  modal_degree_eq (by decide) (by decide)

theorem not_conjecture252 : ¬ Conjecture252 := by
  intro h
  have bad := h Vertex graph252 (by decide) connected252 four_cycle_free252
  rw [smallest_mode252, total_domination252] at bad
  omega

#print axioms not_conjecture252

end Graffiti252
