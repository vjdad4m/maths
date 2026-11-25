/- Pinned proposal https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L66 . A 16-vertex tree has burning number at most 3 and power domination number at least 5, violating the asserted upper bound 4.
Lean 4.19.0 / Mathlib v4.19.0, run lake env lean. AI-assisted work; no priority claim. -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-! Dismantles the surviving AutoGraphForge conjecture in pinned catalogue line 66.
    Both invariants use the GraphCalc 2.0 operational semantics. -/
namespace AutoGraphPowerBurning

inductive Observed {V : Type*} (G : SimpleGraph V) (S : Finset V) : V → Prop where
  | root {v} (h : v ∈ S) : Observed G S v
  | neighbor {v w} (h : w ∈ S) (hvw : G.Adj v w) : Observed G S v
  | force {v w} (hvw : G.Adj v w) (hw : Observed G S w)
      (rest : ∀ u, G.Adj w u → u ≠ v → Observed G S u) : Observed G S v

noncomputable def power {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ S : Finset V, n = S.card ∧ ∀ v, Observed G S v}

def Burns {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ source : Fin k → V, ∀ v, ∃ t : Fin k, ∃ p : G.Walk (source t) v,
    p.length ≤ k - 1 - t.val

noncomputable def burning {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | Burns G k}

private abbrev I := Fin 5
private abbrev V := Option (I × Fin 3)
private def hub : V := none
private def branch (i : I) : V := some (i,0)
private def leaf1 (i : I) : V := some (i,1)
private def leaf2 (i : I) : V := some (i,2)

private def adj : V → V → Prop
  | none, none => False
  | none, some (_, t) => t = 0
  | some (_, t), none => t = 0
  | some (i,t), some (j,u) => i = j ∧ ((t = 0 ∧ u ≠ 0) ∨ (t ≠ 0 ∧ u = 0))

private def G : SimpleGraph V where
  Adj := adj
  symm := by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · rename_i a b
      rcases a with ⟨i,t⟩; rcases b with ⟨j,u⟩
      rcases h with ⟨h, ⟨ht,hu⟩ | ⟨ht,hu⟩⟩
      · exact ⟨h.symm, .inr ⟨hu,ht⟩⟩
      · exact ⟨h.symm, .inl ⟨hu,ht⟩⟩
  loopless := by
    rintro (_ | ⟨i,t⟩) h
    · exact h
    · rcases h with ⟨_, ⟨ht,hn⟩ | ⟨hn,ht⟩⟩ <;> exact hn ht

private theorem hub_branch (i : I) : G.Adj hub (branch i) := rfl
private theorem branch_leaf1 (i : I) : G.Adj (branch i) (leaf1 i) :=
  ⟨rfl,.inl ⟨rfl,by decide⟩⟩
private theorem branch_leaf2 (i : I) : G.Adj (branch i) (leaf2 i) :=
  ⟨rfl,.inl ⟨rfl,by decide⟩⟩

private theorem leaf1_neighbor (i : I) (u : V) : G.Adj (leaf1 i) u → u = branch i := by
  rcases u with (_ | ⟨j,t⟩)
  · intro h; exact (by decide : (1 : Fin 3) ≠ 0) h |>.elim
  · intro h
    rcases h with ⟨rfl, ⟨hf,_⟩ | ⟨_,rfl⟩⟩
    · exact (by decide : (1 : Fin 3) ≠ 0) hf |>.elim
    · rfl

private theorem leaf2_neighbor (i : I) (u : V) : G.Adj (leaf2 i) u → u = branch i := by
  rcases u with (_ | ⟨j,t⟩)
  · intro h; exact (by decide : (2 : Fin 3) ≠ 0) h |>.elim
  · intro h
    rcases h with ⟨rfl, ⟨hf,_⟩ | ⟨_,rfl⟩⟩
    · exact (by decide : (2 : Fin 3) ≠ 0) hf |>.elim
    · rfl

private theorem leaf_ne (i : I) : leaf1 i ≠ leaf2 i := by
  simp [leaf1, leaf2]

private theorem miss_pair (S : Finset V) (i : I)
    (hb : branch i ∉ S) (h1 : leaf1 i ∉ S) (h2 : leaf2 i ∉ S) {v : V}
    (h : Observed G S v) : v ≠ leaf1 i ∧ v ≠ leaf2 i := by
  induction h with
  | root hv => exact ⟨fun e => h1 (e ▸ hv), fun e => h2 (e ▸ hv)⟩
  | neighbor hw hvw =>
    exact ⟨fun e => hb (leaf1_neighbor _ _ (e ▸ hvw) ▸ hw),
           fun e => hb (leaf2_neighbor _ _ (e ▸ hvw) ▸ hw)⟩
  | @force v w hvw _ _ _ ih =>
    constructor
    · intro hv
      have he : w = branch i := leaf1_neighbor i w (hv ▸ hvw)
      apply (ih (leaf2 i) (he ▸ branch_leaf2 i) ?_).2 rfl
      exact fun e => leaf_ne i (hv.symm.trans e.symm)
    · intro hv
      have he : w = branch i := leaf2_neighbor i w (hv ▸ hvw)
      apply (ih (leaf1 i) (he ▸ branch_leaf1 i) ?_).1 rfl
      exact fun e => leaf_ne i (e.trans hv)

private theorem seed_in_branch (S : Finset V) (h : ∀ v, Observed G S v) (i : I) :
    ∃ v : V, v ∈ S ∧ ∃ t : Fin 3, v = some (i,t) := by
  classical
  by_cases h0 : branch i ∈ S
  · exact ⟨branch i,h0,0,rfl⟩
  by_cases h1 : leaf1 i ∈ S
  · exact ⟨leaf1 i,h1,1,rfl⟩
  by_cases h2 : leaf2 i ∈ S
  · exact ⟨leaf2 i,h2,2,rfl⟩
  exact ((miss_pair S i h0 h1 h2 (h (leaf1 i))).1 rfl).elim

private theorem five_seeds (S : Finset V) (h : ∀ v, Observed G S v) : 5 ≤ S.card := by
  classical
  let f : I → V := fun i => (seed_in_branch S h i).choose
  have hf (i : I) : f i ∈ S ∧ ∃ t : Fin 3, f i = some (i,t) :=
    (seed_in_branch S h i).choose_spec
  have h_inj : Function.Injective f := by
    intro i j h
    obtain ⟨t, ht⟩ := (hf i).2
    obtain ⟨u, hu⟩ := (hf j).2
    rw [ht, hu, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1
  let F : I ↪ V := ⟨f,h_inj⟩
  have hsub : Finset.univ.map F ⊆ S := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
    exact (hf i).1
  simpa using Finset.card_le_card hsub

private theorem power_ge : 5 ≤ power G := by
  classical
  have hn : ({n | ∃ S : Finset V, n = S.card ∧ ∀ v, Observed G S v} : Set ℕ).Nonempty := by
    exact ⟨_, Finset.univ, rfl, fun v => Observed.root (Finset.mem_univ v)⟩
  have hout := Nat.sInf_mem hn
  change ∃ S : Finset V, power G = S.card ∧ ∀ v, Observed G S v at hout
  obtain ⟨S, he, hs⟩ := hout
  exact he.symm ▸ five_seeds S hs

private theorem from_hub (v : V) : ∃ p : G.Walk hub v, p.length ≤ 2 := by
  rcases v with (_ | ⟨i,t⟩)
  · exact ⟨.nil, by simp⟩
  have ht : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases ht with rfl | rfl | rfl
  · exact ⟨.cons (hub_branch i) .nil, by simp⟩
  · exact ⟨.cons (hub_branch i) (.cons (branch_leaf1 i) .nil), by simp⟩
  · exact ⟨.cons (hub_branch i) (.cons (branch_leaf2 i) .nil), by simp⟩

private theorem g_conn : G.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨hub, fun v => ⟨(from_hub v).choose⟩⟩

private theorem burning_le : burning G ≤ 3 := by
  apply Nat.sInf_le
  change Burns G 3
  refine ⟨fun t => if t = 0 then hub else if t = 1 then leaf1 0 else leaf1 1, ?_⟩
  intro v
  obtain ⟨p,hp⟩ := from_hub v
  exact ⟨0, by simp; exact ⟨p,hp⟩⟩

def Conjecture : Prop := ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
  2 ≤ Fintype.card V → G.Connected → (power G : ℤ) ≤ 3 * (burning G : ℤ) - 5

/-- The exact normalized AutoGraphForge survivor 4d1a8af, line 66, is false. -/
theorem power_burning_false : ¬ Conjecture := by
  intro h
  have hh := h V G (by decide) g_conn
  have hp := power_ge
  have hb := burning_le
  omega

#print axioms power_burning_false
end AutoGraphPowerBurning
