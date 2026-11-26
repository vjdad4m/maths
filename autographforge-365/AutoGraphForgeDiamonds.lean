import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Ján Pastorek, normalized AutoGraphForge lines 365, 376 and 1839, pinned commit
4d1a8afc99447cacd2328cca20e47b6493e8dbc5. A ring of five diamonds.
The power number and burning model below are the published line 66 definitions. -/
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

end AutoGraphPowerBurning

namespace AutoGraphForgeDiamonds
open SimpleGraph Finset AutoGraphPowerBurning
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
abbrev V := Fin 5 × Fin 4

def edges (a b : V) : Prop :=
  (a.1 = b.1 ∧ a.2 ≠ b.2 ∧ (a.2 = 1 ∨ a.2 = 2 ∨ b.2 = 1 ∨ b.2 = 2)) ∨
  (a.2 = 3 ∧ b.2 = 0 ∧ a.1 + 1 = b.1) ∨ (b.2 = 3 ∧ a.2 = 0 ∧ b.1 + 1 = a.1)
instance (a b : V) : Decidable (edges a b) := by unfold edges; infer_instance

def graph : SimpleGraph V where
  Adj := edges
  symm := by change ∀ a b : V, edges a b → edges b a; decide
  loopless := by change ∀ a : V, ¬ edges a a; decide

instance (a b : V) : Decidable (graph.Adj a b) := inferInstanceAs (Decidable (edges a b))

/-- The source predicate forbidding an induced claw. -/
def ClawFree {U : Type*} (G : SimpleGraph U) := ∀ v a b c : U,
  G.Adj v a → G.Adj v b → G.Adj v c → a ≠ b → a ≠ c → b ≠ c →
  G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

theorem clawFree : ClawFree graph := by
  have check : ∀ v a : V, graph.Adj v a → ∀ b : V, graph.Adj v b → ∀ c : V, graph.Adj v c →
      a ≠ b → a ≠ c → b ≠ c → graph.Adj a b ∨ graph.Adj a c ∨ graph.Adj b c := by decide
  exact fun v a b c ha hb hc => check v a ha b hb c hc

theorem noK4 : graph.CliqueFree 4 := by
  have check : ∀ a b : V, graph.Adj a b → ∀ c : V, graph.Adj a c → graph.Adj b c →
      ∀ d : V, graph.Adj a d → graph.Adj b d → ¬graph.Adj c d := by decide
  by_contra bad
  obtain ⟨f⟩ := (not_cliqueFree_iff _).mp bad
  have edge (i j : Fin 4) (ne : i ≠ j) : graph.Adj (f i) (f j) := f.map_adj_iff.mpr ne
  exact check (f 0) (f 1) (edge 0 1 (by decide)) (f 2) (edge 0 2 (by decide))
    (edge 1 2 (by decide)) (f 3) (edge 0 3 (by decide)) (edge 1 3 (by decide)) (edge 2 3 (by decide))

theorem cubic : graph.IsRegularOfDegree 3 := by
  have h : ∀ a : V, (univ.filter (edges a)).card = 3 := by decide
  intro a
  rw [SimpleGraph.degree, neighborFinset_eq_filter]
  exact h a

theorem subcubic : graph.maxDegree ≤ 3 :=
  graph.maxDegree_le_of_forall_degree_le 3 (fun v => (cubic v).le)

private def middle (i : Fin 5) (v : V) : Prop := v.1 = i ∧ (v.2=1 ∨ v.2=2)
private instance (i : Fin 5) (v : V) : Decidable (middle i v) := by unfold middle; infer_instance

/-- In a seedless diamond the two middle vertices form an unobserved fort. -/
private theorem missed (S : Finset V) (i : Fin 5) (miss : ∀ v ∈ S, v.1 ≠ i)
    {v : V} (obs : Observed graph S v) : ¬ middle i v := by
  have neighbors : ∀ (i : Fin 5) (v : V), middle i v → ∀ w : V, graph.Adj v w → w.1=i := by decide
  have twin : ∀ (i : Fin 5) (v : V), middle i v → ∀ w : V, graph.Adj v w → ¬middle i w →
      ∃ u : V, u ≠ v ∧ middle i u ∧ graph.Adj w u := by decide
  induction obs with
  | root hv => exact fun h => miss _ hv h.1
  | neighbor hw e => exact fun h => miss _ hw (neighbors _ _ h _ e)
  | @force v w e _ _ ihw ihrest =>
    intro hv
    obtain ⟨u,ne,hu,wu⟩ := twin i v hv w e ihw
    exact ihrest u wu ne hu

theorem power_exact : power graph = 5 := by
  classical
  let sizes := {n | ∃ S : Finset V, n = S.card ∧ ∀ v, Observed graph S v}
  have all : sizes.Nonempty := ⟨_,univ,rfl,fun x => .root (mem_univ x)⟩
  obtain ⟨S,cost,full⟩ := Nat.sInf_mem all
  change power graph = S.card at cost
  have covers : S.image Prod.fst = univ := by
    apply eq_univ_of_forall
    intro i
    by_contra h
    have no : ∀ v ∈ S, v.1 ≠ i := fun v hv hi => h (mem_image.mpr ⟨v,hv,hi⟩)
    exact missed S i no (full (i,1)) ⟨rfl,Or.inl rfl⟩
  have lo := card_image_le (f := Prod.fst) (s := S)
  rw [covers,card_univ,Fintype.card_fin,← cost] at lo
  apply Nat.le_antisymm _ lo
  let sel : Fin 5 ↪ V := ⟨fun i => (i,1),fun _ _ e => congrArg Prod.fst e⟩
  let D := univ.map sel
  apply Nat.sInf_le (s := sizes)
  refine ⟨D, by simp [D], ?_⟩
  intro v
  have seed : (v.1,1) ∈ D := mem_map.mpr ⟨v.1,mem_univ _,rfl⟩
  by_cases h : v.2 = 1
  · exact .root (show v ∈ D from (show (v.1,1) = v from Prod.ext rfl h.symm) ▸ seed)
  · apply Observed.neighbor seed
    exact Or.inl ⟨rfl,h,Or.inr (Or.inr (Or.inl rfl))⟩

private def within : ℕ → V → V → Bool
  | 0, u, v => decide (u = v)
  | n+1, u, v => decide (u = v ∨ ∃ w : V, graph.Adj u w ∧ within n w v = true)

private theorem walk_of_within {n : ℕ} {u v : V} (h : within n u v = true) :
    ∃ p : graph.Walk u v, p.length ≤ n := by
  induction n generalizing u v with
  | zero =>
    have e : u=v := of_decide_eq_true h
    subst v
    exact ⟨.nil,by simp⟩
  | succ n ih =>
    change decide (_ ∨ _) = true at h
    rcases of_decide_eq_true h with rfl | ⟨w,uw,hit⟩
    · exact ⟨.nil,by simp⟩
    · obtain ⟨p,hp⟩ := ih hit
      exact ⟨.cons uw p,by simpa using hp⟩

private def source (t : Fin 4) : V :=
  if t = 0 then (0,0) else if t = 1 then (1,3) else if t = 2 then (3,0) else (3,3)

private theorem four_rounds : Burns graph 4 := by
  have cover : ∀ v : V, ∃ t : Fin 4, within (3-t.val) (source t) v = true := by decide
  refine ⟨source,fun v => ?_⟩
  obtain ⟨t,h⟩ := cover v
  exact ⟨t,walk_of_within h⟩


theorem burning_upper : burning graph ≤ 4 := Nat.sInf_le (s := {k | Burns graph k}) four_rounds

private theorem within_of_walk {u v : V} (p : graph.Walk u v) (n : ℕ) (le : p.length ≤ n) :
    within n u v = true := by
  induction p generalizing n with
  | nil =>
    cases n with
    | zero => simp [within]
    | succ n => simp [within]
  | cons e p ih =>
    cases n with
    | zero => simp at le
    | succ n =>
      apply decide_eq_true
      exact Or.inr ⟨_,e,ih n (by simpa using le)⟩

theorem burning_exact : burning graph = 4 := by
  classical
  apply le_antisymm burning_upper
  by_contra bad
  have witness : ({k | Burns graph k} : Set ℕ).Nonempty := ⟨4,four_rounds⟩
  let k := burning graph
  have hk : k ≤ 3 := by dsimp [k]; omega
  obtain ⟨start,cover⟩ := (show Burns graph k from Nat.sInf_mem witness)
  let ignite (t : Fin 3) := if h : t.val < k then start ⟨t.val,h⟩ else (0,0)
  let ball (t : Fin 3) := univ.filter (fun v => within (2-t.val) (ignite t) v = true)
  have all : univ.biUnion ball = univ := by
    apply eq_univ_of_forall
    intro v
    obtain ⟨t,p,len⟩ := cover v
    let j : Fin 3 := ⟨t.val,by have := t.isLt; omega⟩
    apply mem_biUnion.mpr
    refine ⟨j,mem_univ _, mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    change within (2-t.val) (if h : t.val < k then start ⟨t.val,h⟩ else (0,0)) v = true
    rw [dif_pos t.isLt]
    exact within_of_walk p _ (by omega)
  have every : ∀ (t : Fin 3) (w : V),
      (univ.filter (fun v => within (2-t.val) w v = true)).card ≤ (if t=0 then 10 else if t=1 then 4 else 1) := by decide
  have big := card_biUnion_le (s := (univ : Finset (Fin 3))) (t := ball)
  rw [all,card_univ] at big
  have few := sum_le_sum (s := (univ : Finset (Fin 3))) (fun t _ => every t (ignite t))
  change ∑ t, (ball t).card ≤ _ at few
  have sum : (∑ t : Fin 3, if t=0 then 10 else if t=1 then 4 else 1) = 15 := by decide
  rw [sum] at few
  have n : Fintype.card V = 20 := by decide
  omega

theorem counterexample_line365 : 2 ≤ Fintype.card V ∧ graph.CliqueFree 4 ∧
    ClawFree graph ∧ ¬power graph ≤ burning graph :=
  ⟨by decide,noK4,clawFree,by have := power_exact; have := burning_exact; omega⟩

theorem counterexample_line376 : 2 ≤ Fintype.card V ∧ ClawFree graph ∧
    graph.maxDegree ≤ 3 ∧ ¬power graph ≤ burning graph :=
  ⟨by decide,clawFree,subcubic,by have := power_exact; have := burning_exact; omega⟩

theorem counterexample_line1839 : 2 ≤ Fintype.card V ∧ (∃ d, graph.IsRegularOfDegree d) ∧
    graph.maxDegree ≤ 3 ∧ ¬power graph ≤ burning graph :=
  ⟨by decide,⟨3,cubic⟩,subcubic,by have := power_exact; have := burning_exact; omega⟩

#print axioms counterexample_line1839
#print axioms power_exact
#print axioms burning_exact
#print axioms counterexample_line365
#print axioms counterexample_line376
end AutoGraphForgeDiamonds

