import Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace RegularHarmonic595
open SimpleGraph Finset
abbrev Hub (n : ℕ) := Fin (n + 1)
abbrev Block (n : ℕ) := Hub n × Bool
abbrev Vertex (n : ℕ) := Hub n ⊕ (Block n × Fin 5)

def inside (u v : Fin 5) : Prop :=
  u ≠ v ∧ ¬ ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0))

def attachment {n} (h : Hub n) (p : Block n) (u : Fin 5) : Prop :=
  (h = p.1 ∧ u = 0) ∨ (h = p.1 + 1 ∧ u = 1)

def adjacent {n} : Vertex n → Vertex n → Prop
  | .inl _, .inl _ => False
  | .inl h, .inr (p,u) => attachment h p u
  | .inr (p,u), .inl h => attachment h p u
  | .inr (p,u), .inr (q,v) => p = q ∧ inside u v

instance (u v : Fin 5) : Decidable (inside u v) := by unfold inside; infer_instance

instance {n} : DecidableRel (@adjacent n) := by
  intro x y
  cases x <;> cases y <;> simp only [adjacent, attachment, inside] <;> infer_instance

def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj := adjacent
  symm := by
    intro x y h
    cases x <;> cases y <;> try exact h
    exact ⟨h.1.symm, (by decide : ∀ u v, inside u v → inside v u) _ _ h.2⟩
  loopless := by
    rintro (h | ⟨p,u⟩)
    · exact id
    · exact fun h => h.2.1 rfl

instance (n) : DecidableRel (graph n).Adj := inferInstanceAs (DecidableRel adjacent)

theorem order (n) : Fintype.card (Vertex n) = 11 * (n+1) := by
  simp [Vertex, Block, Hub, Fintype.card_sum, Fintype.card_prod]; omega

theorem connected (n) : (graph n).Connected := by
  let G := graph n
  have within (p : Block n) (u v : Fin 5) : G.Reachable (.inr (p,u)) (.inr (p,v)) := by
    have toTwo (a : Fin 5) : G.Reachable (.inr (p,a)) (.inr (p,2)) := by
      by_cases h : a = 2
      · subst a; exact Reachable.rfl
      · exact (show G.Adj (.inr (p,a)) (.inr (p,2)) from ⟨rfl, (by decide : ∀ a, a ≠ 2 → inside a 2) a h⟩).reachable
    exact (toTwo u).trans (toTwo v).symm
  have start (p : Block n) : G.Adj (.inl p.1) (.inr (p,0)) := Or.inl ⟨rfl,rfl⟩
  have finish (p : Block n) : G.Adj (.inr (p,1)) (.inl (p.1+1)) := Or.inr ⟨rfl,rfl⟩
  have step (i : Hub n) : G.Reachable (.inl i) (.inl (i+1)) := by
    let p : Block n := (i,false)
    exact (start p).reachable.trans ((within p 0 1).trans (finish p).reachable)
  have allHubs (k : ℕ) : G.Reachable (.inl 0) (.inl (k : Hub n)) := by
    induction k with
    | zero => exact Reachable.rfl
    | succ k ih => simpa only [Nat.cast_succ] using ih.trans (step k)
  have reach (x : Vertex n) : G.Reachable (.inl 0) x := by
    rcases x with i | ⟨p,u⟩
    · exact_mod_cast allHubs i.val
    · have h : G.Reachable (.inl 0) (.inl p.1) := by exact_mod_cast allHubs p.1.val
      exact h.trans ((start p).reachable.trans (within p 0 u))
  exact ⟨fun x y => (reach x).symm.trans (reach y)⟩

theorem regular (n) : (graph n).IsRegularOfDegree 4 := by
  intro x
  rcases x with i | ⟨p,u⟩
  · let v (j : Hub n) (b : Bool) (u : Fin 5) : Vertex n := .inr ((j,b),u)
    have neighbors : (graph n).neighborFinset (.inl i) =
        {v i false 0, v i true 0, v (i-1) false 1, v (i-1) true 1} := by
      ext y
      rcases y with h | ⟨⟨j,b⟩,u⟩
      · simp [mem_neighborFinset,graph,adjacent,v]
      · cases b <;> simp [mem_neighborFinset,graph,adjacent,attachment,v,
          eq_sub_iff_add_eq, eq_comm (a := i)]
    change ((graph n).neighborFinset (.inl i)).card = 4
    rw [neighbors]
    simp [v]
  · let inner := univ.filter (inside u)
    let tag : Fin 5 ↪ Vertex n := ⟨fun j => .inr (p,j), fun _ _ h => (Prod.mk.inj (Sum.inr.inj h)).2⟩
    let outer : Finset (Vertex n) :=
      if u = 0 then {.inl p.1} else if u = 1 then {.inl (p.1+1)} else ∅
    have neighbors : (graph n).neighborFinset (.inr (p,u)) = outer ∪ inner.map tag := by
      ext y
      rcases y with h | ⟨q,j⟩ <;> by_cases h0 : u = 0 <;> by_cases h1 : u = 1 <;>
        simp_all [mem_neighborFinset,graph,adjacent,attachment,outer,inner,tag,eq_comm,and_comm]
    have dis : Disjoint outer (inner.map tag) := by
      apply disjoint_left.mpr
      intro y hy hz
      obtain ⟨j,_,rfl⟩ := mem_map.mp hz
      unfold outer at hy
      split at hy <;> simp_all [tag]
      split at hy <;> simp_all [tag]
    change ((graph n).neighborFinset (.inr (p,u))).card = 4
    rw [neighbors,card_union_of_disjoint dis,card_map]
    have count : ∀ t : Fin 5, (univ.filter (inside t)).card = if t = 0 ∨ t = 1 then 3 else 4 := by decide
    change outer.card + (univ.filter (inside u)).card = 4
    rw [count]
    by_cases h0 : u = 0 <;> by_cases h1 : u = 1 <;> simp_all [outer]

end RegularHarmonic595
