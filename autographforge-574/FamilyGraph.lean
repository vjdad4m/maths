import Row1078
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace EulerDom574
open Finset SimpleGraph TriangleMatching1078
variable (n : ℕ)
/-- There are n+2 core pairs. The two Boolean values are the endpoints. -/
abbrev Key := Fin (n+2)
abbrev Core := Key n × Bool
abbrev Cross := {p : Core n × Core n // p.1.1 ≠ p.2.1}
abbrev Outside := Key n ⊕ (Cross n × Fin (2*(n+2)))
abbrev Vtx := Core n ⊕ Outside n

variable {n}
def mate (x : Core n) : Core n := (x.1,!x.2)
@[simp] theorem mate_mate (x : Core n) : mate (mate x) = x := by cases x; simp [mate]
theorem mate_ne (x : Core n) : mate x ≠ x := by rcases x with ⟨i,b⟩; cases b <;> simp [mate]

/-- One extra outside vertex per index restores even degree at every core. -/
def left : Outside n → Core n
  | .inl i => (i,false)
  | .inr (p,_) => p.val.1

def right : Outside n → Core n
  | .inl i => (i+1,true)
  | .inr (p,_) => p.val.2

theorem different (o : Outside n) : (left o).1 ≠ (right o).1 := by
  rcases o with i|⟨p,t⟩
  · change i ≠ i+1
    intro eq
    have h : (0 : Key n) = 1 := add_left_cancel (show i+0=i+1 by rw [add_zero]; exact eq)
    have := congrArg Fin.val h
    simp at this
  · exact p.property

def incident (x : Core n) (o : Outside n) := x=left o ∨ x=right o
instance (x : Core n) (o : Outside n) : Decidable (incident x o) := inferInstanceAs (Decidable (_ ∨ _))

def adj : Vtx n → Vtx n → Prop
  | .inl x, .inl y => y=mate x
  | .inl x, .inr o | .inr o, .inl x => incident x o
  | .inr _, .inr _ => False

instance : DecidableRel (@adj n) := by
  intro a b; cases a <;> cases b <;> dsimp [adj] <;> infer_instance

variable (n) in
def graph : SimpleGraph (Vtx n) where
  Adj := adj
  symm := by
    rintro (x|o) (y|p) h
    · change x = mate y
      change y = mate x at h
      simp [h]
    all_goals exact h
  loopless := by
    rintro (x|o)
    · exact (mate_ne x).symm
    · exact id

instance : DecidableRel (graph n).Adj := inferInstanceAs (DecidableRel adj)

/-- Matched cores never share an outside neighbor. -/
theorem no_common (x : Core n) (o : Outside n) :
    incident x o → ¬ incident (mate x) o := by
  rintro (rfl|rfl) (h|h)
  · exact mate_ne _ h
  · exact different o (show (mate (left o)).1 = (right o).1 from congrArg Prod.fst h)
  · exact different o (congrArg Prod.fst h).symm
  · exact mate_ne _ h

theorem triangle_free : TriangleFree (graph n) := by
  rintro (x|o) (y|p) (z|q) h₁ h₂ h₃
  · change y=mate x at h₁
    change z=mate y at h₂
    change x=mate z at h₃
    subst y; subst z; simp at h₃
    exact mate_ne x h₃.symm
  · change y=mate x at h₁
    subst y; exact no_common x q h₃ h₂
  · change x=mate z at h₃
    subst x; exact no_common z p h₂ h₁
  · exact h₂
  · change z=mate y at h₂
    subst z; exact no_common y o h₁ h₃
  · exact h₃
  · exact h₁
  · exact h₁

theorem connected : (graph n).Connected := by
  have coreReach (x y : Core n) : (graph n).Reachable (.inl x) (.inl y) := by
    by_cases same : x.1=y.1
    · rcases x with ⟨i,a⟩; rcases y with ⟨j,b⟩
      change i=j at same
      subst j
      cases a <;> cases b
      all_goals first | exact Reachable.rfl | apply Adj.reachable; rfl
    · let o : Outside n := .inr (⟨(x,y),same⟩,0)
      have a : (graph n).Adj (.inl x) (.inr o) := Or.inl rfl
      have b : (graph n).Adj (.inr o) (.inl y) := Or.inr rfl
      exact a.reachable.trans b.reachable
  have toward (x : Vtx n) : (graph n).Reachable x (.inl (0,false)) := by
    rcases x with c|o
    · exact coreReach _ _
    · exact ((show (graph n).Adj (.inr o) (.inl (left o)) from Or.inl rfl).reachable).trans (coreReach _ _)
  exact ⟨fun u v => (toward u).trans (toward v).symm⟩

private theorem degree_sum (v : Vtx n) : (graph n).degree v =
    ∑ w : Vtx n, if adj v w then 1 else 0 := by
  unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
  rw [sum_boole,Set.toFinset_setOf]
  rfl

theorem outside_degree (o : Outside n) : (graph n).degree (.inr o) = 2 := by
  classical
  rw [degree_sum,Fintype.sum_sum_type]
  have ne : left o ≠ right o := fun h => different o (congrArg Prod.fst h)
  have counted (c : Core n) : (if incident c o then 1 else 0 : ℕ) =
      (if c=left o then 1 else 0) + (if c=right o then 1 else 0) := by
    by_cases a : c=left o <;> by_cases b : c=right o <;> simp_all [incident]
  simp [adj,counted,sum_add_distrib]

theorem core_degree (x : Core n) : ∃ t : ℕ, (graph n).degree (.inl x) = 2+2*t := by
  classical
  rw [degree_sum,Fintype.sum_sum_type,Fintype.sum_sum_type]
  have single : (∑ i : Key n, if incident x (.inl i) then 1 else 0 : ℕ) = 1 := by
    rcases x with ⟨j,b⟩
    cases b
    · simp [incident,left,right]
    · have eq (i : Key n) : j = i+1 ↔ i = j-1 := by rw [eq_sub_iff_add_eq,eq_comm]
      simp [incident,left,right,eq]
  let weight (p : Cross n) : ℕ := if x=p.val.1 ∨ x=p.val.2 then n+2 else 0
  refine ⟨∑ p,weight p,?_⟩
  have copies (p : Cross n) : (∑ i : Fin (2*(n+2)), if incident x (.inr (p,i)) then 1 else 0 : ℕ)
      = 2*weight p := by by_cases h : x=p.val.1 ∨ x=p.val.2 <;> simp [incident,left,right,weight,h]
  simp only [adj,single]
  rw [show (∑ c : Core n, if c=mate x then 1 else 0 : ℕ) = 1 by simp]
  rw [Fintype.sum_prod_type]
  simp only [copies,← mul_sum]
  omega

theorem all_even (v : Vtx n) : Even ((graph n).degree v) := by
  rcases v with x|o
  · obtain ⟨t,h⟩ := core_degree x
    exact ⟨t+1,by omega⟩
  · rw [outside_degree]; decide

theorem nontrivial : 2 ≤ Fintype.card (Vtx n) := by
  have h := Fintype.card_le_of_injective (@Sum.inl (Core n) (Outside n)) Sum.inl_injective
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
  change 2 ≤ Fintype.card (Core n ⊕ Outside n)
  omega
end EulerDom574
