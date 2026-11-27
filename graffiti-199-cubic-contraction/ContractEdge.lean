import TreeBudget

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

structure ContractedEdge (G : SimpleGraph V) where
  a : V
  b : V
  edge : G.Adj a b

namespace ContractedEdge

variable (E : ContractedEdge G)

abbrev Other := {x : V // x ≠ E.a ∧ x ≠ E.b}

abbrev Vertex := Option E.Other

def graph : SimpleGraph E.Vertex where
  Adj
    | none, none => False
    | none, some x => G.Adj E.a x.val ∨ G.Adj E.b x.val
    | some x, none => G.Adj E.a x.val ∨ G.Adj E.b x.val
    | some x, some y => G.Adj x.val y.val
  symm := by
    intro x y e
    cases x <;> cases y
    · exact e
    · exact e
    · exact e
    · exact e.symm
  loopless := by
    intro x
    cases x with
    | none => exact id
    | some x => exact G.loopless x.val

def representative : E.Vertex ↪ V where
  toFun
    | none => E.a
    | some x => x.val
  inj' := by
    intro x y h
    rcases x with (_|x) <;> rcases y with (_|y)
    · rfl
    · exact (y.property.1 h.symm).elim
    · exact (x.property.1 h).elim
    · exact congrArg some (Subtype.ext h)

@[simp] theorem rep_none : E.representative none = E.a := rfl
@[simp] theorem rep_some (x : E.Other) : E.representative (some x) = x.val := rfl

theorem rep_ne_b (x : E.Vertex) : E.representative x ≠ E.b := by
  cases x
  · exact E.edge.ne
  · exact (‹E.Other›).property.2

variable [DecidableEq V]

def project (x : V) : E.Vertex :=
  if h : x ≠ E.a ∧ x ≠ E.b then some ⟨x,h⟩ else none

@[simp] theorem project_a : E.project E.a = none := dif_neg (fun h => h.1 rfl)

@[simp] theorem project_b : E.project E.b = none := dif_neg (fun h => h.2 rfl)

theorem project_of_other (x : V) (h : x ≠ E.a ∧ x ≠ E.b) :
    E.project x = some ⟨x,h⟩ :=
  dif_pos h

@[simp] theorem project_rep (x : E.Vertex) : E.project (E.representative x) = x := by
  cases x with
  | none => exact E.project_a
  | some x => exact E.project_of_other _ x.property

theorem rep_project (x : V) (hx : x ≠ E.b) : E.representative (E.project x) = x := by
  by_cases ha : x = E.a
  · subst x
    simp
  · rw [E.project_of_other _ ⟨ha,hx⟩,E.rep_some]

theorem project_none_iff (x : V) : E.project x = none ↔ x = E.a ∨ x = E.b := by
  by_cases h : x ≠ E.a ∧ x ≠ E.b
  · rw [E.project_of_other _ h]
    simp [h.1,h.2]
  · have none : E.project x = none := dif_neg h
    rw [none]
    tauto

theorem project_adj_or_eq {x y : V} (xy : G.Adj x y) :
    E.graph.Adj (E.project x) (E.project y) ∨ E.project x = E.project y := by
  by_cases hx : x ≠ E.a ∧ x ≠ E.b
  · rw [E.project_of_other _ hx]
    by_cases hy : y ≠ E.a ∧ y ≠ E.b
    · rw [E.project_of_other _ hy]
      exact Or.inl xy
    · have e : E.project y = none := dif_neg hy
      rw [e]
      apply Or.inl
      change G.Adj E.a x ∨ G.Adj E.b x
      rcases (E.project_none_iff y).mp e with q|q
      · exact Or.inl (q ▸ xy.symm)
      · exact Or.inr (q ▸ xy.symm)
  · have e : E.project x = none := dif_neg hx
    rw [e]
    by_cases hy : y ≠ E.a ∧ y ≠ E.b
    · rw [E.project_of_other _ hy]
      apply Or.inl
      change G.Adj E.a y ∨ G.Adj E.b y
      rcases (E.project_none_iff x).mp e with q|q
      · exact Or.inl (q ▸ xy)
      · exact Or.inr (q ▸ xy)
    · have e' : E.project y = none := dif_neg hy
      exact Or.inr e'.symm

variable [Fintype V]

theorem card_vertex : Fintype.card E.Vertex + 1 = Fintype.card V := by
  let f : E.Vertex → {x : V // x ≠ E.b} := fun x => ⟨E.representative x,E.rep_ne_b x⟩
  have bij : Function.Bijective f :=
    ⟨fun _ _ h => E.representative.injective (congrArg Subtype.val h),
      fun x => ⟨E.project x.val,Subtype.ext (E.rep_project _ x.prop)⟩⟩
  rw [Fintype.card_congr (Equiv.ofBijective f bij)]
  have h := Fintype.card_subtype_compl (fun x : V => x = E.b)
  have one : Fintype.card {x : V // x = E.b} = 1 := Fintype.card_unique
  rw [one] at h
  change Fintype.card {x : V // x ≠ E.b} = Fintype.card V - 1 at h
  have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨E.b⟩
  omega

end ContractedEdge

end Graffiti199Depleted
