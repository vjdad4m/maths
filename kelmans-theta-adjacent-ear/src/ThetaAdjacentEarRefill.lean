import ThetaAdjacentEarPatch
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAdjacentEarRefill
open SquareCap (FactorOn)
open ThetaAdjacentEarPatch (Local mapped_mode)
noncomputable section

variable {V : Type*}

abbrev Out (v : V) : V⊕Fin 9 := .inl v
abbrev In (v : Fin 9) : V⊕Fin 9 := .inr v

/-- Only the surviving ring and the two incidences to the absorbed
contacts are required. The absorbed edge may itself be absent. -/
structure Shape (H : SimpleGraph (V⊕Fin 9)) : Prop where
  e01 : H.Adj (In 0) (In 1)
  e12 : H.Adj (In 1) (In 2)
  e23 : H.Adj (In 2) (In 3)
  e34 : H.Adj (In 3) (In 4)
  e45 : H.Adj (In 4) (In 5)
  e50 : H.Adj (In 5) (In 0)
  e27 : H.Adj (In 2) (In 7)
  e58 : H.Adj (In 5) (In 8)

def firstSite (s : Bool) : Fin 9 := if s then 4 else 1
def nextSite (s : Bool) : Fin 9 := if s then 7 else 8

/-- For a chosen leaf mode the replacement needs precisely the
wires that its cap tile used, plus its actual exterior edge. -/
def Allowed (H : SimpleGraph (V⊕Fin 9)) (s : Bool) (m : Fin 3) (a b : V) : Prop :=
  (m=0 ∧ H.Adj (In (firstSite s)) (Out a) ∧ H.Adj (In (nextSite s)) (Out b)) ∨
  (m=1 ∧ H.Adj (In (firstSite s)) (Out a) ∧ H.Adj (Out a) (Out b)) ∨
  (m=2 ∧ H.Adj (In (nextSite s)) (Out a) ∧ H.Adj (Out a) (Out b))

def liveFin (V : Type*) [DecidableEq V] : Finset (V⊕Fin 9) :=
  ((univ : Finset (Fin 9)).erase 6).map ⟨Sum.inr,Sum.inr_injective⟩

theorem mem_live {V : Type*} [DecidableEq V] (i : Fin 9) :
    In (V:=V) i ∈ liveFin V ↔ i≠6 := by simp [liveFin,mem_map]

private def code (i : Fin 8) : Fin 9 :=
  if h : i.val<6 then ⟨i.val,by omega⟩ else ⟨i.val+1,by have li:=i.isLt; omega⟩

private theorem code_inj : Function.Injective code := by
  have e : ∀ x y : Fin 8, code x=code y→x=y := by decide
  exact e

private theorem code_inv : ∀ j : Fin 9, j≠6 ↔ ∃ i : Fin 8,code i=j := by decide

private def put (v : Fin 4 ↪ V) (i : Local) : V⊕Fin 9 :=
  if h : i.val<8 then In (code ⟨i.val,h⟩)
  else Out (v ⟨i.val-8,by have hi:=i.isLt; omega⟩)

private theorem put_inj (v : Fin 4↪V) : Function.Injective (put v) := by
  intro i j h
  by_cases hi : i.val<8 <;> by_cases hj : j.val<8
  · simp only [put,dif_pos hi,dif_pos hj] at h
    have e := code_inj (Sum.inr_injective h)
    exact Fin.ext (congrArg (fun x : Fin 8=>x.val) e)
  · simp only [put,dif_pos hi,dif_neg hj] at h
    exact Sum.noConfusion h
  · simp only [put,dif_neg hi,dif_pos hj] at h
    exact Sum.noConfusion h
  · simp only [put,dif_neg hi,dif_neg hj] at h
    have e := v.injective (Sum.inl_injective h)
    apply Fin.ext
    have e' := congrArg (fun x : Fin 4=>x.val) e
    dsimp at e'
    omega

private def emb (v : Fin 4↪V) : Local↪(V⊕Fin 9) := ⟨put v,put_inj v⟩

@[simp] private theorem emb0 (v : Fin 4↪V) : emb v 0 = In 0 := by
  change put v 0 = _
  simp [put,code,show (0:Local).val<8 from by decide,show ((0:Fin 8).val)<6 from by decide]

@[simp] private theorem emb1 (v : Fin 4↪V) : emb v 1 = In 1 := by
  change put v 1 = _
  simp [put,code,show (1:Local).val<8 from by decide,show ((1:Fin 8).val)<6 from by decide]

@[simp] private theorem emb2 (v : Fin 4↪V) : emb v 2 = In 2 := by
  change put v 2 = _
  simp [put,code,show (2:Local).val<8 from by decide,show ((2:Fin 8).val)<6 from by decide]

@[simp] private theorem emb3 (v : Fin 4↪V) : emb v 3 = In 3 := by
  change put v 3 = _
  simp [put,code,show (3:Local).val<8 from by decide,show ((3:Fin 8).val)<6 from by decide]
  all_goals rfl

@[simp] private theorem emb4 (v : Fin 4↪V) : emb v 4 = In 4 := by
  change put v 4 = _
  simp [put,code,show (4:Local).val<8 from by decide,show ((4:Fin 8).val)<6 from by decide]
  all_goals rfl

@[simp] private theorem emb5 (v : Fin 4↪V) : emb v 5 = In 5 := by
  change put v 5 = _
  simp [put,code,show (5:Local).val<8 from by decide,show ((5:Fin 8).val)<6 from by decide]
  all_goals rfl

@[simp] private theorem emb6 (v : Fin 4↪V) : emb v 6 = In 7 := by
  change put v 6 = _
  simp [put,code,show (6:Local).val<8 from by decide,show ¬((6:Fin 8).val)<6 from by decide]
  all_goals rfl

@[simp] private theorem emb7 (v : Fin 4↪V) : emb v 7 = In 8 := by
  change put v 7 = _
  simp [put,code,show (7:Local).val<8 from by decide,show ¬((7:Fin 8).val)<6 from by decide]
  all_goals rfl

@[simp] private theorem emb8 (v : Fin 4↪V) : emb v 8 = Out (v 0) := by
  change put v 8 = _
  simp [put,code,show ¬(8:Local).val<8 from by decide]
  all_goals rfl

@[simp] private theorem emb9 (v : Fin 4↪V) : emb v 9 = Out (v 1) := by
  change put v 9 = _
  simp [put,code,show ¬(9:Local).val<8 from by decide]
  all_goals rfl

@[simp] private theorem emb10 (v : Fin 4↪V) : emb v 10 = Out (v 2) := by
  change put v 10 = _
  simp [put,code,show ¬(10:Local).val<8 from by decide]
  all_goals rfl

@[simp] private theorem emb11 (v : Fin 4↪V) : emb v 11 = Out (v 3) := by
  change put v 11 = _
  simp [put,code,show ¬(11:Local).val<8 from by decide]
  all_goals rfl


private def support [DecidableEq V] (v : Fin 4↪V) : Finset (V⊕Fin 9) :=
  {Out (v 0),Out (v 1),Out (v 2),Out (v 3)}

private theorem image_emb [DecidableEq V] (v : Fin 4↪V) :
    (univ : Finset Local).map (emb v) = liveFin V ∪ support v := by
  ext x
  constructor
  · intro h
    obtain ⟨k,_,rfl⟩ := mem_map.mp h
    by_cases g : k.val<8
    · apply mem_union_left
      simp only [emb,Function.Embedding.coeFn_mk,put,dif_pos g,mem_live]
      exact (code_inv _).mpr ⟨_,rfl⟩
    · apply mem_union_right
      have rg : ∀ k : Local, ¬k.val<8 → k=8∨k=9∨k=10∨k=11 := by decide
      rcases rg k g with rfl|rfl|rfl|rfl <;> simp [support]
  · intro h
    rcases mem_union.mp h with h|h
    · obtain ⟨j,jn,rfl⟩ := mem_map.mp h
      obtain ⟨k,rfl⟩ := (code_inv j).mp (mem_erase.mp jn).1
      let t : Local := ⟨k.val,by have hl:=k.isLt; omega⟩
      refine mem_map.mpr ⟨t,mem_univ _,?_⟩
      have small : t.val<8 := k.isLt
      simp [emb,put,small,t]
    · simp only [support,mem_insert,mem_singleton] at h
      rcases h with rfl|rfl|rfl|rfl
      · exact mem_map.mpr ⟨8,mem_univ _,by simp⟩
      · exact mem_map.mpr ⟨9,mem_univ _,by simp⟩
      · exact mem_map.mpr ⟨10,mem_univ _,by simp⟩
      · exact mem_map.mpr ⟨11,mem_univ _,by simp⟩

private theorem edges_ok {H : SimpleGraph (V⊕Fin 9)} (sh : Shape H)
    (v : Fin 4↪V) {m n : Fin 3}
    (a : Allowed H false m (v 0) (v 1))
    (b : Allowed H true n (v 2) (v 3)) :
    ∀ x y,(x,y)∈ThetaAdjacentEarPatch.edges (m,n) → H.Adj (emb v x) (emb v y) := by
  intro x y e
  simp only [ThetaAdjacentEarPatch.edges,List.mem_append] at e
  rcases e with (c|c)|c
  · simp [ThetaAdjacentEarPatch.core] at c
    rcases c with h|h|h|h|h|h|h|h <;> have hx := h.1 <;> have hy := h.2 <;>
      subst x <;> subst y
    all_goals first | simpa using sh.e01 | simpa using sh.e12 | simpa using sh.e23 |
      simpa using sh.e34 | simpa using sh.e45 | simpa using sh.e50 |
      simpa using sh.e27 | simpa using sh.e58
  · rcases a with ⟨rfl,ha,hb⟩|⟨rfl,ha,hb⟩|⟨rfl,ha,hb⟩
    all_goals
      simp [ThetaAdjacentEarPatch.modeEdges] at c
      rcases c with h|h <;> have hx := h.1 <;> have hy := h.2 <;> subst x <;> subst y
      all_goals first | simpa [firstSite,nextSite] using ha | simpa [firstSite,nextSite] using hb
  · rcases b with ⟨rfl,ha,hb⟩|⟨rfl,ha,hb⟩|⟨rfl,ha,hb⟩
    all_goals
      simp [ThetaAdjacentEarPatch.modeEdges] at c
      rcases c with h|h <;> have hx := h.1 <;> have hy := h.2 <;> subst x <;> subst y
      all_goals first | simpa [firstSite,nextSite] using ha | simpa [firstSite,nextSite] using hb

/-- General nine-mode lifting, including modes with a suppressed
replacement wire: only the active mode's links are assumed. -/
theorem refill [DecidableEq V] {H : SimpleGraph (V⊕Fin 9)} (sh : Shape H)
    (v : Fin 4↪V) {m n : Fin 3}
    (a : Allowed H false m (v 0) (v 1))
    (b : Allowed H true n (v 2) (v 3)) :
    FactorOn H (liveFin V ∪ {Out (v 0),Out (v 1),Out (v 2),Out (v 3)}) := by
  change FactorOn H (liveFin V ∪ support v)
  exact (image_emb v) ▸ mapped_mode (m,n) (emb v) (edges_ok sh v a b)

#print axioms refill
end
end KelmansCactus.AtomicBridge.ThetaAdjacentEarRefill
