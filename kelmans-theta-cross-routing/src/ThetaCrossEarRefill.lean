import ThetaCrossEarPatch
import ThetaAdjacentEarRefill
import ThetaFiveModes
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaCrossEarRefill
open SquareCap (FactorOn)
open ThetaCrossEarPatch (Local mapped_mode)
noncomputable section

variable {V : Type*}

open ThetaAdjacentEarRefill (Out In Shape liveFin mem_live)

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

open ThetaFiveModes (Lane)

/-- The cross routing groups the two original contacts, and groups
the two released replacement contacts. -/
def firstSite (s : Bool) : Fin 9 := if s then 8 else 1
def nextSite (s : Bool) : Fin 9 := if s then 7 else 4

def Allowed (H : SimpleGraph (V⊕Fin 9)) (p : Lane ↪ V)
    (s : Bool) (m : Fin 3) (a b : V) : Prop :=
  (m=0 ∧ a=p (s,false) ∧ b=p (s,true) ∧
    H.Adj (In (firstSite s)) (Out a) ∧ H.Adj (In (nextSite s)) (Out b)) ∨
  (m=1 ∧ a=p (s,false) ∧ H.Adj (In (firstSite s)) (Out a) ∧ H.Adj (Out a) (Out b)) ∨
  (m=2 ∧ a=p (s,true) ∧ H.Adj (In (nextSite s)) (Out a) ∧ H.Adj (Out a) (Out b))

private theorem used_left {H : SimpleGraph (V⊕Fin 9)} {p : Lane↪V}
    (v : Fin 4↪V) {m : Fin 3} (a : Allowed H p false m (v 0) (v 1))
    {i : Bool} {l : Local} (h : ThetaCrossEarPatch.usedPort 8 9 m i=some l) :
    emb v l=Out (p (false,i)) := by
  rcases a with ⟨rfl,a,b,_,_⟩|⟨rfl,a,_,_⟩|⟨rfl,a,_,_⟩ <;> cases i <;>
    simp [ThetaCrossEarPatch.usedPort] at h
  all_goals subst l; first | simp [a,b] | simp [a]

private theorem used_right {H : SimpleGraph (V⊕Fin 9)} {p : Lane↪V}
    (v : Fin 4↪V) {n : Fin 3} (b : Allowed H p true n (v 2) (v 3))
    {i : Bool} {l : Local} (h : ThetaCrossEarPatch.usedPort 10 11 n i=some l) :
    emb v l=Out (p (true,i)) := by
  rcases b with ⟨rfl,a,b,_,_⟩|⟨rfl,a,_,_⟩|⟨rfl,a,_,_⟩ <;> cases i <;>
    simp [ThetaCrossEarPatch.usedPort] at h
  all_goals subst l; first | simp [a,b] | simp [a]

private theorem cross_edge_ok {H : SimpleGraph (V⊕Fin 9)} {p : Lane↪V}
    (v : Fin 4↪V) {m n : Fin 3}
    (a : Allowed H p false m (v 0) (v 1))
    (b : Allowed H p true n (v 2) (v 3))
    (cross : ∀ i : Bool,H.Adj (Out (p (false,i))) (Out (p (true,i))))
    {i : Bool} {x y : Local} (h : (x,y)∈ThetaCrossEarPatch.cross (m,n) i) :
    H.Adj (emb v x) (emb v y) := by
  unfold ThetaCrossEarPatch.cross at h
  dsimp only at h
  cases u : ThetaCrossEarPatch.usedPort 8 9 m i with
  | none => simp [u] at h
  | some l =>
    cases w : ThetaCrossEarPatch.usedPort 10 11 n i with
    | none => simp [u,w] at h
    | some r =>
      simp [u,w] at h
      rcases h with ⟨rfl,rfl⟩
      rw [used_left v a u,used_right v b w]
      exact cross i

private theorem edges_ok {H : SimpleGraph (V⊕Fin 9)} {p : Lane↪V}
    (sh : Shape H) (ear : H.Adj (In 7) (In 8))
    (cross : ∀ i : Bool,H.Adj (Out (p (false,i))) (Out (p (true,i))))
    (v : Fin 4↪V) {m n : Fin 3}
    (a : Allowed H p false m (v 0) (v 1))
    (b : Allowed H p true n (v 2) (v 3)) :
    ∀ x y,(x,y)∈ThetaCrossEarPatch.edges (m,n) → H.Adj (emb v x) (emb v y) := by
  intro x y e
  simp only [ThetaCrossEarPatch.edges,List.mem_append] at e
  rcases e with (((c|c)|c)|c)|c
  · simp [ThetaCrossEarPatch.core] at c
    rcases c with h|h|h|h|h|h|h|h|h <;> have hx := h.1 <;> have hy := h.2 <;>
      subst x <;> subst y
    all_goals first | simpa using sh.e01 | simpa using sh.e12 | simpa using sh.e23 |
      simpa using sh.e34 | simpa using sh.e45 | simpa using sh.e50 |
      simpa using sh.e27 | simpa using sh.e58 | simpa using ear
  · rcases a with ⟨rfl,_,_,ha,hb⟩|⟨rfl,_,ha,hb⟩|⟨rfl,_,ha,hb⟩
    all_goals
      simp [ThetaCrossEarPatch.modeEdges] at c
      rcases c with h|h <;> have hx := h.1 <;> have hy := h.2 <;> subst x <;> subst y
      all_goals first | simpa [firstSite,nextSite] using ha | simpa [firstSite,nextSite] using hb
  · rcases b with ⟨rfl,_,_,ha,hb⟩|⟨rfl,_,ha,hb⟩|⟨rfl,_,ha,hb⟩
    all_goals
      simp [ThetaCrossEarPatch.modeEdges] at c
      rcases c with h|h <;> have hx := h.1 <;> have hy := h.2 <;> subst x <;> subst y
      all_goals first | simpa [firstSite,nextSite] using ha | simpa [firstSite,nextSite] using hb
  · exact cross_edge_ok v a b cross c
  · exact cross_edge_ok v a b cross c

/-- The finite nine-mode certificate lifts to arbitrary distinct exterior
vertices. Edges are used only between contacts that a cap tile actually used. -/
theorem refill [DecidableEq V] {H : SimpleGraph (V⊕Fin 9)} {p : Lane↪V}
    (sh : Shape H) (ear : H.Adj (In 7) (In 8))
    (cross : ∀ i : Bool,H.Adj (Out (p (false,i))) (Out (p (true,i))))
    (v : Fin 4↪V) {m n : Fin 3}
    (a : Allowed H p false m (v 0) (v 1))
    (b : Allowed H p true n (v 2) (v 3)) :
    FactorOn H (liveFin V ∪ {Out (v 0),Out (v 1),Out (v 2),Out (v 3)}) := by
  change FactorOn H (liveFin V ∪ support v)
  exact (image_emb v) ▸ mapped_mode (m,n) (emb v) (edges_ok sh ear cross v a b)

#print axioms refill
end
end KelmansCactus.AtomicBridge.ThetaCrossEarRefill
