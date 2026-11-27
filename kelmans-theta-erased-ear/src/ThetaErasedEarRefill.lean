import ThetaErasedEarPatch
import ThetaAdjacentEarRefill
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaErasedEarRefill
open SquareCap (FactorOn)
open ThetaErasedEarPatch (Site lift_shared lift_separate)
open ThetaAdjacentEarRefill (Out In Shape liveFin mem_live)
noncomputable section

variable {V : Type*}

def midSite (s : Fin 3) : Fin 9 := if s=0 then 1 else 8
def firstSite (s : Fin 3) : Fin 9 := if s=2 then 1 else 4
def lastSite (s : Fin 3) : Fin 9 := if s=2 then 4 else 7

def LeafAllowed (H : SimpleGraph (V⊕Fin 9)) (s m : Fin 3) (a b : V) : Prop :=
  (m=0 ∧ H.Adj (In (firstSite s)) (Out a) ∧ H.Adj (In (lastSite s)) (Out b)) ∨
  (m=1 ∧ H.Adj (In (firstSite s)) (Out a) ∧ H.Adj (Out a) (Out b)) ∨
  (m=2 ∧ H.Adj (In (lastSite s)) (Out a) ∧ H.Adj (Out a) (Out b))

private def code (i : Fin 8) : Fin 9 :=
  if h : i.val<6 then ⟨i.val,by omega⟩ else ⟨i.val+1,by have li:=i.isLt; omega⟩

private theorem code_inj : Function.Injective code := by
  have e : ∀ x y : Fin 8, code x=code y→x=y := by decide
  exact e

private theorem code_inv : ∀ j : Fin 9, j≠6 ↔ ∃ i : Fin 8,code i=j := by decide

private def put {n : ℕ} (v : Fin n ↪ V) (i : Site n) : V⊕Fin 9 :=
  if h : i.val<8 then In (code ⟨i.val,h⟩)
  else Out (v ⟨i.val-8,by have hi:=i.isLt; omega⟩)

private theorem put_inj {n : ℕ} (v : Fin n↪V) : Function.Injective (put v) := by
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
    have e' := congrArg (fun x : Fin n=>x.val) e
    dsimp at e'
    omega

private def emb {n : ℕ} (v : Fin n↪V) : Site n↪(V⊕Fin 9) := ⟨put v,put_inj v⟩

@[simp] private theorem e1_0 (v : Fin 1↪V) : emb v 0 = In 0 := rfl

@[simp] private theorem e1_1 (v : Fin 1↪V) : emb v 1 = In 1 := rfl

@[simp] private theorem e1_2 (v : Fin 1↪V) : emb v 2 = In 2 := rfl

@[simp] private theorem e1_3 (v : Fin 1↪V) : emb v 3 = In 3 := rfl

@[simp] private theorem e1_4 (v : Fin 1↪V) : emb v 4 = In 4 := rfl

@[simp] private theorem e1_5 (v : Fin 1↪V) : emb v 5 = In 5 := rfl

@[simp] private theorem e1_6 (v : Fin 1↪V) : emb v 6 = In 7 := rfl

@[simp] private theorem e1_7 (v : Fin 1↪V) : emb v 7 = In 8 := rfl

@[simp] private theorem e1_8 (v : Fin 1↪V) : emb v 8 = Out (v 0) := rfl

@[simp] private theorem e4_0 (v : Fin 4↪V) : emb v 0 = In 0 := rfl

@[simp] private theorem e4_1 (v : Fin 4↪V) : emb v 1 = In 1 := rfl

@[simp] private theorem e4_2 (v : Fin 4↪V) : emb v 2 = In 2 := rfl

@[simp] private theorem e4_3 (v : Fin 4↪V) : emb v 3 = In 3 := rfl

@[simp] private theorem e4_4 (v : Fin 4↪V) : emb v 4 = In 4 := rfl

@[simp] private theorem e4_5 (v : Fin 4↪V) : emb v 5 = In 5 := rfl

@[simp] private theorem e4_6 (v : Fin 4↪V) : emb v 6 = In 7 := rfl

@[simp] private theorem e4_7 (v : Fin 4↪V) : emb v 7 = In 8 := rfl

@[simp] private theorem e4_8 (v : Fin 4↪V) : emb v 8 = Out (v 0) := rfl

@[simp] private theorem e4_9 (v : Fin 4↪V) : emb v 9 = Out (v 1) := rfl

@[simp] private theorem e4_10 (v : Fin 4↪V) : emb v 10 = Out (v 2) := rfl

@[simp] private theorem e4_11 (v : Fin 4↪V) : emb v 11 = Out (v 3) := rfl

private def supp [DecidableEq V] {n : ℕ} (v : Fin n↪V) : Finset (V⊕Fin 9) :=
  (univ : Finset (Fin n)).map (⟨fun j=>Out (v j),fun _ _ h=>v.injective (Sum.inl_injective h)⟩)

private theorem image_emb [DecidableEq V] {n : ℕ} (v : Fin n↪V) :
    (univ : Finset (Site n)).map (emb v) = liveFin V ∪ supp v := by
  ext x
  constructor
  · intro h
    obtain ⟨k,_,rfl⟩ := mem_map.mp h
    by_cases g : k.val<8
    · apply mem_union_left
      simp only [emb,Function.Embedding.coeFn_mk,put,dif_pos g,mem_live]
      exact (code_inv _).mpr ⟨_,rfl⟩
    · apply mem_union_right
      simp only [emb,Function.Embedding.coeFn_mk,put,dif_neg g]
      exact mem_map.mpr ⟨_,mem_univ _,rfl⟩
  · intro h
    rcases mem_union.mp h with h|h
    · obtain ⟨j,jn,rfl⟩ := mem_map.mp h
      obtain ⟨k,rfl⟩ := (code_inv j).mp (mem_erase.mp jn).1
      let t : Site n := ⟨k.val,by have hl:=k.isLt; omega⟩
      refine mem_map.mpr ⟨t,mem_univ _,?_⟩
      have small : t.val<8 := k.isLt
      simp [emb,put,small,t]
    · obtain ⟨j,_,rfl⟩ := mem_map.mp h
      let t : Site n := ⟨j.val+8,by have hl:=j.isLt; omega⟩
      refine mem_map.mpr ⟨t,mem_univ _,?_⟩
      have ng : ¬t.val<8 := by simp [t]
      have same : t.val-8=j.val := by simp [t]
      simp [emb,put,ng,same]

private theorem core1 {H : SimpleGraph (V⊕Fin 9)} (sh : Shape H)
    (v : Fin 1↪V)
    (x y : Site 1) (h : (x,y)∈ThetaErasedEarPatch.core 1) :
    H.Adj (emb v x) (emb v y) := by
  simp [ThetaErasedEarPatch.core] at h
  rcases h with e|e|e|e|e|e|e|e <;> have hx := e.1 <;> have hy := e.2 <;>
    subst x <;> subst y
  all_goals first | simpa using sh.e01 | simpa using sh.e12 | simpa using sh.e23 |
    simpa using sh.e34 | simpa using sh.e45 | simpa using sh.e50 |
    simpa using sh.e27 | simpa using sh.e58

private theorem core4 {H : SimpleGraph (V⊕Fin 9)} (sh : Shape H)
    (v : Fin 4↪V)
    (x y : Site 4) (h : (x,y)∈ThetaErasedEarPatch.core 4) :
    H.Adj (emb v x) (emb v y) := by
  simp [ThetaErasedEarPatch.core] at h
  rcases h with e|e|e|e|e|e|e|e <;> have hx := e.1 <;> have hy := e.2 <;>
    subst x <;> subst y
  all_goals first | simpa using sh.e01 | simpa using sh.e12 | simpa using sh.e23 |
    simpa using sh.e34 | simpa using sh.e45 | simpa using sh.e50 |
    simpa using sh.e27 | simpa using sh.e58

theorem refill_shared [DecidableEq V] {H : SimpleGraph (V⊕Fin 9)} (sh : Shape H)
    (s : Bool) (a : V)
    (edge : H.Adj (In (if s then 4 else 1)) (Out a)) :
    FactorOn H (liveFin V ∪ {Out a}) := by
  let v : Fin 1↪V := ⟨fun _=>a,fun _ _ _=>Subsingleton.elim _ _⟩
  have sup : supp v={Out a} := by
    ext z; simp [supp,v]
  rw [←sup,←image_emb]
  apply lift_shared s (emb v)
  intro x y h
  simp [ThetaErasedEarPatch.sharedEdges] at h
  rcases h with h|⟨hx,hy⟩
  · exact core1 sh v x y h
  subst x
  subst y
  cases s <;> simpa [v] using edge

theorem refill_separate [DecidableEq V] {H : SimpleGraph (V⊕Fin 9)} (sh : Shape H)
    (s m : Fin 3)
    (v : Fin 4↪V)
    (wire : H.Adj (In (midSite s)) (Out (v 0)))
    (edge : H.Adj (Out (v 0)) (Out (v 1)))
    (leaf : LeafAllowed H s m (v 2) (v 3)) :
    FactorOn H (liveFin V ∪ {Out (v 0),Out (v 1),Out (v 2),Out (v 3)}) := by
  have sup : supp v={Out (v 0),Out (v 1),Out (v 2),Out (v 3)} := by
    ext z
    constructor
    · intro h
      obtain ⟨i,_,rfl⟩ := mem_map.mp h
      fin_cases i <;> simp
    · intro h
      simp only [mem_insert,mem_singleton] at h
      rcases h with rfl|rfl|rfl|rfl
      · exact mem_map.mpr ⟨0,mem_univ _,rfl⟩
      · exact mem_map.mpr ⟨1,mem_univ _,rfl⟩
      · exact mem_map.mpr ⟨2,mem_univ _,rfl⟩
      · exact mem_map.mpr ⟨3,mem_univ _,rfl⟩
  rw [←sup,←image_emb]
  apply lift_separate s m (emb v)
  intro x y h
  simp only [ThetaErasedEarPatch.separateEdges,List.mem_append] at h
  rcases h with (h|h)|h
  · exact core4 sh v x y h
  · simp at h
    rcases h with ⟨hx,hy⟩|⟨hx,hy⟩ <;> subst x <;> subst y
    · fin_cases s <;> simpa [ThetaErasedEarPatch.middleSite,midSite] using wire
    · simpa using edge
  rcases leaf with ⟨rfl,h1,h2⟩|⟨rfl,h1,h2⟩|⟨rfl,h1,h2⟩
  all_goals
    fin_cases s <;> simp [ThetaErasedEarPatch.firstSite,ThetaErasedEarPatch.lastSite] at h
    all_goals
      rcases h with ⟨hx,hy⟩|⟨hx,hy⟩ <;> subst x <;> subst y
      all_goals first | simpa [firstSite,lastSite] using h1 | simpa [firstSite,lastSite] using h2

#print axioms refill_shared
#print axioms refill_separate
end
end KelmansCactus.AtomicBridge.ThetaErasedEarRefill
