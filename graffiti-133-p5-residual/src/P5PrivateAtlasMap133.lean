import P5PrivateAtlasRaw133
import P5CorePrivateLayers133
import NestedCorePrivateWeightedFitHelpers133

namespace Graffiti133P5PrivateAtlas
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby
  Graffiti133PrivateGeneric Graffiti133NestedWeightedCore
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem encode_five_bits :
    ∀ B : Fin 5→Bool,∃ m : Fin 32,∀ i : Fin 5,m.val.testBit i.val=B i := by decide

theorem two_steps_cases :
    ∀ i j : Fin 5,i=j ∨ Cyclic i j ∨ i+2=j ∨ j+2=i := by decide

theorem five_diagonals_exact :
    ∀ i j : Fin 5,
      (i=j → i+2≠j ∧ j+2≠i) ∧ (Cyclic i j→i+2≠j ∧ j+2≠i) ∧
      (i+2=j→j+2≠i) ∧ (j+2=i→i+2≠j) := by decide

private theorem adj_five_bits :
    ∀ i j : Fin 5,Cyclic i j ↔ CycleEdge i.val j.val=true := by decide

private theorem two_add_value (i : Fin 5) : (i+2).val=(i.val+2)%5 := by rfl

def layerTen (H : Hole G 5) (w : Fin 5→V) (a : Fin 10) : V :=
  if h : a.val<5 then H.c ⟨a.val,h⟩ else w ⟨a.val-5,by have := a.isLt; omega⟩

def layerFifteen (H : Hole G 5) (w q : Fin 5→V) (a : Fin 15) : V :=
  if h : a.val<10 then layerTen H w ⟨a.val,h⟩ else q ⟨a.val-10,by have := a.isLt; omega⟩

theorem ten_layer_fit (H : Hole G 5) (h4 : FourCycleFree G)
    (w : Fin 5→V)
    (out : ∀ i,Outside H.c (w i))
    (priv : ∀ i j,G.Adj (w i) (H.c j)↔j=i)
    (m : Fin 32) (bits : ∀ i : Fin 5,m.val.testBit i.val=decide (G.Adj (w i) (w (i+2)))) :
    ∀ a b : Fin 10,G.Adj (layerTen H w a) (layerTen H w b)↔firstEdge m.val a.val b.val=true := by
  have diag (i j : Fin 5) :
      G.Adj (w i) (w j)↔
      ((decide ((i.val+2)%5=j.val) && m.val.testBit i.val) ||
       (decide ((j.val+2)%5=i.val) && m.val.testBit j.val))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,bits]
    rw [←two_add_value,←two_add_value]
    simp only [←Fin.ext_iff]
    constructor
    · intro h
      rcases two_steps_cases i j with e|e|e|e
      · exact (h.ne (congrArg w e)).elim
      · have bad := h4 (w i) (H.c j) (H.c i) (w j) (out i j)
          ((priv i i).mpr rfl) (((H.adj _ _).mpr e).symm) h ((priv j j).mpr rfl).symm
        exact (out j i bad.symm).elim
      · exact Or.inl ⟨e,e.symm ▸ h⟩
      · exact Or.inr ⟨e,e.symm ▸ h.symm⟩
    · rintro (⟨e,h⟩|⟨e,h⟩)
      · exact e ▸ h
      · exact (e ▸ h).symm
  have sym (a b : Fin 10) : firstEdge m.val a.val b.val=firstEdge m.val b.val a.val := by
    simp only [firstEdge,min_comm,max_comm]
  have sorted (a b : Fin 10) (ab : a.val≤b.val) :
      G.Adj (layerTen H w a) (layerTen H w b)↔firstEdge m.val a.val b.val=true := by
    by_cases bb : b.val<5
    · have aa : a.val<5 := lt_of_le_of_lt ab bb
      rw [layerTen,dif_pos aa,layerTen,dif_pos bb]
      simp only [firstEdge,Nat.min_eq_left ab,Nat.max_eq_right ab,bb,if_true]
      exact (H.adj _ _).trans (adj_five_bits _ _)
    · by_cases aa : a.val<5
      · rw [layerTen,dif_pos aa,layerTen,dif_neg bb,G.adj_comm,priv]
        simp only [firstEdge,Nat.min_eq_left ab,Nat.max_eq_right ab,bb,if_false,aa,if_true,
          decide_eq_true_eq,Fin.ext_iff]
        omega
      · rw [layerTen,dif_neg aa,layerTen,dif_neg bb]
        simpa only [firstEdge,Nat.min_eq_left ab,Nat.max_eq_right ab,aa,bb,if_false] using
          diag ⟨a.val-5,by have := a.isLt; omega⟩ ⟨b.val-5,by have := b.isLt; omega⟩
  intro a b
  by_cases ab : a.val≤b.val
  · exact sorted _ _ ab
  · rw [sym,G.adj_comm]
    exact sorted _ _ (by omega)

theorem ten_layer_injective (H : Hole G 5) (w : Fin 5→V)
    (wo : ∀ i,Outside H.c (w i)) (wi : Function.Injective w) :
    Function.Injective (layerTen H w) := by
  intro a b eq
  by_cases la : a.val<5 <;> by_cases lb : b.val<5
  · rw [layerTen,dif_pos la,layerTen,dif_pos lb] at eq
    exact Fin.ext (congrArg (fun j : Fin 5=>j.val) (H.inj eq))
  · rw [layerTen,dif_pos la,layerTen,dif_neg lb] at eq
    exact (wo _ _ eq.symm).elim
  · rw [layerTen,dif_neg la,layerTen,dif_pos lb] at eq
    exact (wo _ _ eq).elim
  · rw [layerTen,dif_neg la,layerTen,dif_neg lb] at eq
    have e : a.val-5=b.val-5 := congrArg (fun j : Fin 5=>j.val) (wi eq)
    exact Fin.ext (by omega)

theorem fifteen_layer_injective (H : Hole G 5) (w q : Fin 5→V)
    (fi : Function.Injective (layerTen H w)) (qi : Function.Injective q)
    (fresh : ∀ i j,q i≠layerTen H w j) : Function.Injective (layerFifteen H w q) := by
  intro a b eq
  by_cases la : a.val<10 <;> by_cases lb : b.val<10
  · rw [layerFifteen,dif_pos la,layerFifteen,dif_pos lb] at eq
    exact Fin.ext (congrArg (fun j : Fin 10=>j.val) (fi eq))
  · rw [layerFifteen,dif_pos la,layerFifteen,dif_neg lb] at eq
    exact (fresh _ _ eq.symm).elim
  · rw [layerFifteen,dif_neg la,layerFifteen,dif_pos lb] at eq
    exact (fresh _ _ eq).elim
  · rw [layerFifteen,dif_neg la,layerFifteen,dif_neg lb] at eq
    have e : a.val-10=b.val-10 := congrArg (fun j : Fin 5=>j.val) (qi eq)
    exact Fin.ext (by omega)

theorem fifteen_layer_fit (H : Hole G 5) (w q : Fin 5→V)
    (m : Fin 32) (a b : Fin 5)
    (raw : ∀ x y : Fin 10,G.Adj (layerTen H w x) (layerTen H w y)↔firstEdge m.val x.val y.val=true)
    (only : ∀ i : Fin 5,∀ x : Fin 10,G.Adj (layerTen H w x) (q i)↔x.val=i.val+5)
    (hit : G.Adj (q a) (q b)) : Fit G (layerFifteen H w q) (outerSpec m a b) := by
  apply nested_fit_sorted
  · intro i j
    simp only [outerSpec,min_comm,max_comm]
  intro u v t le ev
  simp only [outerSpec,Nat.min_eq_left le,Nat.max_eq_right le] at ev
  by_cases h : v.val<10
  · rw [if_pos h,Option.some.injEq] at ev
    rw [←ev,layerFifteen,dif_pos (lt_of_le_of_lt le h),layerFifteen,dif_pos h]
    exact raw _ _
  rw [if_neg h] at ev
  by_cases u10 : u.val<10
  · rw [if_pos u10,Option.some.injEq] at ev
    rw [←ev,layerFifteen,dif_pos u10,layerFifteen,dif_neg h,only]
    simp only [decide_eq_true_eq]
    omega
  rw [if_neg u10] at ev
  by_cases eq : u.val=a.val+10 ∧ v.val=b.val+10
  · rw [if_pos eq,Option.some.injEq] at ev
    subst t
    rw [layerFifteen,dif_neg u10,layerFifteen,dif_neg h]
    have eu : (⟨u.val-10,by have := u.isLt; omega⟩ : Fin 5)=a := by
      apply Fin.ext
      change u.val-10=a.val
      have h := eq.1
      omega
    have ev : (⟨v.val-10,by have := v.isLt; omega⟩ : Fin 5)=b := by
      apply Fin.ext
      change v.val-10=b.val
      have h := eq.2
      omega
    rw [eu,ev]
    exact iff_of_true hit rfl
  · rw [if_neg eq] at ev
    contradiction

#print axioms ten_layer_fit
#print axioms fifteen_layer_fit
end Graffiti133P5PrivateAtlas
