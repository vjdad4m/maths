import Packing
import Mathlib.Combinatorics.SimpleGraph.Circulant

namespace Packing2560
open Finset SimpleGraph BullCover1125 TriangleMatching1078

/-- A graph is chordal if it has no induced cycle of length four or greater. -/
def Chordal {V : Type*} (G : SimpleGraph V) :=
  ∀ n : ℕ, 4 ≤ n → Free G (cycleGraph n)

/-- The pinned numeric row, including the missing-value convention on isolates. -/
theorem row2560 {V : Type*} [Fintype V] (G : SimpleGraph V) (_nontrivial : 2 ≤ Fintype.card V)
    (_chordal : Chordal G) (cl : Free G claw) {r : ℕ} (numeric : edgeCoverValue G = some r) :
    r ≤ 3 * lineDomination G := by
  classical
  by_cases h : IsolateFree G
  · have eq : edgeCoverNumber G = r := by simpa [edgeCoverValue,h] using numeric
    have fine := refined h cl
    have cap := min_le_left (lineDomination G) (bullPacking G)
    omega
  · simp [edgeCoverValue,h] at numeric

theorem bull_claw_free : Free bull claw := by
  rintro ⟨f⟩
  have check : ∀ a b c d : Fin 5, b ≠ c → b ≠ d → c ≠ d →
      bull.Adj a b → bull.Adj a c → bull.Adj a d →
      bull.Adj b c ∨ bull.Adj b d ∨ bull.Adj c d := by decide
  have adj (i : Fin 4) (h : claw.Adj 0 i) := f.map_rel_iff.mpr h
  have clash := check (f 0) (f 1) (f 2) (f 3) (f.injective.ne (by decide))
    (f.injective.ne (by decide)) (f.injective.ne (by decide)) (adj 1 (by decide))
    (adj 2 (by decide)) (adj 3 (by decide))
  rcases clash with h|h|h
  · exact absurd (f.map_rel_iff.mp h) (by decide)
  · exact absurd (f.map_rel_iff.mp h) (by decide)
  · exact absurd (f.map_rel_iff.mp h) (by decide)

/-- Only the three triangle vertices have two distinct neighbors. Every
vertex on a cycle has two, so a cycle in the bull has at most three vertices. -/
theorem bull_chordal : Chordal bull := by
  rintro n hn ⟨f⟩
  have cap := Fintype.card_le_of_injective _ f.injective
  simp only [Fintype.card_fin] at cap
  have two : ∀ i : Fin n, ∃ j k : Fin n, j ≠ k ∧ (cycleGraph n).Adj i j ∧ (cycleGraph n).Adj i k := by
    rcases (show n=4 ∨ n=5 by omega) with rfl|rfl <;> decide
  let core : Finset (Fin 5) := {0,1,4}
  have core_only : ∀ v x y : Fin 5, x ≠ y → bull.Adj v x → bull.Adj v y → v ∈ core := by decide
  have all (i : Fin n) : f i ∈ core := by
    obtain ⟨j,k,jk,ij,ik⟩ := two i
    exact core_only _ _ _ (f.injective.ne jk) (f.map_rel_iff.mpr ij) (f.map_rel_iff.mpr ik)
  let g (i : Fin n) : ↥core := ⟨f i,all i⟩
  have small := Fintype.card_le_of_injective g (fun i j eq => f.injective (congrArg Subtype.val eq))
  rw [Fintype.card_fin,Fintype.card_coe] at small
  have three : core.card = 3 := by decide
  omega

theorem sharp : 2 ≤ Fintype.card (Fin 5) ∧ Chordal bull ∧ Free bull claw ∧
    edgeCoverValue bull = some 3 ∧ lineDomination bull = 1 := by
  classical
  obtain ⟨h,c,d⟩ := bull_values
  exact ⟨by decide,bull_chordal,bull_claw_free,by simp [edgeCoverValue,h,c],d⟩

theorem packing_zero_iff {V : Type*} [Fintype V] (G : SimpleGraph V) :
    bullPacking G = 0 ↔ Free G bull := by
  classical
  constructor
  · intro zero ⟨f⟩
    have pos := packing_le (fun _ : Fin 1 => f) (fun i j ne => False.elim (ne (Subsingleton.elim i j)))
    simp [zero] at pos
  · intro free
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro k hk
    obtain ⟨f,_⟩ := (mem_filter.mp hk).2
    by_contra! pos
    exact free ⟨f ⟨0,pos⟩⟩

theorem packing_order {V : Type*} [Fintype V] (G : SimpleGraph V) :
    bullPacking G ≤ Fintype.card V / 5 := by
  classical
  apply Finset.sup_le
  intro k hk
  obtain ⟨f,separate⟩ := (mem_filter.mp hk).2
  let g (p : Fin k × Fin 5) := f p.1 p.2
  have inj : Function.Injective g := by
    rintro ⟨i,u⟩ ⟨j,v⟩ eq
    have ij : i=j := Classical.byContradiction (fun ne => separate i j ne u v eq)
    subst j
    exact congrArg (Prod.mk i) ((f i).injective eq)
  have cap := Fintype.card_le_of_injective g inj
  simp only [Fintype.card_prod,Fintype.card_fin] at cap
  exact (Nat.le_div_iff_mul_le (by decide)).mpr cap

theorem bull_packing_sharp : bullPacking bull = 1 := by
  have cap := packing_order bull
  have pos := refined bull_values.1 bull_claw_free
  rw [bull_values.2.1,bull_values.2.2] at pos
  simp only [Fintype.card_fin] at cap
  omega

#print axioms packing_order
#print axioms packing_zero_iff
#print axioms bull_packing_sharp
#print axioms patch_estimate
#print axioms refined
#print axioms row2560
#print axioms sharp
end Packing2560
