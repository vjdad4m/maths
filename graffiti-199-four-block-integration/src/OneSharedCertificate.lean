import OneSharedData
import DepletedPaths

open private validFull lift_full_cert from SplitTipsLocal

namespace Graffiti199Depleted.OneShared

open Graffiti199K2.NearPacking.Depleted

abbrev J := Fin 9

def leftLabel (k : Fin 4) : J := k.castAdd 5

def rightLabel (i j : Fin 4) : Fin 4 → J :=
  ![4,if j = 1 then leftLabel i else 5,
    if j = 2 then leftLabel i else if j = 1 then 5 else 6,
    if j = 3 then leftLabel i else 6]

def freshRight (j : Fin 4) : Fin 3 → Fin 4 :=
  ![0,if j = 1 then 2 else 1,if j = 3 then 2 else 3]

theorem right_labels (i j : Fin 4) (hi : singletonHigh i = true) (hj : singletonHigh j = true) :
    Function.Injective (freshRight j) ∧
      (∀ k : Fin 4, (∃ a : Fin 3, freshRight j a = k) ↔ k ≠ j) ∧
      rightLabel i j j = leftLabel i ∧
      ∀ a : Fin 3, rightLabel i j (freshRight j a) = (a.natAdd 4).castAdd 2 := by
  unfold Function.Injective
  revert i j
  decide

def coreHigh (k : J) : Bool := (k != 0) && (k != 4) && decide (k.val < 7)

theorem left_high (k : Fin 4) (hi : singletonHigh k = true) : coreHigh (leftLabel k) = true := by
  revert k
  decide

theorem right_high (i j k : Fin 4)
    (hi : singletonHigh i = true) (hj : singletonHigh j = true) (hk : singletonHigh k = true) :
    coreHigh (rightLabel i j k) = true := by
  revert i j k
  decide

theorem high_preimage (k : J) (h : coreHigh k = true) :
    ∃ a : I, high a = true ∧ a ≠ 7 ∧ a.castAdd 1 = k := by
  revert k
  decide

def pairOutsideSeven (r : Row) : Prop :=
  (halves r).1 ≠ 7 ∧ (halves r).2.1 ≠ 7 ∧ (halves r).2.2.1 ≠ 7 ∧ (halves r).2.2.2 ≠ 7

private instance (r : Row) : Decidable (pairOutsideSeven r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def edgeMap {m : ℕ} (f : Fin m → J) (e : Fin m × Fin m) : J × J :=
  (f e.1,f e.2)

def coreEdges (i j : Fin 4) (r : Row) : List (J × J) :=
  let a := (halves r).1.castAdd 1
  let b := (halves r).2.1.castAdd 1
  let c := (halves r).2.2.1.castAdd 1
  let d := (halves r).2.2.2.castAdd 1
  singletonEdges.map (edgeMap leftLabel) ++ singletonEdges.map (edgeMap (rightLabel i j)) ++
    [(7,8),(7,a),(7,b),(a,b),(8,c),(8,d),(c,d)]

def looseBans : List (Fin 4 × Fin 4) := [(1,3),(2,3)]

def coreBans (i j : Fin 4) : List (J × J) :=
  looseBans.map (edgeMap leftLabel) ++ looseBans.map (edgeMap (rightLabel i j))

private def feasible (i j : Fin 4) (r : Row) : Bool :=
  (coreBans i j).all fun (a,b) => !((coreEdges i j r).contains (a,b) ||
    (coreEdges i j r).contains (b,a))

private def route (i j : Fin 4) (r : Row) (k : J) : List J :=
  ((data.getD (4 * i.val + j.val) #[]).getD r.val #[]).getD k.val []

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 8192 in
private theorem route_check :
    ∀ (i j : Fin 4) (r : Row), singletonHigh i = true → singletonHigh j = true →
      pairOutsideSeven r → feasible i j r = true → ∀ k : J, coreHigh k = true →
      validFull (coreEdges i j r) (route i j r k) ((route i j r k).headD 0) k = true := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- Every compatible one-shared-tip core has a path ending at any high vertex. -/
theorem core_path_ending_at_high {V : Type*} {G : SimpleGraph V} (f : J ↪ V)
    {i j : Fin 4} (hi : singletonHigh i = true) (hj : singletonHigh j = true)
    {r : Row} (proper : pairOutsideSeven r)
    (edges : ∀ a b, (a,b) ∈ coreEdges i j r → G.Adj (f a) (f b))
    (nonedges : ∀ a b, (a,b) ∈ coreBans i j → ¬ G.Adj (f a) (f b))
    {k : J} (hk : coreHigh k = true) : ∃ p : PathOn G (labelRegion f), p.last = f k := by
  have possible : feasible i j r = true := by
    apply List.all_eq_true.mpr
    rintro ⟨a,b⟩ h
    change Bool.not ((coreEdges i j r).contains (a,b) || (coreEdges i j r).contains (b,a)) = true
    cases eq : (coreEdges i j r).contains (a,b) || (coreEdges i j r).contains (b,a)
    · rfl
    · simp only [Bool.or_eq_true,List.contains_iff_mem] at eq
      exact (nonedges a b h (eq.elim (edges a b) (fun e => (edges b a e).symm))).elim
  obtain ⟨p,_,last⟩ := lift_full_cert f _ edges (route_check i j r hi hj proper possible k hk)
  exact ⟨p,last⟩

#print axioms core_path_ending_at_high

end Graffiti199Depleted.OneShared
