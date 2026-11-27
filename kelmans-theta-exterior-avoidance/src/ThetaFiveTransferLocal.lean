import SquareCapFactor
import Mathlib.Tactic.FinCases

open SimpleGraph Finset
namespace KelmansCactus.AtomicBridge.ThetaFiveTransferLocal
open SquareCap (FactorOn IsTile factor_map)

abbrev Ring := Fin 6
abbrev Patch := Fin 9

private def cyclic (i j : Ring) : Prop := i+1=j ∨ j+1=i
private def into (i : Ring) : Patch := ⟨i.val,by have h:=i.isLt; omega⟩
private def inRing (i : Patch) (h : i.val<6) : Ring := ⟨i.val,h⟩

def ringEdges : List (Patch×Patch) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]

/-- Mode 0: all three borrowed contacts. Modes 1 and 2: one
opposite contact (label 7) plus its actual outside neighbor 8. -/
def edges (mode : Fin 3) : List (Patch×Patch) :=
  ringEdges ++ [(1,6)] ++
    if mode=0 then [(2,7),(5,8)] else if mode=1 then [(2,7),(7,8)] else [(5,7),(7,8)]

private theorem ordered_noloop : ∀ mode a,(a,a)∉edges mode := by decide

def graph (mode : Fin 3) : SimpleGraph Patch where
  Adj a b := (a,b)∈edges mode ∨ (b,a)∈edges mode
  symm := by intro _ _ h; exact h.elim Or.inr Or.inl
  loopless a h := ordered_noloop mode a (h.elim id id)

instance (mode : Fin 3) : DecidableRel (graph mode).Adj := fun a b=>
  inferInstanceAs (Decidable ((a,b)∈edges mode ∨ (b,a)∈edges mode))

private instance (mode : Fin 3) (s : Finset Patch) : Decidable (IsTile (graph mode) s) := by
  unfold IsTile
  infer_instance

private def tiles (mode : Fin 3) : Finset (Finset Patch) :=
  if mode=0 then {{0,1,6},{2,3,7},{4,5,8}}
  else if mode=1 then {{0,1,6},{2,7,8},{3,4,5}}
  else {{0,1,6},{5,7,8},{2,3,4}}

private abbrev tileGood (mode : Fin 3) : Prop :=
  ∀ s∈tiles mode,IsTile (graph mode) s
private abbrev tileDisj (mode : Fin 3) : Prop :=
  ∀ s∈tiles mode,∀ t∈tiles mode,s≠t → Disjoint s t
private abbrev tileCover (mode : Fin 3) : Prop :=
  (tiles mode).biUnion id=univ

private theorem tt1 (m : Fin 3) : tileGood m := by
  intro s hs
  fin_cases m
  all_goals
    simp [tiles] at hs
    rcases hs with rfl|rfl|rfl <;> decide
private theorem tt2 (m : Fin 3) : tileDisj m := by
  intro s hs t ht ne
  fin_cases m
  all_goals
    simp [tiles] at hs ht
    rcases hs with rfl|rfl|rfl <;> rcases ht with rfl|rfl|rfl
    all_goals first | exact (ne rfl).elim | decide
private theorem tt3 (m : Fin 3) : tileCover m := by
  fin_cases m <;> decide

/-- The precise finite normalized replacement: a C6 and three
outside vertices tile in each of the center and two leaf modes. -/
theorem normalized_local_refill (mode : Fin 3) : FactorOn (graph mode) univ :=
  ⟨tiles mode,tt1 mode,tt2 mode,tt3 mode⟩

/-- Any injective copy of the corresponding finite patch transfers
the checked tiling to the exact image, regardless of extra edges. -/
theorem mapped_local_refill {T : Type*} [DecidableEq T] {G : SimpleGraph T}
    (mode : Fin 3) (f : Patch↪T)
    (keeps : ∀ a b,(a,b)∈edges mode → G.Adj (f a) (f b)) :
    FactorOn G (univ.map f) := by
  refine factor_map f (fun a b edge=>?_ ) (normalized_local_refill mode)
  exact edge.elim (keeps a b) (fun h=>(keeps b a h).symm)

#print axioms mapped_local_refill
#print axioms normalized_local_refill
end KelmansCactus.AtomicBridge.ThetaFiveTransferLocal
