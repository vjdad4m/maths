import PrismCore
import RemoteSpacedPrismHandle

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteSpacedPrismLayout
open RemoteSpacedPrismHandle (Port first second third)
open RemoteSubdivisionCore (Marks)

/-- There are six gap segments, each of length three k plus one. -/
def gap (k : Nat) : Nat := 3*k+1
def columns (k : Nat) : Nat := 6*gap k
theorem gap_pos (k : Nat) : 0<gap k := by simp [gap]
theorem columns_large (k : Nat) : 6≤columns k := by
  simp only [columns,gap]
  omega

abbrev Core (k : Nat) := Fin (columns k)×Bool
abbrev Board (k : Nat) := Core k ⊕ Port

abbrev core (k : Nat) : SimpleGraph (Core k) := Prism.core (columns k) (columns_large k)

def index : Port→Nat
  | .inl (.inl false) => 0
  | .inl (.inl true) => 1
  | .inl (.inr false) => 2
  | .inl (.inr true) => 3
  | .inr false => 4
  | .inr true => 5

theorem index_lt6 : ∀ i : Port,index i<6 := by decide
theorem index_injective : Function.Injective index := by
  change ∀ i j : Port,index i=index j→i=j
  decide
theorem index_surjective : ∀ j : Fin 6,∃ i : Port,index i=j.val := by decide

def markCol (k : Nat) (i : Port) : Fin (columns k) :=
  ⟨index i * gap k,Nat.mul_lt_mul_of_pos_right (index_lt6 i) (gap_pos k)⟩

theorem markCol_injective (k : Nat) : Function.Injective (markCol k) := by
  intro i j e
  have h : index i * gap k = index j * gap k :=
    congrArg (fun v : Fin (columns k)=>v.val) e
  exact index_injective (Nat.eq_of_mul_eq_mul_right (gap_pos k) h)

def marks (k : Nat) : Marks (core k) Port where
  a i := (markCol k i,false)
  b i := (markCol k i,true)
  edge _ := Or.inr ⟨rfl,by change false≠true; decide⟩
  separated := by
    intro i j x l r
    have eq (i : Port) (h : x=(markCol k i,false)∨x=(markCol k i,true)) :
        x.1=markCol k i := h.elim (congrArg Prod.fst) (congrArg Prod.fst)
    exact markCol_injective k ((eq i l).symm.trans (eq j r))

abbrev board (k : Nat) : SimpleGraph (Board k) := (marks k).expanded

theorem slot_adj (k : Nat) (i : Port) (r : Bool) :
    (board k).Adj (Sum.inr i) (Sum.inl (markCol k i,r)) := by
  cases r
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem row_adj (k : Nat) {a b : Fin (columns k)} (edge : a.val+1=b.val) (r : Bool) :
    (board k).Adj (.inl (a,r)) (.inl (b,r)) := by
  have e : (a.val+1) % columns k=b.val := by
    rw [edge,Nat.mod_eq_of_lt b.isLt]
  refine ⟨Or.inl ⟨rfl,Or.inl e⟩,?_⟩
  rintro ⟨i,⟨x,y⟩|⟨x,y⟩⟩
  · have rf : r=false := congrArg Prod.snd x
    have rt : r=true := congrArg Prod.snd y
    rw [rf] at rt
    contradiction
  · have rt : r=true := congrArg Prod.snd x
    have rf : r=false := congrArg Prod.snd y
    rw [rf] at rt
    contradiction

theorem core_cube (k : Nat) : ∀ v,(core k).degree v=3 :=
  Prism.core_cubic (columns k) (columns_large k)

theorem core_cyclic_four (k : Nat) : SquareCap.SmallTrivial (core k) :=
  Prism.core_small (columns k) (columns_large k)

#print axioms row_adj
#print axioms core_cyclic_four
end KelmansCactus.AtomicBridge.RemoteSpacedPrismLayout
