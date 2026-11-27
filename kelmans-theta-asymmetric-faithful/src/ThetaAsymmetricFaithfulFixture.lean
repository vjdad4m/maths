import ThetaAsymmetricFaithful
import ThetaAsymmetricFaithfulTable

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulFixture
open SquareCap (boundary FactorOn SmallTrivial IsTile)
open ThetaSevenFaithfulCap (core3)
open ThetaSevenFaithfulSplice (Dead Live Faith)
open ThetaSevenFaithfulRefill (In)
open ThetaAsymmetricFaithful (ambient candidate glue lift restricted target)
open ThetaAsymmetricFaithfulTable (Wire formerWires)

abbrev Out := Fin 13
abbrev W := Out⊕Fin 3

def extEdges : List (Out×Out) :=
  [(0,8),(1,7),(1,8),(2,9),(2,11),(3,11),(3,12),(4,10),
    (4,11),(5,6),(5,7),(6,8),(6,10),(7,12),(9,10),(9,12)]

private theorem loop : ∀ x : Out,(x,x)∉extEdges := by decide

def B : SimpleGraph Out where
  Adj a b := (a,b)∈extEdges∨(b,a)∈extEdges
  symm := fun _ _ h=>h.elim Or.inr Or.inl
  loopless x h := loop x (h.elim id id)

instance : DecidableRel B.Adj := fun a b=>
  inferInstanceAs (Decidable ((a,b)∈extEdges∨(b,a)∈extEdges))

def p (i : Wire) : Out := if i=5 then 0 else if i=6 then 5 else ⟨i.val,by omega⟩

def oldCap : SimpleGraph W := glue B core3 p formerWires

instance : DecidableRel oldCap.Adj :=
  inferInstanceAs (DecidableRel (glue B core3 p formerWires).Adj)

def color : W→Bool
  | .inl i => decide (i∈([0,1,5,6,7,8]:List Out))
  | .inr j => decide (j=2)

def cut : Finset (W×W) :=
  {(.inl 0,.inr 1),(.inl 6,.inl 10),(.inl 7,.inl 12)}

theorem old_cut_exact : boundary oldCap color=cut := by
  classical
  have test : ∀ x y : W, (color x=true ∧ color y=false ∧ oldCap.Adj x y) ↔ (x,y)∈cut := by decide
  ext ⟨x,y⟩
  simpa only [boundary,mem_filter,mem_univ,true_and] using test x y

theorem old_cap_invalid : ¬SmallTrivial oldCap := by
  intro good
  have k : (boundary oldCap color).card≤3 := by rw [old_cut_exact]; decide
  rcases good color k with h|h
  · exact (by decide : (Sum.inl 0:W)≠Sum.inl 1) (h _ _ (by decide) (by decide))
  · exact (by decide : (Sum.inl 2:W)≠Sum.inl 3) (h _ _ (by decide) (by decide))

theorem cubic_ambient : ∀ v,(ambient B p).degree v=3 := by decide

instance : DecidableRel (restricted B p).Adj := fun a b=>
  inferInstanceAs (Decidable ((candidate B p).Adj a b∧
    ¬((a=Faith∧b=Sum.inl (p 4))∨(a=Sum.inl (p 4)∧b=Faith))))

private instance (s : Finset W) : Decidable (IsTile (restricted B p) s) := by
  unfold IsTile; infer_instance

def packing : Finset (Finset W) :=
  {{.inl 0,.inl 8,Live},{.inl 7,.inl 1,.inl 12},{.inl 9,.inl 2,.inl 10},
    {.inl 11,.inl 3,.inl 4},{.inl 5,.inl 6,Faith}}

theorem candidate_factor : FactorOn (restricted B p) (univ.erase Dead) := by
  refine ⟨packing,?_,?_,by decide⟩
  · intro a ma
    simp only [packing,mem_insert,mem_singleton] at ma
    rcases ma with rfl|rfl|rfl|rfl|rfl <;> decide
  · intro a ma b mb ne
    simp only [packing,mem_insert,mem_singleton] at ma mb
    rcases ma with rfl|rfl|rfl|rfl|rfl <;> rcases mb with rfl|rfl|rfl|rfl|rfl
    all_goals first | exact (ne rfl).elim | decide

theorem lifted_target : FactorOn (target B p) (univ.erase (In 6)) :=
  lift B p (by decide) candidate_factor

#print axioms old_cut_exact
#print axioms old_cap_invalid
#print axioms cubic_ambient
#print axioms lifted_target
end KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulFixture
