import ThetaAsymmetricFaithfulTable
import ThetaSevenFaithfulSplice

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAsymmetricFaithful
open SquareCap (SmallTrivial FactorOn omitEdge)
open ThetaSevenFaithfulCap (core3 core9)
open ThetaSevenFaithfulSplice (Dead Live Faith)
open ThetaSevenFaithfulRefill (In Shape)
open ThetaAsymmetricFaithfulTable (Wire oldWires newWires)

noncomputable section
universe u
variable {V : Type u} {I : Type*}

def link (p : Wire→V) (W : List (Wire×I)) (x : V) (j : I) : Prop :=
  ∃ i : Wire,p i=x ∧ (i,j)∈W

def linkAdj (B : SimpleGraph V) (K : SimpleGraph I) (p : Wire→V)
    (W : List (Wire×I)) : V⊕I→V⊕I→Prop
  | .inl x,.inl y => B.Adj x y
  | .inr x,.inr y => K.Adj x y
  | .inl x,.inr y => link p W x y
  | .inr y,.inl x => link p W x y

/-- Two wire labels may denote the same physical exterior vertex, but
the local factor lift never treats those labels as two disjoint vertices. -/
def glue (B : SimpleGraph V) (K : SimpleGraph I) (p : Wire→V)
    (W : List (Wire×I)) : SimpleGraph (V⊕I) where
  Adj := linkAdj B K p W
  symm := by intro x y e; cases x <;> cases y <;> first | exact e | exact e.symm
  loopless := by
    intro x e
    cases x with
    | inl x => exact B.loopless _ e
    | inr x => exact K.loopless _ e

instance [DecidableEq V] [DecidableEq I] (B : SimpleGraph V) [DecidableRel B.Adj]
    (K : SimpleGraph I) [DecidableRel K.Adj] (p : Wire→V) (W : List (Wire×I)) :
    DecidableRel (glue B K p W).Adj := by
  rintro (x|x) (y|y)
  · exact inferInstanceAs (Decidable (B.Adj x y))
  · exact inferInstanceAs (Decidable (∃ i : Wire,p i=x∧(i,y)∈W))
  · exact inferInstanceAs (Decidable (∃ i : Wire,p i=y∧(i,x)∈W))
  · exact inferInstanceAs (Decidable (K.Adj x y))

def ambient (B : SimpleGraph V) (p : Wire→V) := glue B core9 p oldWires
def candidate (B : SimpleGraph V) (p : Wire→V) := glue B core3 p newWires
def target (B : SimpleGraph V) (p : Wire→V) := omitEdge (ambient B p) (In 7) (In 8)
def restricted (B : SimpleGraph V) (p : Wire→V) :=
  omitEdge (candidate B p) Faith (.inl (p 4))

instance [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj] (p : Wire→V) :
    DecidableRel (ambient B p).Adj :=
  inferInstanceAs (DecidableRel (glue B core9 p oldWires).Adj)
instance [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj] (p : Wire→V) :
    DecidableRel (candidate B p).Adj :=
  inferInstanceAs (DecidableRel (glue B core3 p newWires).Adj)

variable [Fintype V] [DecidableEq V]

/-- Exact factor transfer for the auxiliary-at-t layout, allowing
the two faithful h-neighbors to be old or new exterior contacts. -/
theorem lift (B : SimpleGraph V) (p : Wire→V) (ne : p 0≠p 3)
    (f : FactorOn (restricted B p) (univ.erase Dead)) :
    FactorOn (target B p) (univ.erase (In 6)) := by
  have kept (x y : Fin 9) (xy : core9.Adj x y)
      (d : ¬((x=7∧y=8)∨(x=8∧y=7))) : (target B p).Adj (In x) (In y) :=
    ⟨xy,by simpa using d⟩
  have sh : Shape (target B p) := {
    e01 := kept 0 1 (by decide) (by decide)
    e12 := kept 1 2 (by decide) (by decide)
    e23 := kept 2 3 (by decide) (by decide)
    e34 := kept 3 4 (by decide) (by decide)
    e45 := kept 4 5 (by decide) (by decide)
    e50 := kept 5 0 (by decide) (by decide)
    e17 := kept 1 7 (by decide) (by decide) }
  have q2 : (target B p).Adj (In 2) (.inl (p 0)) := ⟨⟨0,rfl,by decide⟩,by simp⟩
  have q5 : (target B p).Adj (In 5) (.inl (p 3)) := ⟨⟨3,rfl,by decide⟩,by simp⟩
  refine ThetaSevenFaithfulSplice.splice ne sh q2 q5 ?_ ?_ f
  · intro x nd h
    cases x with
    | inl y =>
      obtain ⟨i,e,edge⟩ : link p newWires y 1 := h.1
      have al : ∀ i : Wire,(i,1)∈newWires→i=0∨i=3 := by decide
      rcases al i edge with rfl|rfl
      · exact Or.inl (congrArg Sum.inl e.symm)
      · exact Or.inr (congrArg Sum.inl e.symm)
    | inr j =>
      have x : core3.Adj 1 j := h.1
      have only : ∀ j : Fin 3,core3.Adj 1 j→j=0 := by decide
      exact (nd (congrArg Sum.inr (only j x))).elim
  · have tag : ∀ i : Fin 3,i≠0→i≠1→i=2 := by decide
    have fa (y : V) (e : (restricted B p).Adj Faith (.inl y)) :
        (target B p).Adj (In 8) (.inl y) := by
      obtain ⟨i,eq,run⟩ : link p newWires y 2 := e.1
      have only : ∀ i : Wire,(i,2)∈newWires→i=4∨i=5∨i=6 := by decide
      rcases only i run with rfl|rfl|rfl
      · exact (e.2 (Or.inl ⟨rfl,congrArg Sum.inl eq.symm⟩)).elim
      · exact ⟨⟨5,eq,by decide⟩,by simp⟩
      · exact ⟨⟨6,eq,by decide⟩,by simp⟩
    intro x y xd xl yd yl e
    cases x with
    | inl u =>
      cases y with
      | inl v => exact ⟨e.1,by simp⟩
      | inr j =>
        have h := tag j (fun z=>yd (congrArg Sum.inr z)) (fun z=>yl (congrArg Sum.inr z))
        subst j
        exact (fa u e.symm).symm
    | inr i =>
      have hi := tag i (fun z=>xd (congrArg Sum.inr z)) (fun z=>xl (congrArg Sum.inr z))
      subst i
      cases y with
      | inl v => exact fa v e
      | inr j =>
        have hj := tag j (fun z=>yd (congrArg Sum.inr z)) (fun z=>yl (congrArg Sum.inr z))
        subst j
        exact (e.ne rfl).elim


/-- Once this exact cap is cubic and cyclic four, only smaller F2 is
used; cap validity is intentionally not asserted in this module. -/
theorem reduce_of_valid_cap {B : SimpleGraph V} [DecidableRel B.Adj] {p : Wire→V}
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    (ne : p 0≠p 3)
    (enough : 1≤Fintype.card V)
    (cub : ∀ v,(candidate B p).degree v=3)
    (valid : SmallTrivial (candidate B p)) (order : Fintype.card (V⊕Fin 9)%6=4) :
    FactorOn (target B p) (univ.erase (In 6)) := by
  let C := candidate B p
  have c3 : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have c9 : Fintype.card (V⊕Fin 9)=Fintype.card V+9 := by simp
  have conn := SquareCap.three_connected_of_small_trivial C cub (by omega) valid
  have wire : C.Adj Faith (Sum.inl (p 4)) := ⟨4,rfl,by decide⟩
  have f := smaller (V⊕Fin 3) C (by omega) cub conn valid (by omega)
    Dead Faith (Sum.inl (p 4)) wire
  exact lift B p ne f

#print axioms lift
#print axioms reduce_of_valid_cap
end
end KelmansCactus.AtomicBridge.ThetaAsymmetricFaithful
