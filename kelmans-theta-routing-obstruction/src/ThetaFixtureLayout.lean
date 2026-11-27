import ThetaCase
import ThetaFixture

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaFixture
open SquareCap (SmallTrivial)
open PentagonCap (pathCap attach)
open PentagonProfile (Port)
noncomputable section

abbrev Outside := Fin 9

def outsideEdges : List (Outside × Outside) :=
  [(1,4),(2,3),(0,5),(5,6),(6,7),(7,8),(0,8),(1,5),(4,7),(2,6),(3,8)]

private theorem increasing : ∀ x : Outside, (x,x)∉outsideEdges := by decide

def outside : SimpleGraph Outside where
  Adj a b := (a,b)∈outsideEdges ∨ (b,a)∈outsideEdges
  symm := by intro _ _ h; exact h.elim Or.inr Or.inl
  loopless a h := increasing a (h.elim id id)

instance : DecidableRel outside.Adj := fun a b =>
  inferInstanceAs (Decidable ((a,b)∈outsideEdges ∨ (b,a)∈outsideEdges))

def ports : Port ↪ Outside :=
  ⟨fun i => ⟨i.val,by have li := i.isLt; omega⟩,fun _ _ eq=>Fin.ext (congrArg (fun x : Outside=>x.val) eq)⟩

instance : DecidableRel (ThetaCase.ambient outside ports).Adj := by
  intro a b
  cases a <;> cases b
  · exact inferInstanceAs (Decidable (outside.Adj _ _))
  · exact inferInstanceAs (Decidable (∃ i : Port, ports i = _ ∧ ThetaCase.arm i = _))
  · exact inferInstanceAs (Decidable (∃ i : Port, ports i = _ ∧ ThetaCase.arm i = _))
  · exact inferInstanceAs (Decidable (ThetaCase.theta.Adj _ _))

private def fwd : (Outside ⊕ Fin 7) → X
  | .inl i => ⟨i.val+7,by have hi:=i.isLt; omega⟩
  | .inr i => ⟨i.val,by have hi:=i.isLt; omega⟩

private theorem fwd_bij : Function.Bijective fwd := by
  constructor
  · intro a b h
    have eq := congrArg Fin.val h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        change a.val+7=b.val+7 at eq
        exact congrArg Sum.inl (Fin.ext (by omega))
      | inr b =>
        change a.val+7=b.val at eq
        have hi := b.isLt
        omega
    | inr a =>
      cases b with
      | inl b =>
        change a.val=b.val+7 at eq
        have hi := a.isLt
        omega
      | inr b => exact congrArg Sum.inr (Fin.ext eq)
  · intro i
    by_cases c : i.val<7
    · exact ⟨Sum.inr ⟨i.val,c⟩,rfl⟩
    · have hi := i.isLt
      exact ⟨Sum.inl ⟨i.val-7,by omega⟩,Fin.ext (by change (i.val-7)+7=i.val; omega)⟩

/-- The obstruction graph really has the exact theta-and-five-wires
layout used by the conditional proof. -/
def exact_layout : ThetaCase.ambient outside ports ≃g graph where
  toEquiv := Equiv.ofBijective fwd fwd_bij
  map_rel_iff' := by
    intro x y
    have audit : ∀ a b : Outside ⊕ Fin 7,
      graph.Adj (fwd a) (fwd b) ↔ (ThetaCase.ambient outside ports).Adj a b := by decide
    exact audit x y

/-- In this explicit input BOTH forbidden contact adjacencies occur.
The fixed cap is therefore inadmissible, despite the target's
verified factor. -/
theorem fixed_cap_unusable : ¬ SmallTrivial (pathCap outside ports) := by
  exact ThetaGeometry.kept_edge_breaks_fixed_cap
    (by decide : outside.degree (ports 1)=2)
    (by decide : outside.degree (ports 4)=2)
    (by decide : outside.Adj (ports 1) (ports 4))

theorem both_contact_obstructions :
    outside.Adj (ports 1) (ports 4) ∧ outside.Adj (ports 2) (ports 3) := by decide

#print axioms exact_layout
#print axioms fixed_cap_unusable
#print axioms both_contact_obstructions

end
end KelmansCactus.AtomicBridge.ThetaFixture
