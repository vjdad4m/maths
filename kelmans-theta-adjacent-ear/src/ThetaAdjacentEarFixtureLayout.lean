import ThetaAdjacentEarFixture
import ThetaCase
import ThetaGeometry
import ThetaAdjacentEarCap
import EarRelease


open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAdjacentEarFixture
open SquareCap (SmallTrivial)
open PentagonCap (pathCap attach)
open PentagonProfile (Port)
noncomputable section

abbrev Outside := Fin 9

def outsideEdges : List (Outside × Outside) :=
  [(0,6),(0,7),(1,4),(1,5),(2,5),(2,7),(3,7),(3,8),(4,6),(5,8),(6,8)]

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


/-- Explicit unique alternative neighbors in the exact labeled
7-theta exterior, not just a graph on unlinked coordinates. -/
def explicit_release : EarRelease.Released outside ports where
  next1 := ⟨5,by decide,by decide⟩
  next4 := ⟨6,by decide,by decide⟩
  end1 := by decide
  end4 := by decide

theorem old_and_new_pairs :
    outside.Adj (ports 1) (ports 4) ∧ ¬outside.Adj (ports 0) (ports 2) ∧
    outside.Adj (ports 0) explicit_release.next4.val ∧
    outside.Adj (ports 2) explicit_release.next1.val ∧
    outside.Adj (ports 3) 7 := by decide

abbrev XRest := EarRelease.Rest ports
def exterior : SimpleGraph XRest := outside.comap Subtype.val

instance : DecidableRel exterior.Adj := fun a b => inferInstanceAs (Decidable (outside.Adj a.val b.val))

def newPorts : Port ↪ XRest :=
  ⟨EarRelease.contacts explicit_release,by
    have trial : ∀ i j : Port,EarRelease.contacts explicit_release i=
      EarRelease.contacts explicit_release j→i=j := by decide
    exact trial⟩

/-- The prescribed cross-routing really gives an inadmissible cap
for this fixture. An actual geometric obstruction, not merely a failed
proof of a sufficient nonadjacency test. -/
theorem prescribed_cap_has_nontrivial_three_cut :
    ¬SmallTrivial (pathCap exterior (ThetaAdjacentEarCap.ports newPorts)) := by
  exact ThetaGeometry.kept_edge_breaks_fixed_cap
    (by decide : exterior.degree ((ThetaAdjacentEarCap.ports newPorts) 1)=2)
    (by decide : exterior.degree ((ThetaAdjacentEarCap.ports newPorts) 4)=2)
    (by decide : exterior.Adj ((ThetaAdjacentEarCap.ports newPorts) 1)
      ((ThetaAdjacentEarCap.ports newPorts) 4))

#print axioms exact_layout
#print axioms old_and_new_pairs
#print axioms prescribed_cap_has_nontrivial_three_cut
end
end KelmansCactus.AtomicBridge.ThetaAdjacentEarFixture
