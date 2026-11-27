import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path

namespace KelmansCactus.AtomicBridge.ThetaLocalRoute

abbrev Ring := Fin 6
abbrev Mode := Fin 4

/-- Local omissions seen after deleting theta root 6: one surviving
ring edge, one ring wire, or nothing (including a root-incident edge). -/
inductive Ban
  | none
  | ring (start : Ring)
  | wire (site : Ring)
  deriving DecidableEq

/-- Four dihedral symmetries preserving the available wire sites. -/
def route (m : Mode) (i : Ring) : Ring :=
  if m=0 then i else if m=1 then i+3 else if m=2 then -i else 3-i

theorem route_injective (m : Mode) : Function.Injective (route m) := by
  have audit : ∀ m : Mode, ∀ i j : Ring, route m i=route m j → i=j := by decide
  exact audit m

def chosen : Ban → Mode
  | .none => 0
  | .ring i => if i=0 then 2 else if i=2 ∨ i=4 then 1 else if i=3 then 3 else 0
  | .wire i => if i=1 then 1 else if i=2 then 2 else if i=5 then 3 else 0

def ringOK (ban : Ban) (i j : Ring) : Prop :=
  (i+1=j ∨ j+1=i) ∧ (ban ≠ .ring i ∨ i+1≠j) ∧ (ban ≠ .ring j ∨ j+1≠i)

def wireOK (ban : Ban) (i : Ring) : Prop :=
  (i=1 ∨ i=2 ∨ i=4 ∨ i=5) ∧ ban≠.wire i

/-- Fallback profile needs edges 01, 23, 34, 45 and wires 1,2,5.
The straight profile additionally uses either 12 or 50. -/
def Good (ban : Ban) (f : Ring → Ring) : Prop :=
  ringOK ban (f 0) (f 1) ∧ ringOK ban (f 2) (f 3) ∧
  ringOK ban (f 3) (f 4) ∧ ringOK ban (f 4) (f 5) ∧
  (ringOK ban (f 1) (f 2) ∨ ringOK ban (f 5) (f 0)) ∧
  wireOK ban (f 1) ∧ wireOK ban (f 2) ∧ wireOK ban (f 5)

instance (b : Ban) (i j : Ring) : Decidable (ringOK b i j) := by
  unfold ringOK; infer_instance

instance (b : Ban) (i : Ring) : Decidable (wireOK b i) := by
  unfold wireOK; infer_instance

instance (b : Ban) (f : Ring→Ring) : Decidable (Good b f) := by
  unfold Good; infer_instance

theorem exact_local_routing (b : Ban) : Good b (route (chosen b)) := by
  cases b with
  | none => decide
  | ring start =>
    have a : ∀ x : Ring, Good (.ring x) (route (chosen (.ring x))) := by decide
    exact a start
  | wire site =>
    have a : ∀ x : Ring, Good (.wire x) (route (chosen (.wire x))) := by decide
    exact a site

#print axioms exact_local_routing
#print axioms route_injective
end KelmansCactus.AtomicBridge.ThetaLocalRoute
