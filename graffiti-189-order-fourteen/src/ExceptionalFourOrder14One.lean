import TinyFourOrder14OneModel


namespace FourOrder14One
open Finset

def exceptionalAdd (e : Bool) (w u v : Vertex) : Bool :=
  edge 4 8 exceptionMarks e true false false true u v ||
  decide ((u=1 ∧ v=w) ∨ (v=1 ∧ u=w))

def exceptionalBadDegree (e : Bool) : Prop :=
  (∀ w : Vertex, edge 4 8 exceptionMarks e true false false true 1 w=true → w=0 ∨ w=2) ∧
  ∀ w : Vertex, w≠0 → w≠1 → w≠2 → w∉({0,4,8,12,13}:Finset Vertex) →
  ∃ z ∈ ({0,4,8,12,13}:Finset Vertex),
    4 < (univ.filter fun y => y≠z ∧ !(exceptionalAdd e w z y) = true ∧
      ∃ u : Vertex, exceptionalAdd e w z u=true ∧ exceptionalAdd e w u y=true).card

noncomputable instance (e : Bool) : Decidable (exceptionalBadDegree e) := by
  unfold exceptionalBadDegree
  infer_instance

set_option maxRecDepth 15000 in
set_option maxHeartbeats 3000000 in
theorem exceptional_degree_certificate (e : Bool) : exceptionalBadDegree e := by
  cases e <;> decide

#print axioms exceptional_degree_certificate
end FourOrder14One
