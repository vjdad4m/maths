import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open Finset SimpleGraph

/-- A spanning shore path can attach to both cuts, or start at one
specified cut and have its other endpoint free. -/
inductive WingMask
  | terminal
  | aFree
  | bFree

def WingRealizes {V : Type*} (G : SimpleGraph V) (a b : V) (S : Finset V) : WingMask → Prop
  | .terminal => ∃ u v, G.Adj a u ∧ G.Adj b v ∧ RouteOn G S u v
  | .aFree => ∃ u v, G.Adj a u ∧ RouteOn G S u v
  | .bFree => ∃ u v, G.Adj b u ∧ RouteOn G S u v

def ComplementaryWings {V : Type*} (G : SimpleGraph V) (a b : V) (S T : Finset V) : Prop :=
  (WingRealizes G a b S .terminal ∧ (WingRealizes G a b T .aFree ∨ WingRealizes G a b T .bFree)) ∨
  (WingRealizes G a b T .terminal ∧ (WingRealizes G a b S .aFree ∨ WingRealizes G a b S .bFree))

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Path signatures already refer to the original graph. The global
step consists only of concatenating witnesses through the two cuts. -/
theorem traceable_of_complementary_wings {a b : V} (ab : a≠b) {S T : Finset V}
    (sep : Disjoint S T) (aS : a∉S) (bS : b∉S) (aT : a∉T) (bT : b∉T)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈S ∨ z∈T)
    (sig : ComplementaryWings G a b S T) :
    ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have join {A B : Finset V} (sep' : Disjoint A B)
      (aA : a∉A) (bA : b∉A) (aB : a∉B) (bB : b∉B)
      (cover' : ∀ z : V,z=a ∨ z=b ∨ z∈A ∨ z∈B)
      (term : WingRealizes G a b A .terminal)
      (r : WingRealizes G a b B .aFree ∨ WingRealizes G a b B .bFree) :
      ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
    obtain ⟨u,v,au,bv,p⟩ := term
    have mid := (p.prefix au aA).suffix bv.symm
      (fun h=>(mem_insert.mp h).elim ab.symm bA)
    have dis : Disjoint (insert b (insert a A)) B := by
      apply disjoint_left.mpr
      intro x xA xB
      rcases mem_insert.mp xA with rfl|xA
      · exact bB xB
      rcases mem_insert.mp xA with rfl|xA
      · exact aB xB
      exact disjoint_left.mp sep' xA xB
    have pack {x y : V} (full : RouteOn G (insert b (insert a A)∪B) x y) :
        ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
      obtain ⟨q,qp,qs⟩ := full
      refine ⟨x,y,q,qp,fun z=>(qs z).mpr ?_⟩
      rcases cover' z with rfl|rfl|zA|zB
      · simp
      · simp
      · exact mem_union_left _ (mem_insert_of_mem (mem_insert_of_mem zA))
      exact mem_union_right _ zB
    rcases r with ⟨x,y,ax,q⟩|⟨x,y,bx,q⟩
    · exact pack (mid.reverse.join q dis ax)
    exact pack (mid.join q dis bx)
  rcases sig with h|h
  · exact join sep aS bS aT bT cover h.1 h.2
  exact join sep.symm aT bT aS bS (fun z=>(cover z).imp id (fun h=>h.imp id Or.symm)) h.1 h.2

#print axioms traceable_of_complementary_wings
end Graffiti189LongestPath.CrossSaturation
