import CambyPathEnds133

namespace Graffiti133Bicycle
open SimpleGraph Finset
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem component_after_removing (B : Finset V) (u : V) (hu : u∉B) :
    ∃ S : Finset V, u∈S ∧ Disjoint S B ∧ (G.induce (S : Set V)).Connected ∧
      ∀ x∈S, ∀ y∉B, G.Adj x y → y∈S := by
  classical
  let X : Set V := {v | v∉B}
  let J := G.induce X
  let a : X := ⟨u,hu⟩
  let C := J.connectedComponentMk a
  let T : Finset X := Finset.univ.filter (·∈C.supp)
  let S : Finset V := T.image Subtype.val
  have sMem (v : V) : v∈S ↔ ∃ x : X, x∈C.supp ∧ x.val=v := by
    change v∈T.image Subtype.val ↔ _
    simp [T]
  have home : a∈C.supp := (C.mem_supp_iff a).mpr rfl
  refine ⟨S,(sMem _).mpr ⟨a,home,rfl⟩,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v ha hb
    obtain ⟨x,hx,rfl⟩ := (sMem _).mp ha
    exact x.property hb
  · let F : J.induce C.supp →g G.induce (S : Set V) :=
      ⟨fun x => ⟨x.val.val,(sMem _).mpr ⟨x.val,x.property,rfl⟩⟩,fun e=>e⟩
    apply C.connected_induce_supp.map F
    intro v
    obtain ⟨x,hx,e⟩ := (sMem _).mp v.property
    exact ⟨⟨x,hx⟩,Subtype.ext e⟩
  · intro x hx y hy e
    obtain ⟨z,hz,rfl⟩ := (sMem _).mp hx
    let w : X := ⟨y,hy⟩
    have zw : J.Adj z w := e
    exact (sMem _).mpr ⟨w,(C.mem_supp_congr_adj zw).mp hz,rfl⟩

theorem disjoint_component_of_outside_anchor (B S T : Finset V)
    (hS : ∀ x∈S, ∀ y∉B, G.Adj x y → y∈S)
    (outT : Disjoint T B) (conn : (G.induce (T : Set V)).Connected)
    {u : V} (uT : u∈T) (uS : u∉S) : Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro v hv hvt
  let a : (T : Set V) := ⟨v,hvt⟩
  let b : (T : Set V) := ⟨u,uT⟩
  obtain ⟨p⟩ := conn a b
  have go : ∀ {x y : (T : Set V)}, (G.induce (T : Set V)).Walk x y →
      x.val∈S → y.val∈S := by
    intro x y q
    induction q with
    | nil => exact id
    | @cons i j k e q ih =>
      intro hi
      apply ih
      exact hS _ hi _ (fun h=>Finset.disjoint_left.mp outT j.property h) e
  exact uS (go p hv)

#print axioms component_after_removing
#print axioms disjoint_component_of_outside_anchor
end Graffiti133Bicycle
