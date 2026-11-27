import DistanceTwoCut189
import Mathlib.SetTheory.Cardinal.Finite

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem induced_reachable_of_walk_in (A : Finset V)
    {u v : V} (p : G.Walk u v) (stays : ∀ z∈p.support,z∈A)
    (ua : u∈A) (va : v∈A) :
    (G.induce (↑A : Set V)).Reachable ⟨u,ua⟩ ⟨v,va⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons u w z uw p ih =>
    have ps (t : V) (h : t∈p.support) : t∈A := stays t (by simpa only [support_cons,List.mem_cons] using Or.inr h)
    have wa := ps _ p.start_mem_support
    have e : (G.induce (↑A : Set V)).Adj ⟨u,ua⟩ ⟨w,wa⟩ := uw
    exact e.reachable.trans (ih ps wa va)

theorem induced_connected_of_joined (A : Finset V) (ne : A.Nonempty)
    (join : ∀ u∈A, ∀ v∈A, ∃ p : G.Walk u v,∀ z∈p.support,z∈A) :
    (G.induce (↑A : Set V)).Connected := by
  obtain ⟨x,xA⟩ := ne
  letI : Nonempty ↑(↑A : Set V) := ⟨⟨x,xA⟩⟩
  apply SimpleGraph.Connected.mk
  intro u v
  obtain ⟨p,ps⟩ := join u.val u.property v.val v.property
  exact induced_reachable_of_walk_in A p ps u.property v.property

theorem singleton_deletion_connected
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected) (z : V) :
    (G.induce {x : V | x≠z}).Connected := by
  have eq : ((↑({z} : Finset V) : Set V)ᶜ) = {x : V | x≠z} := by ext x; simp
  have c := conn ({z} : Finset V) (by simp)
  rw [eq] at c
  exact c

theorem component_card_gt_one_of_disconnected (a b : V)
    (large : 3≤Fintype.card V)
    (dis : ¬(G.induce {x : V | x≠a ∧ x≠b}).Connected) :
    1 < Nat.card (G.induce {x : V | x≠a ∧ x≠b}).ConnectedComponent := by
  classical
  let J := G.induce {x : V | x≠a ∧ x≠b}
  obtain ⟨x,xab⟩ : ∃ x : V,x∉({a,b} : Finset V) := by
    by_contra! h
    have sub : univ ⊆ ({a,b} : Finset V) := fun _ _ => h _
    have c := card_le_card sub
    rw [card_univ] at c
    have e := card_insert_le a ({b} : Finset V)
    simp at e
    omega
  have xo : x≠a ∧ x≠b := by simpa using xab
  letI : Nonempty ↑({x : V | x≠a ∧ x≠b} : Set V) := ⟨⟨x,xo⟩⟩
  by_contra! low
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have small : Fintype.card J.ConnectedComponent≤1 := by
    rw [←Nat.card_eq_fintype_card]
    exact low
  have ss := Fintype.card_le_one_iff_subsingleton.mp small
  apply dis
  change J.Connected
  apply SimpleGraph.Connected.mk
  intro u v
  exact ConnectedComponent.exact (ss.elim (J.connectedComponentMk u) (J.connectedComponentMk v))

#print axioms induced_reachable_of_walk_in
#print axioms induced_connected_of_joined
#print axioms component_card_gt_one_of_disconnected
end Graffiti189LongestPath.CrossSaturation
