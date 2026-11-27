import NestedCoreThreeGate133
import NestedCoreC7CrossBudget133

namespace Graffiti133NestedCore
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7
  Graffiti133MultiWeighted
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

def trimToGates (G : SimpleGraph V) (K A : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((x∈K ↔ y∈K) ∨ x∈A ∨ y∈A)
  symm := by
    intro x y h
    exact ⟨h.1.symm,h.2.imp Iff.symm Or.symm⟩
  loopless x h := G.loopless x h.1

theorem three_gates_with_extra_crossings
    (K A : Finset V) (ak : A⊆K) (a3 : A.card=3) (h4 : FourCycleFree G)
    (sees : ∀ x∉K,∃ a∈A,G.Adj x a) :
    (∑ w : V,localIndependence G w)+4*K.card≤
      (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+
        4*Fintype.card V+
        2*((Finset.univ \ K).filter fun x=>(gateTags G A x).card=3).card+
        2*(G.edgeFinset \ (trimToGates G K A).edgeFinset).card := by
  let J := trimToGates G K A
  have le : J≤G := fun _ _ e=>e.1
  have j4 : FourCycleFree J :=
    fun a b x y ne ax bx ay byy=>h4 a b x y ne (le ax) (le bx) (le ay) (le byy)
  have same : J.induce (K : Set V)=G.induce (K : Set V) := by
    ext x y
    exact ⟨fun e=>e.1,fun e=>⟨e,Or.inl (iff_of_true x.property y.property)⟩⟩
  have seesJ (x : V) (xo : x∉K) : ∃ a∈A,J.Adj x a := by
    obtain ⟨a,am,e⟩ := sees x xo
    exact ⟨a,am,e,Or.inr (Or.inr am)⟩
  have gateJ (x : V) (xo : x∉K) (y : V) (yk : y∈K) (xy : J.Adj x y) : y∈A := by
    rcases xy.2 with e|e|e
    · exact (xo (e.mpr yk)).elim
    · exact (xo (ak e)).elim
    · exact e
  have tag_eq (x : V) : gateTags J A x=gateTags G A x := by
    ext a
    apply Iff.intro
    · intro m
      obtain ⟨am,e⟩ := Finset.mem_filter.mp m
      exact Finset.mem_filter.mpr ⟨am,le e⟩
    · intro m
      obtain ⟨am,e⟩ := Finset.mem_filter.mp m
      exact Finset.mem_filter.mpr ⟨am,e,Or.inr (Or.inr am)⟩
  have signed := three_gate_preserves_score_up_to_triples (G:=J) K A ak a3 j4 seesJ gateJ
  simp only [same,tag_eq] at signed
  have added := score_difference_le_twice_added_edges J le h4
  have aux {g j b n k tr ed : Nat} (p : j+4*k≤b+4*n+2*tr) (q : g≤j+2*ed) :
      g+4*k≤b+4*n+2*tr+2*ed := by omega
  exact aux signed added

theorem C7_nested_three_gate_crossing_budget_mean_four (K A : Finset V)
    (ak : A⊆K) (a3 : A.card=3) (h4 : FourCycleFree G)
    (H : Hole (G.induce (K : Set V)) 7)
    (h9 : ¬∃ p : Fin 9→(K : Set V),InducedPath (G.induce (K : Set V)) p)
    (dom : ∀ y,Outside H.c y→∃ i,(G.induce (K : Set V)).Adj y (H.c i))
    (sees : ∀ x∉K,∃ a∈A,G.Adj x a)
    (budget : 3*(multiVertices H).card+2*(G.edgeFinset \ (trimToGates G K A).edgeFinset).card≤12) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  have lo := C7_dominating_slack_depending_on_multis H (restricted_c4 h4 K) h9 dom
  have card : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
  rw [card] at lo
  have signed := three_gates_with_extra_crossings K A ak a3 h4 sees
  have t := at_most_one_triple_gate_vertex h4 A (Finset.univ \ K) a3
  have aux {l b n k p q u : Nat} (lo : b+14≤4*k+3*p)
      (sc : l+4*k≤b+4*n+2*u+2*q) (t : u≤1) (budget : 3*p+2*q≤12) :
      l≤4*n := by omega
  exact aux lo signed t budget

#print axioms three_gates_with_extra_crossings
#print axioms C7_nested_three_gate_crossing_budget_mean_four
end Graffiti133NestedCore
