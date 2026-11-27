import NeighborhoodAdapter

open private appendDisjoint appendDisjoint_region from NeighborhoodAdapter

namespace Graffiti199Depleted

open Graffiti199K2.NearPacking.Depleted
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] {loss : Bool}

private theorem high_first_block (i : Fin 4) (hi : singletonHigh i = true) :
    high (i.castAdd 4) = true := by
  fin_cases i
  · cases hi
  · rfl
  · rfl
  · rfl

private theorem high_second_block (i : Fin 4) (hi : singletonHigh i = true) :
    high (i.natAdd 4) = true := by
  fin_cases i
  · cases hi
  · rfl
  · rfl
  · rfl

/-- Build the four-loss footprint from separately supplied blocks. The
reassigned tips are given as vertices of the original graph, and the proof
recovers their local indices in the two singleton blocks. -/
theorem depleted_footprint_of_blocks (S T : PrivateSingleton G) (D : Fin 2 ↪ V)
    (sepST : Disjoint (labelRegion S.f) (labelRegion T.f))
    (sepD : Disjoint (labelRegion S.f ∪ labelRegion T.f) (labelRegion D))
    (looseS : ¬ G.Adj (S.f 2) (S.f 3)) (looseT : ¬ G.Adj (T.f 2) (T.f 3))
    (lowEdge : G.Adj (D 0) (D 1))
    (degreeD : ∀ i, G.degree (D i) = 3)
    (W : Fin 4 ↪ V)
    (highW : ∀ j, (∃ i, singletonHigh i = true ∧ S.f i = W j) ∨
      (∃ i, singletonHigh i = true ∧ T.f i = W j))
    (firstHalf : G.Adj (D 0) (W 0) ∧ G.Adj (D 0) (W 1) ∧ G.Adj (W 0) (W 1))
    (secondHalf : G.Adj (D 1) (W 2) ∧ G.Adj (D 1) (W 3) ∧ G.Adj (W 2) (W 3))
    (Q : O ↪ V)
    (terminal : ∀ a b, (a,b) ∈ terminalEdges → G.Adj (Q a) (Q b))
    (degreeQ : ∀ i ∈ ([0,1] : List O), G.degree (Q i) = 3)
    (separate : Disjoint ((labelRegion S.f ∪ labelRegion T.f) ∪ labelRegion D)
      (terminalRegion Q loss))
    (whole : ∀ v, v ∈ (labelRegion S.f ∪ labelRegion T.f) ∪ labelRegion D ∨
      v ∈ terminalRegion Q loss) :
    ∃ F : DepletedFootprint G loss, F.inner 3 = S.f 3 ∧ F.terminal = Q := by
  classical
  let q : I ↪ V := appendDisjoint S.f T.f sepST
  have qReg : labelRegion q = labelRegion S.f ∪ labelRegion T.f :=
    appendDisjoint_region S.f T.f sepST
  have dis : Disjoint (labelRegion q) (labelRegion D) := qReg.symm ▸ sepD
  let inner : K ↪ V := appendDisjoint q D dis
  have innerReg : innerRegion inner = (labelRegion S.f ∪ labelRegion T.f) ∪ labelRegion D :=
    (appendDisjoint_region q D dis).trans (congrArg (· ∪ labelRegion D) qReg)
  have has (j : Fin 4) : ∃ i : I, high i = true ∧ q i = W j := by
    rcases highW j with ⟨i,hi,eq⟩|⟨i,hi,eq⟩
    · exact ⟨i.castAdd 4,high_first_block i hi,(Fin.append_left S.f T.f i).trans eq⟩
    · exact ⟨i.natAdd 4,high_second_block i hi,(Fin.append_right S.f T.f i).trans eq⟩
  let reassigned : Fin 4 ↪ I := ⟨fun j => (has j).choose,fun j k hk =>
    W.injective ((has j).choose_spec.2.symm.trans ((congrArg (fun i => q i) hk).trans
      (has k).choose_spec.2))⟩
  have locate (j : Fin 4) : inner (inside (reassigned j)) = W j :=
    (Fin.append_left q D (reassigned j)).trans (has j).choose_spec.2
  have fixed : ∀ i j, (i,j) ∈ fixedInnerEdges → G.Adj (inner i) (inner j) := by
    intro i j h
    simp only [fixedInnerEdges,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with e|e|e|e|e|e|e|e|e <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
    · exact S.edges 0 1 (by decide)
    · exact S.edges 0 2 (by decide)
    · exact S.edges 0 3 (by decide)
    · exact S.edges 1 2 (by decide)
    · exact T.edges 0 1 (by decide)
    · exact T.edges 0 2 (by decide)
    · exact T.edges 0 3 (by decide)
    · exact T.edges 1 2 (by decide)
    · exact lowEdge
  have off : ∀ i j, (i,j) ∈ forbidden → ¬ G.Adj (inner i) (inner j) := by
    intro i j h
    simp only [forbidden,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with e|e|e|e <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
    · exact S.looseNonedge
    · exact looseS
    · exact T.looseNonedge
    · exact looseT
  have innerDegree : ∀ i ∈ ([0,4,8,9] : List K), G.degree (inner i) = 3 := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact S.degree
    · exact T.degree
    · exact degreeD 0
    · exact degreeD 1
  refine ⟨⟨inner,Q,reassigned,fun j => (has j).choose_spec.1,fixed,?_,?_,off,
    terminal,innerDegree,degreeQ,innerReg.symm ▸ separate,?_⟩,rfl,rfl⟩
  · rw [locate 0,locate 1]
    exact firstHalf
  · rw [locate 2,locate 3]
    exact secondHalf
  · intro v
    exact (whole v).imp (fun h => innerReg.symm ▸ h) id

/-- The standalone orders 15 and 16 have Mathlib Hamiltonian paths under
the induced-cut version of the connectivity hypotheses. -/
theorem hamiltonian_depleted_of_induced_cuts [DecidableEq V] (F : DepletedFootprint G loss)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (three : ∀ D : Finset V, D.card = 3 →
      (G.induce {v | v ∉ D}).Preconnected ∨
        ∃ s : V, s ∉ D ∧ (∀ t : V, t ∉ D → ¬ G.Adj s t) ∧
          (G.induce {v | v ∉ D ∧ v ≠ s}).Preconnected)
    (looseOff : G.degree (F.inner 3) ≠ 3) :
    (Fintype.card V = if loss then 15 else 16) ∧
      ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian := by
  have size : 10 ≤ Fintype.card V := by
    simpa using Fintype.card_le_of_injective _ F.inner.injective
  obtain ⟨order,path⟩ := depleted_footprint_order_and_path F
    (edgeReach_of_induced_singleton_cuts below three)
    (degree_of_small_deletion_preconnected (by omega) below (F.inner 3)) looseOff
  exact ⟨order,pathOn_univ_iff_hamiltonian_walk.mp path⟩

#print axioms depleted_footprint_of_blocks
#print axioms hamiltonian_depleted_of_induced_cuts

end Graffiti199Depleted
