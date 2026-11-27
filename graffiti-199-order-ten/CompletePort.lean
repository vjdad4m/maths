import PathRepair

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
variable {A : Set V} {D : Finset V}

/-- A blocked cubic-ended three-vertex path has a port complete to it
when the cubic vertices are independent. -/
theorem exists_complete_port_of_cubic_path_shore
    (S : ThreeVertexShore G A) (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (off : ∀ v ∈ D, v ∉ A) (boundary : ShoreBoundary G D A)
    (ind : ∀ x y, G.degree x = 3 → G.degree y = 3 → ¬ G.Adj x y)
    (degree : G.degree S.left = 3) (P : PathOn G {x | x ≠ S.left}) (no : ¬ Traceable G) :
    ∃ d ∈ D, ∀ v ∈ A, G.Adj d v := by
  classical
  obtain ⟨s,sD,_,eqU,eqZ⟩ := cubic_three_vertex_shore_profile S conn size off boundary degree P no
  have middleMem : S.middle ∈ A :=
    Eq.mpr (congrArg (fun U : Set V => S.middle ∈ U) S.shape) (by simp)
  have low := degree_of_small_deletion_preconnected (G := G)
    (by have n := conn.1; omega : 4 ≤ Fintype.card V)
    (fun R hR => (conn.2 R hR).preconnected) S.middle
  have notThree : G.degree S.middle ≠ 3 := fun h => ind _ _ degree h S.lm
  have choosePort : ∃ d ∈ D.erase s, G.Adj d S.middle := by
    by_contra! absent
    have sub : G.neighborFinset S.middle ⊆ {S.left,S.right,s} := by
      intro v hv
      have mv := (G.mem_neighborFinset _ _).mp hv
      by_cases vA : v ∈ A
      · have h : v ∈ ({S.left,S.middle,S.right} : Set V) := S.shape ▸ vA
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
        rcases h with e|e|e
        · simp [e]
        · exact (G.loopless _ (e ▸ mv)).elim
        · simp [e]
      · have vD := boundary _ middleMem _ vA mv
        by_cases e : v = s
        · simp [e]
        · exact (absent v (Finset.mem_erase.mpr ⟨e,vD⟩) mv.symm).elim
    have upper := Finset.card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at upper
    have bound₁ := Finset.card_insert_le S.left ({S.right,s} : Finset V)
    have bound₂ := Finset.card_insert_le S.right ({s} : Finset V)
    rw [Finset.card_singleton] at bound₂
    omega
  obtain ⟨d,hd,dm⟩ := choosePort
  have leftEdge : G.Adj S.left d := by
    apply (G.mem_neighborFinset _ _).mp
    rw [eqU]
    exact Finset.mem_insert_of_mem hd
  have rightEdge : G.Adj S.right d := by
    apply (G.mem_neighborFinset _ _).mp
    rw [eqZ]
    exact Finset.mem_insert_of_mem hd
  refine ⟨d,Finset.mem_of_mem_erase hd,?_⟩
  intro v hv
  have h : v ∈ ({S.left,S.middle,S.right} : Set V) := S.shape ▸ hv
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  rcases h with e|e|e
  · exact e.symm ▸ leftEdge.symm
  · exact e.symm ▸ dm
  · exact e.symm ▸ rightEdge.symm

#print axioms exists_complete_port_of_cubic_path_shore

end Graffiti199Depleted.Catalogue
