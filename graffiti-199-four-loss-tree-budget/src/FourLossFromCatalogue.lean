import ConnectivitySplice

open private FourBlockPacking.innerSet FourBlockPacking.keptSet FourBlockPacking.mem_singletonOverlap
  FourBlockPacking.four_lost_is_all FourBlockPacking.ports_in_inner FourBlockPacking.separate_kept
  FourBlockPacking.covers_allocated from FourBlockIntegration
open private pair_low_stays from OneSharedIntegration

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
variable (F : FourBlockPacking G)

/-- With one shared singleton high, the splice uses a crossing of the
original connected graph. -/
theorem FourBlockPacking.hamiltonian_with_one_overlap_of_connected [DecidableEq V]
    (losses : (F.lost F.depleted).card = 4) (order : Fintype.card V = 15)
    (shared : F.singletonOverlap.card = 1) (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected) :
    ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian := by
  have balance := F.order_add_overlaps losses
  have empty : F.lost F.terminal = ∅ := Finset.card_eq_zero.mp (by omega)
  have kept : terminalRegion F.terminal.f false = FourBlockPacking.keptSet F := by
    ext v
    simp [terminalKept,FourBlockPacking.keptSet,empty]
  have pInner (i : O) : F.depleted.f i ∈ FourBlockPacking.innerSet F := by
    by_cases lo : i.val < 2
    · exact Or.inr ⟨⟨i.val,lo⟩,rfl⟩
    · exact FourBlockPacking.ports_in_inner F
        (F.mem_lost.mp (FourBlockPacking.four_lost_is_all F losses (by omega))).2
  have qKept (i : O) : F.terminal.f i ∈ FourBlockPacking.keptSet F := ⟨i,by simp [empty],rfl⟩
  have qOut (i : O) : F.terminal.f i ∉ FourBlockPacking.innerSet F := fun h =>
    Set.disjoint_left.mp (FourBlockPacking.separate_kept F) h (qKept i)
  obtain ⟨x,xIn,y,yOut,_,_,xy⟩ := cross_after_fewer_than_three below (D := ∅) (by simp)
    (U := FourBlockPacking.innerSet F) (pInner 0) (qOut 0) (by simp) (by simp)
  have highX : x ∈ singletonPorts F.first ∪ singletonPorts F.second := by
    rcases xIn with (⟨i,rfl⟩|⟨i,rfl⟩)|⟨i,rfl⟩
    · exact Or.inl ⟨i,F.first.outgoing_high (fun h => yOut (Or.inl (Or.inl h))) xy,rfl⟩
    · exact Or.inr ⟨i,F.second.outgoing_high (fun h => yOut (Or.inl (Or.inr h))) xy,rfl⟩
    · obtain ⟨j,eq⟩ := pair_low_stays F.depleted (i := i.castAdd 4) i.isLt xy
      exact (yOut (eq ▸ pInner j)).elim
  obtain ⟨i,_,rfl⟩ := (FourBlockPacking.covers_allocated F losses y).resolve_left yOut
  have highY : terminalHigh i = true := by
    have noLow : ¬ i.val < 2 := by
      intro lo
      obtain ⟨j,eq⟩ := pair_low_stays F.terminal lo xy.symm
      exact Set.disjoint_left.mp (FourBlockPacking.separate_kept F) xIn (eq ▸ qKept j)
    fin_cases i <;> first | rfl | exact (noLow (by decide)).elim
  obtain ⟨p,last⟩ := F.path_to_high_with_one_overlap losses shared highX
  obtain ⟨q,first⟩ := terminal_path_from_high F.terminal.f false F.terminal.edges rfl highY
  have sep : Disjoint (FourBlockPacking.innerSet F) (terminalRegion F.terminal.f false) :=
    kept.symm ▸ FourBlockPacking.separate_kept F
  have full : FourBlockPacking.innerSet F ∪ terminalRegion F.terminal.f false = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    exact (FourBlockPacking.covers_allocated F losses v).imp id (fun h => kept.symm ▸ h)
  exact pathOn_univ_iff_hamiltonian_walk.mp ⟨full ▸ p.join q sep (last.symm ▸ first.symm ▸ xy)⟩

/-- At order at least fifteen the four-loss layout has a
Hamiltonian path using the catalogue tree budget and connectivity
below three deletions. -/
theorem FourBlockPacking.hamiltonian_of_four_losses_of_tree_budget [DecidableEq V]
    (losses : (F.lost F.depleted).card = 4) (order : 15 ≤ Fintype.card V)
    (bound : Catalogue.treeNumber G ≤ 5)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected) :
    (Fintype.card V = 15 ∨ Fintype.card V = 16) ∧
      ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian := by
  have balance := F.order_add_overlaps losses
  refine ⟨by omega,?_⟩
  by_cases empty : F.singletonOverlap.card = 0
  · have dis : Disjoint (singletonPorts F.first) (singletonPorts F.second) := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨i,_,rfl⟩ ⟨j,_,eq⟩
      have mem := (FourBlockPacking.mem_singletonOverlap F).mpr ⟨⟨i,rfl⟩,⟨j,eq⟩⟩
      simp [Finset.card_eq_zero.mp empty] at mem
    obtain ⟨_,A,_,_⟩ := F.depleted_footprint_of_order dis losses order
    obtain ⟨L,_,_⟩ := A.normalize
    exact pathOn_univ_iff_hamiltonian_walk.mp (L.traceable_of_tree_budget bound below)
  · exact F.hamiltonian_with_one_overlap_of_connected losses (by omega) (by omega) below

/-- If the full depleted pair's high set is covered by the two
singleton high sets, its four losses follow from the graph incidences. -/
theorem FourBlockPacking.four_losses_of_high_cover
    (covered : pairPorts F.depleted ⊆ singletonPorts F.first ∪ singletonPorts F.second) :
    (F.lost F.depleted).card = 4 := by
  classical
  let high := (Finset.univ : Finset O).filter fun i : O => 2 ≤ i.val
  have eq : F.lost F.depleted = high := by
    ext i
    rw [F.mem_lost]
    simp only [high,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨And.left,fun h => ⟨h,covered ⟨i,h,rfl⟩⟩⟩
  rw [eq]
  decide

namespace Catalogue

/-- At connectivity three and induced tree number at most five, the
four-forbidden-high branch contradicts nontraceability. The allocation
is given on the original vertices. -/
theorem excludes_four_forbidden_highs_of_tree_budget
    (connectivity : vertexConnectivity G = 3) (bound : treeNumber G ≤ 5)
    (forbidden : Finset V) (count : forbidden.card = 4)
    (highOnly : ∀ v ∈ forbidden, v ∈ pairPorts F.depleted)
    (membership : ∀ v ∈ pairPorts F.depleted,
      v ∈ forbidden ↔ v ∈ singletonPorts F.first ∪ singletonPorts F.second)
    (order : 15 ≤ Fintype.card V) (nontraceable : ¬ Traceable G) : False := by
  classical
  letI : Nonempty V := ⟨F.first.f 0⟩
  have k3 : ConnectivityAtLeast G 3 := connectivity ▸ connectivityAtLeast_vertexConnectivity
  have below (D : Finset V) (h : D.card < 3) : (G.induce {v | v ∉ D}).Preconnected :=
    (k3.2 D h).preconnected
  have lost : (F.lost F.depleted).card = 4 := by
    rw [← Finset.card_map F.depleted.f,F.lost_map_eq_forbidden F.depleted forbidden highOnly membership]
    exact count
  exact nontraceable (traceable_iff_hamiltonian_walk.mpr
    (F.hamiltonian_of_four_losses_of_tree_budget lost order bound below).2)

/-- This form uses only the four-block graph incidences and the
catalogue parameters. The depleted pair is recognized by the inclusion
of its four high vertices in the singleton high sets. -/
theorem traceable_of_depleted_pair_of_tree_budget
    (connectivity : vertexConnectivity G = 3) (bound : treeNumber G ≤ 5)
    (covered : pairPorts F.depleted ⊆ singletonPorts F.first ∪ singletonPorts F.second)
    (order : 15 ≤ Fintype.card V) : Traceable G := by
  classical
  letI : Nonempty V := ⟨F.first.f 0⟩
  have k3 : ConnectivityAtLeast G 3 := connectivity ▸ connectivityAtLeast_vertexConnectivity
  have below (D : Finset V) (h : D.card < 3) : (G.induce {v | v ∉ D}).Preconnected :=
    (k3.2 D h).preconnected
  exact traceable_iff_hamiltonian_walk.mpr
    (F.hamiltonian_of_four_losses_of_tree_budget (F.four_losses_of_high_cover covered) order bound below).2

end Catalogue

#print axioms FourBlockPacking.hamiltonian_with_one_overlap_of_connected
#print axioms FourBlockPacking.hamiltonian_of_four_losses_of_tree_budget
#print axioms FourBlockPacking.four_losses_of_high_cover
#print axioms Catalogue.excludes_four_forbidden_highs_of_tree_budget
#print axioms Catalogue.traceable_of_depleted_pair_of_tree_budget

end Graffiti199Depleted
