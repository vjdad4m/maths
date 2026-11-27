import CoreRepair

open private innerHighMap inner_index_cases from NormalizedDepleted

namespace Graffiti199Depleted

open SimpleGraph Graffiti199K2.NearPacking.Depleted

variable {V : Type*} {G : SimpleGraph V} {loss : Bool}

/-- After deleting fewer than three vertices, preconnectedness forces
a crossing between any retained vertices on opposite sides. -/
theorem cross_after_fewer_than_three
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    {D : Finset V} (small : D.card < 3) {U : Set V} {a c : V}
    (au : a ∈ U) (cu : c ∉ U) (aD : a ∉ D) (cD : c ∉ D) :
    ∃ x ∈ U, ∃ y ∉ U, x ∉ D ∧ y ∉ D ∧ G.Adj x y := by
  obtain ⟨w⟩ := below D small ⟨a,aD⟩ ⟨c,cD⟩
  let U' : Set {v : V // v ∉ D} := {v | v.val ∈ U}
  obtain ⟨x,xU,y,yU,e⟩ := crossingOnWalk (U := U') w au cu
  exact ⟨x.val,xU,y.val,yU,x.property,y.property,e⟩

/-- Excluding at most two inner high vertices is enough when each other
inner high vertex can be a spanning-path endpoint. -/
theorem NormalizedDepleted.traceable_with_at_most_two_exclusions (L : NormalizedDepleted G loss)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (B : Finset I) (small : B.card ≤ 2)
    (ends : ∀ i : I, high i = true → i ∉ B →
      ∃ p : PathOn G (innerRegion L.inner), p.last = L.inner (inside i)) :
    Nonempty (PathOn G Set.univ) := by
  let h := innerHighMap.trans L.inner
  let D := B.map h
  have ds : D.card < 3 := by
    have count : D.card = B.card := Finset.card_map h
    omega
  have keep : terminalKept loss 0 = true := by cases loss <;> rfl
  have inner8 : L.inner 8 ∉ D := by
    intro mem
    obtain ⟨i,_,e⟩ := Finset.mem_map.mp mem
    have eq : inside i = 8 := L.inner.injective e
    have val := congrArg (fun k : K => k.val) eq
    have lt := i.isLt
    change i.val = 8 at val
    omega
  have terminal0 : L.terminal 0 ∉ D := by
    intro mem
    obtain ⟨i,_,e⟩ := Finset.mem_map.mp mem
    exact Set.disjoint_left.mp L.separate ⟨inside i,e⟩ ⟨0,keep,rfl⟩
  obtain ⟨x,⟨k,rfl⟩,y,off,xD,_,edge⟩ := cross_after_fewer_than_three below ds
    (U := innerRegion L.inner) ⟨8,rfl⟩ (fun h => Set.disjoint_left.mp L.separate h ⟨0,keep,rfl⟩)
    inner8 terminal0
  rcases inner_index_cases L.row k with ⟨i,rfl,hi⟩|⟨ns,eq⟩
  · have keepI : i ∉ B := fun mem => xD (Finset.mem_map.mpr ⟨i,mem,rfl⟩)
    obtain ⟨p,last⟩ := ends i hi keepI
    exact L.finish_with_contact p ((L.cover y).resolve_left off) (last.symm ▸ edge)
  · obtain ⟨j,_,e⟩ := L.innerLow k ns eq y edge
    exact (off ⟨j,e⟩).elim

/-- The four-loss disjoint-singleton splice follows from the catalogue
tree budget and ordinary connectivity after deleting fewer than three vertices. -/
theorem NormalizedDepleted.traceable_of_tree_budget [Fintype V]
    (L : NormalizedDepleted G loss) (bound : Catalogue.treeNumber G ≤ 5)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected) :
    Nonempty (PathOn G Set.univ) := by
  have usual (b : Bool) (extra : b = true → G.Adj (L.inner 3) (L.inner 7))
      (small : (blocked L.row b).card ≤ 2) : Nonempty (PathOn G Set.univ) := by
    apply L.traceable_with_at_most_two_exclusions below (blocked L.row b) small
    intro i hi off
    exact L.inner_path extra (fun e =>
      off (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,e⟩))
  by_cases edge : G.Adj (L.inner 3) (L.inner 7)
  · rcases TreeRepair.baseline_or_repair L.row true L.possible with small|⟨bad,_⟩
    · exact usual true (fun _ => edge) small
    · cases bad
  · rcases TreeRepair.baseline_or_repair L.row false L.possible with small|⟨_,row⟩
    · exact usual false (fun h => by cases h) small
    · exact L.traceable_with_at_most_two_exclusions below ∅ (by simp)
        (fun _ hi _ => TreeRepair.repaired_path_at_any_high L bound edge row hi)

#print axioms cross_after_fewer_than_three
#print axioms NormalizedDepleted.traceable_of_tree_budget

end Graffiti199Depleted
