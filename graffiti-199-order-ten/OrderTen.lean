import OrderTenSingleton

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- A three-cut with two different components of order at least three
forces a Hamiltonian path through order ten, under three-connectivity
and the bound of five on induced trees. -/
theorem LargeCrossingFailure.traceable_of_order_le_ten
    (F : LargeCrossingFailure G) (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : Fintype.card V ≤ 10) : Traceable G := by
  classical
  let A := componentShore F.cut F.first
  let B := componentShore F.cut F.second
  by_cases full : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ F.cut
  · exact F.traceable_of_order_le_ten_of_cover conn budget order full
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  have offA := componentShore_off_cut F.cut F.first
  have offB := componentShore_off_cut F.cut F.second
  have boundA := componentShore_boundary F.cut F.first
  have boundB := componentShore_boundary F.cut F.second
  have apart := componentShore_disjoint F.different
  let U := (F.cut ∪ A.toFinset) ∪ B.toFinset
  have memU (v : V) : v ∈ U ↔ v ∈ A ∨ v ∈ B ∨ v ∈ F.cut := by
    change v ∈ (F.cut ∪ A.toFinset) ∪ B.toFinset ↔ _
    simp only [Finset.mem_union,Set.mem_toFinset]
    tauto
  have proper : U ≠ Finset.univ := fun eq => full (fun v => (memU v).mp (eq.symm ▸ Finset.mem_univ v))
  have small : U.card < (Finset.univ : Finset V).card := by
    apply Nat.lt_of_not_ge
    intro ge
    exact proper (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ge)
  have dA : Disjoint F.cut A.toFinset :=
    Finset.disjoint_left.mpr (fun x hx hA => offA x hx (Set.mem_toFinset.mp hA))
  have dB : Disjoint (F.cut ∪ A.toFinset) B.toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hx hB
    rcases Finset.mem_union.mp hx with cut|lhs
    · exact offB x cut (Set.mem_toFinset.mp hB)
    · exact Set.disjoint_left.mp apart (Set.mem_toFinset.mp lhs) (Set.mem_toFinset.mp hB)
  have cardU : U.card = 3 + Nat.card A + Nat.card B := by
    change ((F.cut ∪ A.toFinset) ∪ B.toFinset).card = _
    rw [Finset.card_union_of_disjoint dB,Finset.card_union_of_disjoint dA,F.size,
      Set.toFinset_card,Set.toFinset_card,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  have ca : 3 ≤ Nat.card A := F.first_large
  have cb : 3 ≤ Nat.card B := F.second_large
  obtain ⟨r,_,rU⟩ := Finset.exists_mem_not_mem_of_card_lt_card small
  have rA : r ∉ A := fun h => rU ((memU r).mpr (Or.inl h))
  have rB : r ∉ B := fun h => rU ((memU r).mpr (Or.inr (Or.inl h)))
  have rD : r ∉ F.cut := fun h => rU ((memU r).mpr (Or.inr (Or.inr h)))
  rw [Finset.card_univ] at small
  have nA : Nat.card A = 3 := by omega
  have nB : Nat.card B = 3 := by omega
  have complete : insert r U = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_insert_of_not_mem rU,Finset.card_univ]
    omega
  have cover (v : V) : v ∈ A ∨ v ∈ B ∨ v ∈ F.cut ∨ v = r := by
    have hv : v ∈ insert r U := complete.symm ▸ Finset.mem_univ v
    rcases Finset.mem_insert.mp hv with eq|mem
    · exact Or.inr (Or.inr (Or.inr eq))
    · rcases (memU v).mp mem with va|vb|vd
      · exact Or.inl va
      · exact Or.inr (Or.inl vb)
      · exact Or.inr (Or.inr (Or.inl vd))
  have noA (v : V) (va : v ∈ A) : ¬ G.Adj r v :=
    fun rv => rD (boundA _ va _ rA rv.symm)
  have noB (v : V) (vb : v ∈ B) : ¬ G.Adj r v :=
    fun rv => rD (boundB _ vb _ rB rv.symm)
  have sub : G.neighborFinset r ⊆ F.cut := by
    intro v hv
    have edge := (G.mem_neighborFinset _ _).mp hv
    rcases cover v with va|vb|vd|eq
    · exact (noA _ va edge).elim
    · exact (noB _ vb edge).elim
    · exact vd
    · exact (G.loopless r (eq ▸ edge)).elim
  have low := degree_of_small_deletion_preconnected (G := G)
    (by have n := conn.1; omega : 4 ≤ Fintype.card V)
    (fun R hR => (conn.2 R hR).preconnected) r
  have eq := Finset.eq_of_subset_of_card_le sub (by rw [F.size,G.card_neighborFinset_eq_degree]; exact low)
  have rPorts (v : V) (hv : v ∈ F.cut) : G.Adj r v :=
    (G.mem_neighborFinset _ _).mp (eq.symm ▸ hv)
  exact traceable_of_two_three_shores_and_singleton conn budget F.size rA rB rD rPorts noA noB
    offA offB boundA boundB apart cover (componentShore_connected F.cut F.first)
    (componentShore_connected F.cut F.second) nA nB

/-- The minimum-order independent-cubic crossing-failure branch now
requires at least eleven vertices. -/
theorem order_ge_eleven_of_crossing_failure [DecidableEq V]
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    (fail : ¬ CrossingBetweenSurvivingEdges G) : 11 ≤ Fintype.card V := by
  obtain ⟨F,_⟩ := high_cut_of_crossing_failure_of_independent_cubics smaller conn budget order no ind fail
  by_contra! small
  exact no (F.traceable_of_order_le_ten conn budget (by omega))

#print axioms LargeCrossingFailure.traceable_of_order_le_ten
#print axioms order_ge_eleven_of_crossing_failure

end Graffiti199Depleted.Catalogue
