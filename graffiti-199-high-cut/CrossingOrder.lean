import TwoShortShores

open private neighbor_on_connected_shore from HighCutProfile

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem clique_or_path_of_three {A : Set V} (connected : (G.induce A).Connected)
    (count : Nat.card A = 3) : A.Pairwise G.Adj ∨ Nonempty (ThreeVertexShore G A) := by
  classical
  by_cases cl : A.Pairwise G.Adj
  · exact Or.inl cl
  right
  change ¬ (∀ x ∈ A, ∀ z ∈ A, x ≠ z → G.Adj x z) at cl
  push_neg at cl
  obtain ⟨x,xA,z,zA,xz,notXZ⟩ := cl
  letI : Fintype A := Fintype.ofFinite A
  have countFin : A.toFinset.card = 3 := by rw [Set.toFinset_card,← Nat.card_eq_fintype_card,count]
  have cd : ({x,z} : Finset V).card < A.toFinset.card := by rw [Finset.card_pair xz,countFin]; decide
  obtain ⟨y,hy,out⟩ := Finset.exists_mem_not_mem_of_card_lt_card cd
  have yA := Set.mem_toFinset.mp hy
  have xy : x ≠ y := fun e => out (by simp [← e])
  have yz : y ≠ z := fun e => out (by simp [e])
  have sets : ({x,y,z} : Finset V) = A.toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl
      · exact Set.mem_toFinset.mpr xA
      · exact hy
      · exact Set.mem_toFinset.mpr zA
    · rw [countFin,Finset.card_insert_of_not_mem (by simp [xy,xz]),Finset.card_pair yz]
  have form : A = {x,y,z} := by
    ext v
    have h : v ∈ ({x,y,z} : Finset V) ↔ v ∈ A := sets ▸ Set.mem_toFinset
    simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] using h.symm
  have xEdge : G.Adj x y := by
    obtain ⟨v,hv,ex⟩ := neighbor_on_connected_shore connected (by omega) xA
    rw [form] at hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with eq|eq|eq
    · exact (G.loopless x (eq ▸ ex)).elim
    · exact eq ▸ ex
    · exact (notXZ (eq ▸ ex)).elim
  have zEdge : G.Adj y z := by
    obtain ⟨v,hv,ez⟩ := neighbor_on_connected_shore connected (by omega) zA
    rw [form] at hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with eq|eq|eq
    · exact (notXZ (eq ▸ ez.symm)).elim
    · exact eq ▸ ez.symm
    · exact (G.loopless z (eq ▸ ez)).elim
  exact ⟨⟨x,y,z,form,xEdge,zEdge,xz,notXZ⟩⟩

omit [DecidableRel G.Adj] in
private theorem two_distinct_of_card_three {A : Set V} (count : Nat.card A = 3) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ y := by
  letI : Fintype A := Fintype.ofFinite A
  have nA : Fintype.card A = 3 := by simpa only [← Nat.card_eq_fintype_card] using count
  haveI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,y,xy⟩ := exists_pair_ne A
  exact ⟨x,x.property,y,y.property,fun e => xy (Subtype.ext e)⟩

/-- Any large surviving-edge crossing failure on at most nine vertices
has exactly two components of order three and yields a Hamiltonian path.
The components can each be a triangle or an induced three-vertex path. -/
theorem LargeCrossingFailure.traceable_of_order_le_nine
    (F : LargeCrossingFailure G) (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : Fintype.card V ≤ 9) : Traceable G := by
  classical
  let A := componentShore F.cut F.first
  let B := componentShore F.cut F.second
  have offA := componentShore_off_cut F.cut F.first
  have offB := componentShore_off_cut F.cut F.second
  have boundA := componentShore_boundary F.cut F.first
  have boundB := componentShore_boundary F.cut F.second
  have apart := componentShore_disjoint F.different
  have A3 : 3 ≤ Nat.card A := F.first_large
  have B3 : 3 ≤ Nat.card B := F.second_large
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  let U := (F.cut ∪ A.toFinset) ∪ B.toFinset
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
  have upper : U.card ≤ Fintype.card V := Finset.card_le_univ U
  have sizeA : Nat.card A = 3 := by omega
  have sizeB : Nat.card B = 3 := by omega
  have eqU : U = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    (by rw [Finset.card_univ]; omega)
  have cover (x : V) : x ∈ A ∨ x ∈ B ∨ x ∈ F.cut := by
    have hx : x ∈ U := eqU.symm ▸ Finset.mem_univ x
    change x ∈ (F.cut ∪ A.toFinset) ∪ B.toFinset at hx
    simp only [Finset.mem_union,Set.mem_toFinset] at hx
    tauto
  rcases clique_or_path_of_three (componentShore_connected F.cut F.first) sizeA with clA|p3A
  · rcases clique_or_path_of_three (componentShore_connected F.cut F.second) sizeB with clB|p3B
    · exact traceable_of_two_clique_shores conn F.size apart offA offB boundA boundB
        clA clB (two_distinct_of_card_three sizeA) (two_distinct_of_card_three sizeB) cover
    · obtain ⟨Q⟩ := p3B
      have cover' (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ F.cut := by have h := cover v; tauto
      exact traceable_of_three_vertex_path_and_clique_shores conn F.size offB offA boundB boundA
        A3 apart.symm cover' clA Q.shape Q.lm Q.mr Q.lr Q.noLR
  · obtain ⟨P⟩ := p3A
    rcases clique_or_path_of_three (componentShore_connected F.cut F.second) sizeB with clB|p3B
    · exact traceable_of_three_vertex_path_and_clique_shores conn F.size offA offB boundA boundB
        B3 apart cover clB P.shape P.lm P.mr P.lr P.noLR
    · obtain ⟨Q⟩ := p3B
      exact traceable_of_two_three_vertex_path_shores conn budget F.size offA offB boundA boundB apart cover P Q

/-- The remaining all-high crossing failure requires at least ten vertices
in the independent-cubic minimum-order branch. -/
theorem order_ge_ten_of_crossing_failure
    [DecidableEq V] (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    (fail : ¬ CrossingBetweenSurvivingEdges G) : 10 ≤ Fintype.card V := by
  obtain ⟨F,_⟩ := high_cut_of_crossing_failure_of_independent_cubics
    smaller conn budget order no ind fail
  by_contra! small
  exact no (F.traceable_of_order_le_nine conn budget (by omega))

#print axioms LargeCrossingFailure.traceable_of_order_le_nine
#print axioms order_ge_ten_of_crossing_failure

end Graffiti199Depleted.Catalogue
