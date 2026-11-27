import TwoSingletons
import ClawSingleton

open private large_component_of_edge from CrossingCutReduction

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- At order eleven, every vertex beyond the two large distinguished
components is a singleton, by the minimum-order cubic-shore exclusion.
Both nonempty singleton patterns then have spanning paths. -/
theorem LargeCrossingFailure.cover_of_minimum_at_order_eleven
    (F : LargeCrossingFailure G) (order : Fintype.card V = 11)
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b) :
    ∀ v, v ∈ componentShore F.cut F.first ∨
      v ∈ componentShore F.cut F.second ∨ v ∈ F.cut := by
  classical
  let A := componentShore F.cut F.first
  let B := componentShore F.cut F.second
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  let U := (F.cut ∪ A.toFinset) ∪ B.toFinset
  let R := Finset.univ \ U
  have offA := componentShore_off_cut F.cut F.first
  have offB := componentShore_off_cut F.cut F.second
  have boundA := componentShore_boundary F.cut F.first
  have boundB := componentShore_boundary F.cut F.second
  have connA := componentShore_connected F.cut F.first
  have connB := componentShore_connected F.cut F.second
  have apart := componentShore_disjoint F.different
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
  have memU (v : V) : v ∈ U ↔ v ∈ A ∨ v ∈ B ∨ v ∈ F.cut := by
    change v ∈ (F.cut ∪ A.toFinset) ∪ B.toFinset ↔ _
    simp only [Finset.mem_union,Set.mem_toFinset]
    tauto
  have memR (v : V) : v ∈ R ↔ v ∉ U := by simp [R]
  have dim : R.card + U.card = 11 := by
    change (Finset.univ \ U).card + U.card = _
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),Finset.card_univ,order]
  have ca : 3 ≤ Nat.card A := F.first_large
  have cb : 3 ≤ Nat.card B := F.second_large
  have smallR : R.card ≤ 2 := by omega
  have cover (v : V) : v ∈ A ∨ v ∈ B ∨ v ∈ F.cut ∨ v ∈ R := by
    by_cases hv : v ∈ U
    · rcases (memU v).mp hv with ha|hb|hd
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (Or.inl hd))
    · exact Or.inr (Or.inr (Or.inr ((memR v).mpr hv)))
  have extra (v : V) (vR : v ∈ R) : CutSingleton G F.cut v ∧ v ∉ A ∧ v ∉ B := by
    have vU : v ∉ U := (memR v).mp vR
    have vA : v ∉ A := fun h => vU ((memU _).mpr (Or.inl h))
    have vB : v ∉ B := fun h => vU ((memU _).mpr (Or.inr (Or.inl h)))
    have vD : v ∉ F.cut := fun h => vU ((memU _).mpr (Or.inr (Or.inr h)))
    have sub : G.neighborFinset v ⊆ F.cut := by
      intro y hy
      by_contra yD
      let a : Survives F.cut := ⟨v,vD⟩
      let b : Survives F.cut := ⟨y,yD⟩
      let C := (DeletionGraph G F.cut).connectedComponentMk a
      let E := componentShore F.cut C
      have vE : v ∈ E := ⟨a,rfl,rfl⟩
      have cA : C ≠ F.first := by
        intro eq
        apply vA
        change v ∈ componentShore F.cut F.first
        rwa [← eq]
      have cB : C ≠ F.second := by
        intro eq
        apply vB
        change v ∈ componentShore F.cut F.second
        rwa [← eq]
      have awayA := Set.disjoint_left.mp (componentShore_disjoint cA)
      have awayB := Set.disjoint_left.mp (componentShore_disjoint cB)
      letI : Fintype E := Fintype.ofFinite E
      have eSub : E.toFinset ⊆ R := by
        intro z hz
        have zE : z ∈ E := Set.mem_toFinset.mp hz
        apply (memR z).mpr
        intro zU
        rcases (memU z).mp zU with za|zb|zd
        · exact awayA zE za
        · exact awayB zE zb
        · exact componentShore_off_cut F.cut C z zd zE
      have big : 3 ≤ Nat.card E := large_component_of_edge smaller conn budget
        (by omega) F.size no ind (a := a) (b := b) ((G.mem_neighborFinset _ _).mp hy)
      have bound := Finset.card_le_card eSub
      rw [Set.toFinset_card,← Nat.card_eq_fintype_card] at bound
      omega
    have low := degree_of_small_deletion_preconnected (G := G)
      (by omega : 4 ≤ Fintype.card V) (fun E hE => (conn.2 E hE).preconnected) v
    have eq := Finset.eq_of_subset_of_card_le sub
      (by rw [F.size,G.card_neighborFinset_eq_degree]; exact low)
    refine ⟨⟨vD,?_⟩,vA,vB⟩
    intro w
    rw [← G.mem_neighborFinset,eq]
  have shapes : R.card = 0 ∨ R.card = 1 ∨ R.card = 2 := by omega
  rcases shapes with none|one|two
  · intro v
    rcases cover v with va|vb|vd|vr
    · exact Or.inl va
    · exact Or.inr (Or.inl vb)
    · exact Or.inr (Or.inr vd)
    · exact (Finset.not_mem_empty v ((Finset.card_eq_zero.mp none) ▸ vr)).elim
  · obtain ⟨r,frame⟩ := Finset.card_eq_one.mp one
    have rR : r ∈ R := frame.symm ▸ (by simp : r ∈ ({r} : Finset V))
    obtain ⟨hr,rA,rB⟩ := extra r rR
    have newCover (v : V) : v ∈ A ∨ v ∈ B ∨ v ∈ F.cut ∨ v = r := by
      simpa only [frame,Finset.mem_singleton] using cover v
    exfalso
    by_cases nA : Nat.card A = 3
    · exact no (traceable_of_three_and_four_with_singleton conn budget F.size offA offB
        boundA boundB apart hr rA rB newCover connA connB nA (show Nat.card B = 4 by omega))
    · have swap (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ F.cut ∨ v = r := by
        have h := newCover v
        tauto
      exact no (traceable_of_three_and_four_with_singleton conn budget F.size offB offA
        boundB boundA apart.symm hr rB rA swap connB connA (show Nat.card B = 3 by omega)
        (show Nat.card A = 4 by omega))
  · obtain ⟨r,s,rs,frame⟩ := Finset.card_eq_two.mp two
    have rR : r ∈ R := frame.symm ▸ (by simp : r ∈ ({r,s} : Finset V))
    have sR : s ∈ R := frame.symm ▸ (by simp : s ∈ ({r,s} : Finset V))
    obtain ⟨hr,rA,rB⟩ := extra r rR
    obtain ⟨hs,sA,sB⟩ := extra s sR
    have newCover (v : V) : v ∈ A ∨ v ∈ B ∨ v ∈ F.cut ∨ v = r ∨ v = s := by
      simpa only [frame,Finset.mem_insert,Finset.mem_singleton] using cover v
    exact (no (traceable_of_two_three_shores_and_two_singletons conn budget F.size offA offB
      boundA boundB apart rs hr hs rA rB sA sB newCover connA connB
      (show Nat.card A = 3 by omega) (show Nat.card B = 3 by omega))).elim

/-- The exact remaining order-eleven crossing failures have just two
surviving components, with orders three and five or both four. -/
theorem order_eleven_crossing_failure_two_shapes
    (order : Fintype.card V = 11)
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    (fail : ¬ CrossingBetweenSurvivingEdges G) :
    ∃ F : LargeCrossingFailure G, (∀ v ∈ F.cut, 4 ≤ G.degree v) ∧
      (∀ v, v ∈ componentShore F.cut F.first ∨
        v ∈ componentShore F.cut F.second ∨ v ∈ F.cut) ∧
      ((Nat.card (componentShore F.cut F.first) = 3 ∧ Nat.card (componentShore F.cut F.second) = 5) ∨
       (Nat.card (componentShore F.cut F.first) = 4 ∧ Nat.card (componentShore F.cut F.second) = 4) ∨
       (Nat.card (componentShore F.cut F.first) = 5 ∧ Nat.card (componentShore F.cut F.second) = 3)) := by
  classical
  obtain ⟨F,deg⟩ := high_cut_of_crossing_failure_of_independent_cubics
    smaller conn budget (by omega) no ind fail
  have cover := F.cover_of_minimum_at_order_eleven order smaller conn budget no ind
  refine ⟨F,deg,cover,?_⟩
  let A := componentShore F.cut F.first
  let B := componentShore F.cut F.second
  change (Nat.card A = 3 ∧ Nat.card B = 5) ∨ (Nat.card A = 4 ∧ Nat.card B = 4) ∨
    (Nat.card A = 5 ∧ Nat.card B = 3)
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  have offA := componentShore_off_cut F.cut F.first
  have offB := componentShore_off_cut F.cut F.second
  have apart := componentShore_disjoint F.different
  have dA : Disjoint F.cut A.toFinset :=
    Finset.disjoint_left.mpr (fun x hx hA => offA x hx (Set.mem_toFinset.mp hA))
  have dB : Disjoint (F.cut ∪ A.toFinset) B.toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hx hB
    rcases Finset.mem_union.mp hx with cut|lhs
    · exact offB x cut (Set.mem_toFinset.mp hB)
    · exact Set.disjoint_left.mp apart (Set.mem_toFinset.mp lhs) (Set.mem_toFinset.mp hB)
  have full : (F.cut ∪ A.toFinset) ∪ B.toFinset = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    simp only [Finset.mem_union,Set.mem_toFinset]
    have h : v ∈ A ∨ v ∈ B ∨ v ∈ F.cut := cover v
    tauto
  have count := congrArg Finset.card full
  rw [Finset.card_union_of_disjoint dB,Finset.card_union_of_disjoint dA,F.size,
    Set.toFinset_card,Set.toFinset_card,← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,
    Finset.card_univ,order] at count
  have ca : 3 ≤ Nat.card A := F.first_large
  have cb : 3 ≤ Nat.card B := F.second_large
  omega

#print axioms LargeCrossingFailure.cover_of_minimum_at_order_eleven
#print axioms order_eleven_crossing_failure_two_shapes

end Graffiti199Depleted.Catalogue
