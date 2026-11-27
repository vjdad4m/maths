import FiniteShoreCount
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] {D : Finset V}

theorem four_component_route (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (size : D.card = 3) (e : Fin 4 ≃ (DeletionGraph G D).ConnectedComponent) : Traceable G := by
  classical
  let U (i : Fin 4) := componentShore D (e i)
  have full (i : Fin 4) (p : V) (hp : p ∈ D) : GoodAt G (U i) p := by
    by_contra bad
    let f := (Equiv.swap 0 i).trans e
    have bad' : ¬ GoodAt G (componentShore D (f 0)) p := by simpa [f,U] using bad
    exact no_fourth_component conn size budget (f.injective.ne (by decide : (0 : Fin 4) ≠ 1))
      (f.injective.ne (by decide : (0 : Fin 4) ≠ 2)) (f.injective.ne (by decide : (0 : Fin 4) ≠ 3))
      (f.injective.ne (by decide : (1 : Fin 4) ≠ 2)) (f.injective.ne (by decide : (1 : Fin 4) ≠ 3))
      (f.injective.ne (by decide : (2 : Fin 4) ≠ 3)) hp bad'
  obtain ⟨r,a,b,ra,rb,ab,ed⟩ := Finset.card_eq_three.mp size
  have hr : r ∈ D := by simp [ed]
  have ha : a ∈ D := by simp [ed]
  have hb : b ∈ D := by simp [ed]
  have route (i : Fin 4) : ∃ x ∈ U i, ∃ y ∈ U i, Traverses G (U i) x y := by
    obtain ⟨x⟩ := (componentShore_connected D (e i)).nonempty
    exact ⟨x.val,x.property,Traverses.start_clique (full i r hr).1 x.property⟩
  obtain ⟨_,_,_,m₀,P₀⟩ := route 0
  obtain ⟨_,x₁,_,y₁,P₁⟩ := route 1
  obtain ⟨_,x₂,_,y₂,P₂⟩ := route 2
  obtain ⟨_,x₃,_,_,P₃⟩ := route 3
  have ds {i j : Fin 4} (ne : i ≠ j) : Disjoint (U i) (U j) := componentShore_disjoint (e.injective.ne ne)
  have off (i : Fin 4) {s : V} (h : s ∈ D) : s ∉ U i := componentShore_off_cut D (e i) s h
  have d₁ : Disjoint (U 0) ({r} : Set V) := by simpa using off 0 hr
  have d₂ : Disjoint (U 0 ∪ {r}) (U 1) := by simp [Set.disjoint_union_left,ds (by decide : (0 : Fin 4) ≠ 1),off 1 hr]
  have d₃ : Disjoint ((U 0 ∪ {r}) ∪ U 1) ({a} : Set V) := by simp [Set.disjoint_union_left,off 0 ha,off 1 ha,ra.symm]
  have d₄ : Disjoint (((U 0 ∪ {r}) ∪ U 1) ∪ {a}) (U 2) := by
    simp [Set.disjoint_union_left,ds (by decide : (0 : Fin 4) ≠ 2),ds (by decide : (1 : Fin 4) ≠ 2),off 2 hr,off 2 ha]
  have d₅ : Disjoint ((((U 0 ∪ {r}) ∪ U 1) ∪ {a}) ∪ U 2) ({b} : Set V) := by
    simp [Set.disjoint_union_left,off 0 hb,off 1 hb,off 2 hb,rb.symm,ab.symm]
  have d₆ : Disjoint (((((U 0 ∪ {r}) ∪ U 1) ∪ {a}) ∪ U 2) ∪ {b}) (U 3) := by
    simp [Set.disjoint_union_left,ds (by decide : (0 : Fin 4) ≠ 3),ds (by decide : (1 : Fin 4) ≠ 3),
      ds (by decide : (2 : Fin 4) ≠ 3),off 3 hr,off 3 ha,off 3 hb]
  obtain ⟨P,_,_⟩ := (((((P₀.join (Traverses.single r) d₁ ((full 0 r hr).2 _ m₀).symm).join
    P₁ d₂ ((full 1 r hr).2 _ x₁)).join (Traverses.single a) d₃ ((full 1 a ha).2 _ y₁).symm).join
    P₂ d₄ ((full 2 a ha).2 _ x₂)).join (Traverses.single b) d₅ ((full 2 b hb).2 _ y₂).symm).join
    P₃ d₆ ((full 3 b hb).2 _ x₃)
  have all : ((((((U 0 ∪ {r}) ∪ U 1) ∪ {a}) ∪ U 2) ∪ {b}) ∪ U 3) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    simp only [Set.mem_union,Set.mem_singleton_iff]
    by_cases hd : x ∈ D
    · have : x = r ∨ x = a ∨ x = b := by simpa [ed] using hd
      tauto
    let t : Survives D := ⟨x,hd⟩
    obtain ⟨i,eq⟩ := e.surjective ((DeletionGraph G D).connectedComponentMk t)
    have mem : x ∈ U i := ⟨t,eq.symm,rfl⟩
    fin_cases i <;> tauto
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨all ▸ P⟩)

/-- Finite connected graphs with connectivity at least three and induced tree
number at most five are traceable if a three-cut leaves at least three
components, including singleton components. -/
theorem traceable_of_three_or_more_components (conn : ConnectivityAtLeast G 3)
    (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (many : 3 ≤ Nat.card (DeletionGraph G D).ConnectedComponent) : Traceable G := by
  classical
  let K := (DeletionGraph G D).ConnectedComponent
  letI : Fintype K := Fintype.ofFinite K
  have cap := component_count_le_four conn budget size
  change 3 ≤ Nat.card K at many
  change Nat.card K ≤ 4 at cap
  rw [Nat.card_eq_fintype_card] at many cap
  by_cases three : Fintype.card K = 3
  · let e : Fin 3 ≃ K := (Fintype.equivFinOfCardEq three).symm
    apply traceable_of_exactly_three_components conn budget size
      (e.injective.ne (by decide : (0 : Fin 3) ≠ 1)) (e.injective.ne (by decide : (0 : Fin 3) ≠ 2))
      (e.injective.ne (by decide : (1 : Fin 3) ≠ 2))
    intro k
    obtain ⟨i,rfl⟩ := e.surjective k
    fin_cases i <;> simp
  · exact four_component_route conn budget size (Fintype.equivFinOfCardEq (by omega : Fintype.card K = 4)).symm

#print axioms traceable_of_three_or_more_components
end Graffiti199Depleted.Catalogue.Incomplete


