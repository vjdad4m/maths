import OddPortsCut189
namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
open private mem_positive from AdjacentCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- A separating cut vertex allows three parity balls to cover every
other vertex. This bound needs no lower-degree assumption. -/
theorem order_le_three_times_budget_plus_one_at_articulation {c : V}
    (hc : G.Connected) (d : ℕ) (even : ∀ x, (EvenFrom G x).card≤d+1)
    (L R : Finset V) (dis : Disjoint L R)
    (cross : ∀ l∈L,∀ r∈R, ¬G.Adj l r)
    (cover : ∀ z,z=c ∨ z∈L ∨ z∈R)
    {x y : V} (xl : x∈L) (yr : y∈R) (cx : G.Adj c x) (cy : G.Adj c y) :
    Fintype.card V ≤ 3*d+1 := by
  classical
  have cap (z : V) : (PositiveEven G z).card≤d := by
    have h : z∈EvenFrom G z := by simp [EvenFrom,SimpleGraph.dist_self]
    have n := card_erase_of_mem h
    have m := even z
    change ((EvenFrom G z).erase z).card≤d
    omega
  have lbd (u : V) (ul : u∈L) (v : V) (uv : G.Adj u v) : v=c ∨ v=c ∨ v∈L := by
    rcases cover v with h|h|h
    · exact .inl h
    · exact .inr (.inr h)
    · exact (cross _ ul _ h uv).elim
  have rbd (u : V) (ur : u∈R) (v : V) (uv : G.Adj u v) : v=c ∨ v=c ∨ v∈R := by
    rcases cover v with h|h|h
    · exact .inl h
    · exact (cross _ h _ ur uv.symm).elim
    · exact .inr (.inr h)
  have p (z : V) (zc : z≠c) :
      z∈PositiveEven G c ∨ z∈PositiveEven G x ∨ z∈PositiveEven G y := by
    by_cases ez : Even (G.dist c z)
    · exact .inl (mem_positive.mpr ⟨zc,ez⟩)
    rcases cover z with h|zl|zr
    · exact (zc h).elim
    · have e := cross_metric (a:=c) (b:=c) R hc yr (fun h=>disjoint_left.mp dis zl h) rbd
      have dy := dist_eq_one_iff_adj.mpr cy.symm
      rw [min_self,dy] at e
      have q : Even (G.dist y z) := by
        rw [e]
        simp only [Nat.even_iff] at ez ⊢
        omega
      exact .inr (.inr (mem_positive.mpr ⟨fun h=>disjoint_left.mp dis zl (h.symm ▸ yr),q⟩))
    have e := cross_metric (a:=c) (b:=c) L hc xl (fun h=>disjoint_left.mp dis h zr) lbd
    have dx := dist_eq_one_iff_adj.mpr cx.symm
    rw [min_self,dx] at e
    have q : Even (G.dist x z) := by
      rw [e]
      simp only [Nat.even_iff] at ez ⊢
      omega
    exact .inr (.inl (mem_positive.mpr ⟨fun h=>disjoint_left.mp dis (h.symm ▸ xl) zr,q⟩))
  let U := PositiveEven G c ∪ (PositiveEven G x ∪ PositiveEven G y)
  have sub : (univ : Finset V) ⊆ insert c U := by
    intro z _
    by_cases zc : z=c
    · simp [zc]
    · exact mem_insert_of_mem (by simpa only [U,mem_union] using p z zc)
  have s := card_le_card sub
  rw [card_univ] at s
  have c₁ := card_insert_le c U
  have c₂ := card_union_le (PositiveEven G c) (PositiveEven G x ∪ PositiveEven G y)
  have c₃ := card_union_le (PositiveEven G x) (PositiveEven G y)
  have cc := cap c
  have cx' := cap x
  have cy' := cap y
  dsimp only [U] at s c₁
  omega


/-- A single opposite-side porter covers the odd-distance vertices on the
other side, while the root covers the even-distance vertices on both. -/
theorem side_and_opposite_even_le_twice_budget {c : V}
    (hc : G.Connected) (d : ℕ) (even : ∀ x, (EvenFrom G x).card≤d+1)
    (L R : Finset V) (dis : Disjoint L R) (co : c∉L)
    (cross : ∀ l∈L,∀ r∈R, ¬G.Adj l r)
    (cover : ∀ z,z=c ∨ z∈L ∨ z∈R)
    {y : V} (yr : y∈R) (cy : G.Adj c y) :
    L.card + (R ∩ PositiveEven G c).card ≤ 2*d := by
  classical
  have cap (z : V) : (PositiveEven G z).card≤d := by
    have h : z∈EvenFrom G z := by simp [EvenFrom,SimpleGraph.dist_self]
    have n := card_erase_of_mem h
    have m := even z
    change ((EvenFrom G z).erase z).card≤d
    omega
  have rbd (u : V) (ur : u∈R) (v : V) (uv : G.Adj u v) : v=c ∨ v=c ∨ v∈R := by
    rcases cover v with h|h|h
    · exact .inl h
    · exact (cross _ h _ ur uv.symm).elim
    · exact .inr (.inr h)
  have incl : L ∪ (R ∩ PositiveEven G c) ⊆ PositiveEven G c ∪ PositiveEven G y := by
    intro z hz
    rcases mem_union.mp hz with zl|hr
    · by_cases ez : Even (G.dist c z)
      · exact mem_union_left _ (mem_positive.mpr ⟨fun h=>co (h ▸ zl),ez⟩)
      have e := cross_metric (a:=c) (b:=c) R hc yr (fun h=>disjoint_left.mp dis zl h) rbd
      have dy := dist_eq_one_iff_adj.mpr cy.symm
      rw [min_self,dy] at e
      have q : Even (G.dist y z) := by
        rw [e]
        simp only [Nat.even_iff] at ez ⊢
        omega
      exact mem_union_right _ (mem_positive.mpr ⟨fun h=>disjoint_left.mp dis zl (h.symm ▸ yr),q⟩)
    exact mem_union_left _ (mem_inter.mp hr).2
  have dis' : Disjoint L (R ∩ PositiveEven G c) := dis.mono_right inter_subset_left
  have h := card_le_card incl
  rw [card_union_of_disjoint dis'] at h
  have u := card_union_le (PositiveEven G c) (PositiveEven G y)
  have cc := cap c
  have cy' := cap y
  omega

#print axioms side_and_opposite_even_le_twice_budget
#print axioms order_le_three_times_budget_plus_one_at_articulation
end Graffiti189LongestPath.CrossSaturation
