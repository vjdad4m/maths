import ArticulationPair189
namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- If two sets partition the vertices and exactly one edge crosses their boundary,
the positive-even-distance budgets of its endpoints bound the total order. -/
theorem order_le_twice_budget_plus_two_of_single_bridge (hc : G.Connected) (d : ℕ)
    (even : ∀ x, (EvenFrom G x).card≤d+1) (L R : Finset V)
    (dis : Disjoint L R) (cover : ∀ z,z∈L ∨ z∈R) {a b : V}
    (al : a∈L) (br : b∈R) (ab : G.Adj a b)
    (single : ∀ x∈L, ∀ y∈R,G.Adj x y → x=a ∧ y=b) :
    Fintype.card V≤2*d+2 := by
  classical
  have left (x : V) (xl : x∈L) (y : V) (xy : G.Adj x y) : y=b ∨ y=b ∨ y∈L := by
    rcases cover y with yl|yr
    · exact Or.inr (Or.inr yl)
    · exact Or.inl (single x xl y yr xy).2
  have right (y : V) (yr : y∈R) (x : V) (yx : G.Adj y x) : x=a ∨ x=a ∨ x∈R := by
    rcases cover x with xl|xr
    · exact Or.inl (single x xl y yr yx.symm).1
    · exact Or.inr (Or.inr xr)
  have a1 := dist_eq_one_iff_adj.mpr ab
  have b1 := dist_eq_one_iff_adj.mpr ab.symm
  have sub : (univ : Finset V) ⊆ EvenFrom G a ∪ EvenFrom G b := by
    intro z _
    rcases cover z with zl|zr
    · have zo : z∉R := fun e=>disjoint_left.mp dis zl e
      have e := cross_metric (a:=a) (b:=a) R hc br zo right
      rw [min_self,b1] at e
      by_cases ha : Even (G.dist a z)
      · exact mem_union_left _ (by simp [EvenFrom,ha])
      have hb : Even (G.dist b z) := by
        rw [e]
        simp only [Nat.even_iff] at ha ⊢
        omega
      exact mem_union_right _ (by simp [EvenFrom,hb])
    have zo : z∉L := fun e=>disjoint_left.mp dis e zr
    have e := cross_metric (a:=b) (b:=b) L hc al zo left
    rw [min_self,a1] at e
    by_cases hb : Even (G.dist b z)
    · exact mem_union_right _ (by simp [EvenFrom,hb])
    have ha : Even (G.dist a z) := by
      rw [e]
      simp only [Nat.even_iff] at hb ⊢
      omega
    exact mem_union_left _ (by simp [EvenFrom,ha])
  have h := (card_le_card sub).trans (card_union_le _ _)
  rw [card_univ] at h
  have ha := even a
  have hb := even b
  omega

namespace ArticulationPair
variable {c : V} (S : ArticulationPair G c)
theorem order_le_ten_of_unique_right_port (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5) {y : V} (yr : y∈S.R) (cy : G.Adj c y)
    (unique : ∀ z∈S.R,G.Adj c z → z=y) : Fintype.card V≤10 := by
  classical
  let A := insert c S.L
  have dis : Disjoint A S.R := by
    apply disjoint_left.mpr
    intro z za zr
    rcases mem_insert.mp za with rfl|zl
    · exact S.offR zr
    · exact disjoint_left.mp S.dis zl zr
  have cover (z : V) : z∈A ∨ z∈S.R := by
    rcases S.cover z with rfl|zl|zr
    · exact Or.inl (mem_insert_self _ _)
    · exact Or.inl (mem_insert_of_mem zl)
    · exact Or.inr zr
  have cross (u : V) (ua : u∈A) (v : V) (vr : v∈S.R) (uv : G.Adj u v) :
      u=c ∧ v=y := by
    rcases mem_insert.mp ua with rfl|ul
    · exact ⟨rfl,unique v vr uv⟩
    · exact (S.cross _ ul _ vr uv).elim
  exact order_le_twice_budget_plus_two_of_single_bridge hc 4 even A S.R dis cover
    (mem_insert_self _ _) yr cy cross

end ArticulationPair
#print axioms order_le_twice_budget_plus_two_of_single_bridge
#print axioms ArticulationPair.order_le_ten_of_unique_right_port
end Graffiti189LongestPath.CrossSaturation
