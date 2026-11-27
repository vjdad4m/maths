import AdjacentCut189
import NearForeignSaturation189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
open private mem_positive positive_card from AdjacentCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Any walk from one side to the opposite side has to pass through the
two cut vertices, so its length is at least the better of the two metric
detours through them. -/
theorem cross_metric {a b x y : V} (L : Finset V)
    (hc : G.Connected) (xl : x∈L) (yo : y∉L)
    (boundary : ∀ u∈L, ∀ v, G.Adj u v → v=a ∨ v=b ∨ v∈L) :
    G.dist x y = min (G.dist x a+G.dist a y) (G.dist x b+G.dist b y) := by
  have lower' {u w : V} (p : G.Walk u w) (ul : u∈L) (wo : w∉L) :
      min (G.dist x a+G.dist a w) (G.dist x b+G.dist b w) ≤
        G.dist x u + p.length := by
    induction p with
    | nil => exact (wo ul).elim
    | @cons u v w uv q ih =>
        have tri := hc.dist_triangle (u:=x) (v:=u) (w:=v)
        rw [dist_eq_one_iff_adj.mpr uv] at tri
        simp only [Walk.length_cons]
        rcases boundary u ul v uv with va|vb|vl
        · subst v
          have n := Nat.min_le_left (G.dist x a+G.dist a w) (G.dist x b+G.dist b w)
          have ql := G.dist_le q
          omega
        · subst v
          have n := Nat.min_le_right (G.dist x a+G.dist a w) (G.dist x b+G.dist b w)
          have ql := G.dist_le q
          omega
        · have h := ih vl wo
          omega
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist x y
  have lo := lower' p xl yo
  rw [SimpleGraph.dist_self,zero_add,pl] at lo
  exact Nat.le_antisymm (le_min (hc.dist_triangle (u:=x) (v:=a) (w:=y))
    (hc.dist_triangle (u:=x) (v:=b) (w:=y))) lo

namespace Split
open private left_boundary right_boundary from AdjacentCut189
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)

private lemma odd_odd_sum_even {k l : ℕ} (hk : ¬Even k) (hl : ¬Even l) : Even (k+l) := by
  simp only [Nat.even_iff] at *
  omega

private theorem covered_from_odd_ports (hc : G.Connected)
    {x y : V} (xl : x∈S.L) (yr : y∈S.R)
    (xa : ¬Even (G.dist x a)) (xb : ¬Even (G.dist x b))
    (ya : ¬Even (G.dist y a)) (yb : ¬Even (G.dist y b))
    {z : V} (za : z≠a) (zb : z≠b) :
    z∈PositiveEven G a ∨ z∈PositiveEven G b ∨
      z∈PositiveEven G x ∨ z∈PositiveEven G y := by
  by_cases za' : Even (G.dist a z)
  · exact Or.inl (mem_positive.mpr ⟨za,za'⟩)
  by_cases zb' : Even (G.dist b z)
  · exact Or.inr (Or.inl (mem_positive.mpr ⟨zb,zb'⟩))
  rcases S.cover z with h|h|zl|zr
  · exact (za h).elim
  · exact (zb h).elim
  · have zo : z∉S.R := fun e=>disjoint_left.mp S.dis zl e
    have d := cross_metric S.R hc yr zo (right_boundary S)
    have h : Even (G.dist y z) := by
      rw [d,min_def]
      split
      · exact odd_odd_sum_even ya za'
      · exact odd_odd_sum_even yb zb'
    exact Or.inr (Or.inr (Or.inr (mem_positive.mpr ⟨fun e=>zo (e.symm ▸ yr),h⟩)))
  · have zo : z∉S.L := fun e=>disjoint_left.mp S.dis e zr
    have d := cross_metric S.L hc xl zo (left_boundary S)
    have h : Even (G.dist x z) := by
      rw [d,min_def]
      split
      · exact odd_odd_sum_even xa za'
      · exact odd_odd_sum_even xb zb'
    exact Or.inr (Or.inr (Or.inl (mem_positive.mpr ⟨fun e=>zo (e.symm ▸ xl),h⟩)))

/-- Four parity balls cover the graph across a distance-two cut if each
side supplies a vertex odd-distance from both cut vertices. -/
theorem order_le_sixteen_of_odd_ports (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 5) (ab : G.dist a b=2)
    {x y : V} (xl : x∈S.L) (yr : y∈S.R)
    (xa : ¬Even (G.dist x a)) (xb : ¬Even (G.dist x b))
    (ya : ¬Even (G.dist y a)) (yb : ¬Even (G.dist y b)) :
    Fintype.card V≤16 := by
  classical
  have ne : a≠b := by
    intro e
    rw [← e,SimpleGraph.dist_self] at ab
    omega
  have aB : a∈PositiveEven G b := mem_positive.mpr ⟨ne,
    (by rw [SimpleGraph.dist_comm,ab]; decide)⟩
  have bA : b∈PositiveEven G a := mem_positive.mpr ⟨Ne.symm ne,
    (by rw [ab]; decide)⟩
  let A := PositiveEven G a ∪ PositiveEven G b
  let B := PositiveEven G x ∪ PositiveEven G y
  have cov : (univ : Finset V) ⊆ A∪B := by
    intro z _
    by_cases za : z=a
    · simp [A,za,aB]
    by_cases zb : z=b
    · simp [A,zb,bA]
    rcases covered_from_odd_ports S hc xl yr xa xb ya yb za zb with k|k|k|k <;>
      simp [A,B,k]
  have ha := positive_card (even a)
  have hb := positive_card (even b)
  have hx := positive_card (even x)
  have hy := positive_card (even y)
  have cA := card_union_le (PositiveEven G a) (PositiveEven G b)
  have cB := card_union_le (PositiveEven G x) (PositiveEven G y)
  have cc := card_union_le A B
  have c := card_le_card cov
  rw [card_univ] at c
  dsimp only [A,B] at cc c
  omega

#print axioms cross_metric
#print axioms order_le_sixteen_of_odd_ports
end Split
end Graffiti189LongestPath.CrossSaturation
