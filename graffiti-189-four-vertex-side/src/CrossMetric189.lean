import ActualTwoCut189
namespace Graffiti189LongestPath.TwoCut.CutPair
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
variable {a b : V} (S : CutPair G a b)

/-- Exact cross-component metric of a two-vertex cut. -/
theorem cross_distance_eq {i j : Bool} (ij : i≠j) {x y : V}
    (xi : x∈S.H i) (yj : y∈S.H j) :
    G.dist x y = min (G.dist x a + G.dist a y) (G.dist x b + G.dist b y) := by
  have dis := S.disjoint_sides ij
  have crossing {u v : V} (w : G.Walk u v) (ui : u∈S.H i) (vi : v∉S.H i) :
      a∈w.support ∨ b∈w.support := by
    induction w with
    | nil => exact (vi ui).elim
    | @cons u z v uz w ih =>
      rcases S.closed i u ui z uz with rfl|rfl|zi
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)
      · exact (ih zi vi).imp (fun h => by simp [h]) (fun h => by simp [h])
  apply Nat.le_antisymm
  · exact le_min (S.con.dist_triangle (v:=a)) (S.con.dist_triangle (v:=b))
  obtain ⟨w,wl⟩ := S.con.exists_walk_length_eq_dist x y
  rcases crossing w xi (fun yi => disjoint_left.mp dis yi yj) with ha|hb
  · obtain ⟨p,q,eq⟩ := mem_support_iff_exists_append.mp ha
    have hh : w.length=p.length+q.length := by rw [eq,length_append]
    exact (min_le_left _ _).trans (by have hp := G.dist_le p; have hq := G.dist_le q; omega)
  · obtain ⟨p,q,eq⟩ := mem_support_iff_exists_append.mp hb
    have hh : w.length=p.length+q.length := by rw [eq,length_append]
    exact (min_le_right _ _).trans (by have hp := G.dist_le p; have hq := G.dist_le q; omega)

#print axioms cross_distance_eq
end Graffiti189LongestPath.TwoCut.CutPair
