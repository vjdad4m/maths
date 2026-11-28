import CographJoin
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace CographTree
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def StarAt (c : V) := ∀ x y, G.Adj x y ↔ (x = c ∧ y ≠ c) ∨ (y = c ∧ x ≠ c)

omit [Fintype V] in
private theorem no_triangle (h : G.IsAcyclic) {a b c : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (ac : G.Adj a c) : False := by
  let p : G.Path a c := ⟨.cons ab (.cons bc .nil), by
    simp [Walk.isPath_def,ab.ne,bc.ne,ac.ne]⟩
  let q : G.Path a c := ⟨.cons ac .nil, by simp [Walk.isPath_def,ac.ne]⟩
  have e := congrArg (fun w : G.Path a c => w.val.length) (h.path_unique p q)
  simp [p,q] at e

omit [Fintype V] in
private theorem common_unique (h : G.IsAcyclic) {a b c d : V} (hac : a ≠ c)
    (ab : G.Adj a b) (bc : G.Adj b c) (ad : G.Adj a d) (dc : G.Adj d c) : b = d := by
  let p : G.Path a c := ⟨.cons ab (.cons bc .nil), by
    simp [Walk.isPath_def,ab.ne,bc.ne,hac]⟩
  let q : G.Path a c := ⟨.cons ad (.cons dc .nil), by
    simp [Walk.isPath_def,ad.ne,dc.ne,hac]⟩
  have e := congrArg (fun w : G.Path a c => w.val.getVert 1) (h.path_unique p q)
  simpa [p,q] using e

omit [Fintype V] in
private theorem star_of_join_singleton (h : G.IsAcyclic) (A : V → Prop) (c : V)
    (side : ∀ x, A x ↔ x = c) (cross : ∀ u v, A u → ¬ A v → G.Adj u v) :
    StarAt G c := by
  have spoke (v : V) (hv : v ≠ c) : G.Adj c v :=
    cross c v ((side c).mpr rfl) (fun av => hv ((side v).mp av))
  intro x y
  constructor
  · intro xy
    by_cases hx : x = c
    · exact Or.inl ⟨hx, hx ▸ xy.ne.symm⟩
    by_cases hy : y = c
    · exact Or.inr ⟨hy, hy ▸ xy.ne⟩
    exact False.elim (no_triangle G h (spoke x hx) xy (spoke y hy))
  · rintro (⟨rfl,hy⟩ | ⟨rfl,hx⟩)
    · exact spoke y hy
    · exact (spoke x hx).symm

/-- Every connected, nontrivial induced-P₄-free forest is a star, including K₂. -/
theorem star_of_tree_cograph [Nontrivial V] (h : G.IsTree) (hp : CographRadius.Cograph G) :
    ∃ c, StarAt G c := by
  classical
  let x : V := Classical.choice inferInstance
  obtain ⟨A,y,hx,hy,cross⟩ := CographRadius.join_at G h.isConnected hp x
  by_cases single : ∀ v, A v → v = x
  · exact ⟨x,star_of_join_singleton G h.IsAcyclic A x
      (fun v => ⟨single v,fun e => e.symm ▸ hx⟩) cross⟩
  push_neg at single
  obtain ⟨z,hz,hzx⟩ := single
  have right (v : V) (hv : ¬ A v) : v = y :=
    common_unique G h.IsAcyclic hzx (cross z v hz hv) (cross x v hx hv).symm
      (cross z y hz hy) (cross x y hx hy).symm
  refine ⟨y,star_of_join_singleton G h.IsAcyclic (fun v => ¬ A v) y ?_ ?_⟩
  · exact fun v => ⟨right v,fun e => e.symm ▸ hy⟩
  · intro u v hu hv
    exact (cross v u (not_not.mp hv) hu).symm

#print axioms star_of_tree_cograph
end CographTree
