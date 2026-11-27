import Mathlib.Topology.Path
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Book567.Drawing
open SimpleGraph
open scoped unitInterval
abbrev Plane := ℝ × ℝ

/-- A topological drawing using distinct vertex points and embedded edge arcs.
Opposite orientations use the same arc in reverse. Each open edge misses every
vertex, and distinct undirected edges have disjoint open arcs. -/
structure PlaneDrawing {U : Type*} (G : SimpleGraph U) where
  pos : U → Plane
  pos_injective : Function.Injective pos
  arc : ∀ a b, G.Adj a b → Path (pos a) (pos b)
  embedded : ∀ a b (e : G.Adj a b), Topology.IsEmbedding (arc a b e)
  reverse_arc : ∀ a b (e : G.Adj a b), arc b a e.symm = (arc a b e).symm
  avoids_vertex : ∀ a b (e : G.Adj a b) (v : U) (s : I),
    0 < (s : ℝ) → (s : ℝ) < 1 → arc a b e s ≠ pos v
  interiors : ∀ a b c d (e : G.Adj a b) (f : G.Adj c d) (s t : I),
    0 < (s : ℝ) → (s : ℝ) < 1 → 0 < (t : ℝ) → (t : ℝ) < 1 →
    arc a b e s = arc c d f t → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

/-- Usual planar-graph predicate, allowing arbitrary embedded arcs. -/
def Planar {U : Type*} (G : SimpleGraph U) : Prop := Nonempty (PlaneDrawing G)

noncomputable def mix (a b : Plane) (s : ℝ) : Plane :=
  ((1-s)*a.1+s*b.1, (1-s)*a.2+s*b.2)

noncomputable def segmentPath (a b : Plane) : Path a b where
  toFun t := mix a b t
  continuous_toFun := by unfold mix; fun_prop
  source' := by simp [mix]
  target' := by simp [mix]

theorem segment_injective {a b : Plane} (ne : a ≠ b) :
    Function.Injective (segmentPath a b) := by
  intro s t h
  by_contra distinct
  have st : (s : ℝ) - t ≠ 0 := sub_ne_zero.mpr (fun e => distinct (Subtype.ext e))
  apply ne
  have cancel (x y : ℝ) (h : (1-(s:ℝ))*x+s*y = (1-(t:ℝ))*x+t*y) : x=y := by
    have zero : ((s:ℝ)-t)*(y-x) = 0 := by linarith only [h]
    exact (sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left st)).symm
  exact Prod.ext (cancel _ _ (congrArg Prod.fst h)) (cancel _ _ (congrArg Prod.snd h))

theorem between_levels (i j : ℕ) {s : ℝ} (hs : 0<s) (hs' : s<1) :
    (i : ℝ)+s ≠ j := by
  intro h
  by_cases hji : j ≤ i
  · have : (j : ℝ) ≤ i := by exact_mod_cast hji
    linarith
  · have : (i : ℝ)+1 ≤ j := by exact_mod_cast (show i+1 ≤ j by omega)
    linarith

theorem same_level (i j : ℕ) {s t : ℝ} (hs : 0<s) (hs' : s<1)
    (ht : 0<t) (ht' : t<1) (eq : (i : ℝ)+s=j+t) : i=j := by
  rcases lt_trichotomy i j with less|same|greater
  · have : (i : ℝ)+1 ≤ j := by exact_mod_cast (show i+1 ≤ j by omega)
    linarith
  · exact same
  · have : (j : ℝ)+1 ≤ i := by exact_mod_cast (show j+1 ≤ i by omega)
    linarith

end Book567.Drawing
