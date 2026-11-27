import Theta
import Mathlib.Topology.Path
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Theta659
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

private theorem segment_injective {a b : Plane} (ne : a ≠ b) :
    Function.Injective (segmentPath a b) := by
  intro s t h
  by_contra distinct
  have st : (s : ℝ) - t ≠ 0 := sub_ne_zero.mpr (fun e => distinct (Subtype.ext e))
  apply ne
  have cancel (x y : ℝ) (h : (1-(s:ℝ))*x+s*y = (1-(t:ℝ))*x+t*y) : x=y := by
    have zero : ((s:ℝ)-t)*(y-x) = 0 := by linarith only [h]
    exact (sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left st)).symm
  exact Prod.ext (cancel _ _ (congrArg Prod.fst h)) (cancel _ _ (congrArg Prod.snd h))


variable {k : ℕ}

noncomputable def point : V k → Plane
  | (false,none) => (0,0)
  | (true,none) => (3,0)
  | (false,some i) => (1,i.val)
  | (true,some i) => (2,i.val)

private theorem point_injective : Function.Injective (@point k) := by
  rintro ⟨a,_|i⟩ ⟨b,_|j⟩ eq <;> cases a <;> cases b
  all_goals first | (have h := congrArg Prod.fst eq; norm_num [point] at h; done) | simp [point] at eq ⊢
  all_goals apply Fin.ext; exact_mod_cast eq

private inductive Segment (k : ℕ) where
  | left (i : Fin k)
  | middle (i : Fin k)
  | right (i : Fin k)

private def tail : Segment k → V k
  | .left _ => hub false
  | .middle i => inner i false
  | .right _ => hub true
private def tip : Segment k → V k
  | .left i => inner i false
  | .middle i | .right i => inner i true

private def Ends (e : Segment k) (a b : V k) :=
  (a=tail e ∧ b=tip e) ∨ (a=tip e ∧ b=tail e)

private theorem orient {a b : V k} (h : (graph k).Adj a b) : ∃ e, Ends e a b := by
  rcases a with ⟨a,_|i⟩ <;> rcases b with ⟨b,_|j⟩
  · exact h.elim
  · change a=b at h
    subst b
    cases a
    · exact ⟨.left j,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨.right j,Or.inl ⟨rfl,rfl⟩⟩
  · change a=b at h
    subst b
    cases a
    · exact ⟨.left i,Or.inr ⟨rfl,rfl⟩⟩
    · exact ⟨.right i,Or.inr ⟨rfl,rfl⟩⟩
  · change i=j ∧ a≠b at h
    obtain ⟨rfl,ne⟩ := h
    cases a <;> cases b
    · exact (ne rfl).elim
    · exact ⟨.middle i,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨.middle i,Or.inr ⟨rfl,rfl⟩⟩
    · exact (ne rfl).elim

private noncomputable def atTime : Segment k → ℝ → Plane
  | .left i,t => (t,t*i.val)
  | .middle i,t => (1+t,i.val)
  | .right i,t => (3-t,t*i.val)

private theorem atTime_eq (e : Segment k) (t : ℝ) :
    mix (point (tail e)) (point (tip e)) t = atTime e t := by
  cases e <;> ext <;> simp [tail,tip,point,mix,atTime] <;> ring
private theorem normalize {k : ℕ} {a b : V k} (h : (graph k).Adj a b)
    {t : ℝ} (ht : 0<t) (ht' : t<1) :
    ∃ (e : Segment k) (r : ℝ), Ends e a b ∧ 0<r ∧ r<1 ∧
      mix (point a) (point b) t = atTime e r := by
  obtain ⟨e,ends⟩ := orient h
  rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨e,t,Or.inl ⟨rfl,rfl⟩,ht,ht',atTime_eq e t⟩
  · refine ⟨e,1-t,Or.inr ⟨rfl,rfl⟩,by linarith,by linarith,?_⟩
    rw [← atTime_eq]
    ext <;> simp [mix] <;> ring


/-- Every open edge lies strictly in one of three unit-width strips. -/
private theorem avoid (e : Segment k) (v : V k) {s : ℝ} (hs : 0<s) (hs' : s<1) :
    atTime e s ≠ point v := by
  intro eq
  have x := congrArg Prod.fst eq
  rcases v with ⟨b,_|j⟩ <;> cases b <;> cases e <;> simp [point,atTime] at x <;> linarith

private theorem unique_segment (e f : Segment k) {s t : ℝ}
    (hs : 0<s) (hs' : s<1) (ht : 0<t) (ht' : t<1) (h : atTime e s = atTime f t) : e=f := by
  have x := congrArg Prod.fst h
  have y := congrArg Prod.snd h
  have spoke {i j : Fin k} (same : s=t) (equal : s*i.val=t*j.val) : i=j := by
    rw [← same] at equal
    apply Fin.ext
    exact_mod_cast (mul_left_cancel₀ hs.ne' equal)
  cases e <;> cases f <;> simp only [atTime] at x y
  all_goals first
    | exact congrArg Segment.left (spoke (by linarith) y)
    | exact congrArg Segment.right (spoke (by linarith) y)
    | exact congrArg Segment.middle (Fin.ext (by exact_mod_cast y))
    | linarith

noncomputable def drawing (m : ℕ) : PlaneDrawing (graph m) where
  pos := point
  pos_injective := point_injective
  arc a b _ := segmentPath (point a) (point b)
  embedded _ _ e := ((segmentPath _ _).continuous.isClosedEmbedding
    (segment_injective (fun h => e.ne (point_injective h)))).isEmbedding
  reverse_arc := by
    intro a b _
    apply Path.ext
    funext t
    change mix (point b) (point a) t = mix (point a) (point b) (1-(t:ℝ))
    ext <;> simp [mix] <;> ring
  avoids_vertex := by
    intro a b e v s hs hs' meet
    obtain ⟨q,r,_,hr,hr',shape⟩ := normalize e hs hs'
    exact avoid q v hr hr' (shape.symm.trans meet)
  interiors := by
    intro a b c d e f s t hs hs' ht ht' meet
    obtain ⟨q,r,ends,hr,hr',shape⟩ := normalize e hs hs'
    obtain ⟨q',r',ends',hr2,hr2',shape'⟩ := normalize f ht ht'
    have same := unique_segment q q' hr hr' hr2 hr2' (shape.symm.trans (meet.trans shape'))
    subst q'
    rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases ends' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp

theorem planar (m : ℕ) : Planar (graph m) := ⟨drawing m⟩
end Theta659
