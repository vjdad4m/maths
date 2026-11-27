import Family
import Mathlib.Topology.Path
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace PlanarRainbow464
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

/-- Three consecutive heights in each group: lower leaf, center, upper leaf. -/
private def leafY {m : ℕ} (p : Leaf m) : ℕ := 3*p.1.val + if p.2 then 2 else 0
private def lowerY {m : ℕ} (p : Leaf m) : ℕ := 3*p.1.val + if p.2 then 1 else 0

private theorem leafY_inj {m : ℕ} : Function.Injective (@leafY m) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ eq
  cases b <;> cases c <;> simp [leafY] at eq ⊢ <;> first | exact Fin.ext (by omega) | omega

private theorem lowerY_inj {m : ℕ} : Function.Injective (@lowerY m) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ eq
  cases b <;> cases c <;> simp [lowerY] at eq ⊢ <;> first | exact Fin.ext (by omega) | omega

noncomputable def point {m : ℕ} : V m → Plane
  | .inl (.inl false) => (-1,0)
  | .inl (.inl true) => (1,0)
  | .inl (.inr i) => (0, ((3*i.val+1 : ℕ) : ℝ))
  | .inr p => (0, (leafY p : ℝ))

private theorem point_injective {m : ℕ} : Function.Injective (@point m) := by
  rintro ((b|i)|p) ((c|j)|q) h
  · cases b <;> cases c <;> norm_num [point] at h ⊢
  · cases b <;> norm_num [point] at h
  · cases b <;> norm_num [point] at h
  · cases c <;> norm_num [point] at h
  · apply congrArg center
    apply Fin.ext
    have e : 3*i.val+1=3*j.val+1 := by exact Nat.cast_injective (R := ℝ) (congrArg Prod.snd h)
    omega
  · obtain ⟨j,b⟩ := q
    have e : 3*i.val+1=leafY (j,b) := by exact Nat.cast_injective (R := ℝ) (congrArg Prod.snd h)
    cases b <;> simp [leafY] at e <;> omega
  · cases c <;> norm_num [point] at h
  · obtain ⟨i,b⟩ := p
    have e : leafY (i,b)=3*j.val+1 := by exact Nat.cast_injective (R := ℝ) (congrArg Prod.snd h)
    cases b <;> simp [leafY] at e <;> omega
  · apply congrArg Sum.inr
    apply leafY_inj
    exact Nat.cast_injective (R := ℝ) (congrArg Prod.snd h)

private inductive Segment (m : ℕ) where
  | left (p : Leaf m)
  | right (p : Leaf m)
  | vertical (p : Leaf m)

private def tail {m : ℕ} : Segment m → V m
  | .left _ => hub false | .right _ => hub true
  | .vertical (i,false) => leaf i false | .vertical (i,true) => center i
private def tip {m : ℕ} : Segment m → V m
  | .left p | .right p => .inr p
  | .vertical (i,false) => center i | .vertical (i,true) => leaf i true

private def Ends {m : ℕ} (e : Segment m) (a b : V m) :=
  (a=tail e ∧ b=tip e) ∨ (a=tip e ∧ b=tail e)

private theorem orient {m : ℕ} {a b : V m} (h : (graph m).Adj a b) : ∃ e, Ends e a b := by
  have forward (c : Core m) (p : Leaf m) (inc : incident c p) : ∃ e, Ends e (.inl c) (.inr p) := by
    rcases c with (b|i)
    · cases b
      · exact ⟨.left p,Or.inl ⟨rfl,rfl⟩⟩
      · exact ⟨.right p,Or.inl ⟨rfl,rfl⟩⟩
    · obtain ⟨j,b⟩ := p
      change i=j at inc
      subst j
      cases b
      · exact ⟨.vertical (i,false),Or.inr ⟨rfl,rfl⟩⟩
      · exact ⟨.vertical (i,true),Or.inl ⟨rfl,rfl⟩⟩
  rcases a with c|p <;> rcases b with d|q
  · exact h.elim
  · exact forward c q h
  · obtain ⟨e,⟨hd,hp⟩|⟨hd,hp⟩⟩ := forward d p h
    · exact ⟨e,Or.inr ⟨hp,hd⟩⟩
    · exact ⟨e,Or.inl ⟨hp,hd⟩⟩
  · exact h.elim

private noncomputable def atTime {m : ℕ} : Segment m → ℝ → Plane
  | .left p,t => (t-1,t*leafY p)
  | .right p,t => (1-t,t*leafY p)
  | .vertical p,t => (0,lowerY p+t)

private theorem atTime_eq {m : ℕ} (e : Segment m) (t : ℝ) :
    mix (point (tail e)) (point (tip e)) t = atTime e t := by
  cases e with
  | left p => ext <;> simp [tail,tip,point,mix,atTime]
  | right p => ext <;> simp [tail,tip,point,mix,atTime]
  | vertical p =>
    obtain ⟨i,b⟩ := p
    cases b <;> ext <;> simp [tail,tip,point,mix,atTime,leafY,lowerY] <;> ring

private theorem normalize {m : ℕ} {a b : V m} (h : (graph m).Adj a b)
    {t : ℝ} (ht : 0<t) (ht' : t<1) :
    ∃ (e : Segment m) (r : ℝ), Ends e a b ∧ 0<r ∧ r<1 ∧
      mix (point a) (point b) t = atTime e r := by
  obtain ⟨e,ends⟩ := orient h
  rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨e,t,Or.inl ⟨rfl,rfl⟩,ht,ht',atTime_eq e t⟩
  · refine ⟨e,1-t,Or.inr ⟨rfl,rfl⟩,by linarith,by linarith,?_⟩
    rw [← atTime_eq]
    ext <;> simp [mix] <;> ring

/-- The vertical segment is strictly between two consecutive integer levels. -/
private theorem between_levels (i j : ℕ) {s : ℝ} (hs : 0<s) (hs' : s<1) :
    (i : ℝ)+s ≠ j := by
  intro h
  by_cases hji : j ≤ i
  · have : (j : ℝ) ≤ i := by exact_mod_cast hji
    linarith
  · have : (i : ℝ)+1 ≤ j := by exact_mod_cast (show i+1 ≤ j by omega)
    linarith

private theorem avoid {m : ℕ} (e : Segment m) (v : V m) {s : ℝ} (hs : 0<s) (hs' : s<1) :
    atTime e s ≠ point v := by
  intro meet
  have x := congrArg Prod.fst meet
  have y := congrArg Prod.snd meet
  cases e with
  | left p =>
    rcases v with ((b|i)|q)
    · cases b <;> norm_num [point,atTime] at x <;> linarith
    · simp [point,atTime] at x; linarith
    · simp [point,atTime] at x; linarith
  | right p =>
    rcases v with ((b|i)|q)
    · cases b <;> norm_num [point,atTime] at x <;> linarith
    · simp [point,atTime] at x; linarith
    · simp [point,atTime] at x; linarith
  | vertical p =>
    rcases v with ((b|i)|q)
    · cases b <;> norm_num [point,atTime] at x
    · exact between_levels (lowerY p) (3*i.val+1) hs hs' y
    · exact between_levels (lowerY p) (leafY q) hs hs' y

private theorem same_level (i j : ℕ) {s t : ℝ} (hs : 0<s) (hs' : s<1)
    (ht : 0<t) (ht' : t<1) (eq : (i : ℝ)+s=j+t) : i=j := by
  rcases lt_trichotomy i j with less|same|greater
  · have : (i : ℝ)+1 ≤ j := by exact_mod_cast (show i+1 ≤ j by omega)
    linarith
  · exact same
  · have : (j : ℝ)+1 ≤ i := by exact_mod_cast (show j+1 ≤ i by omega)
    linarith

private theorem unique_segment {m : ℕ} (e f : Segment m) {s t : ℝ}
    (hs : 0<s) (hs' : s<1) (ht : 0<t) (ht' : t<1) (h : atTime e s = atTime f t) : e=f := by
  have x := congrArg Prod.fst h
  have y := congrArg Prod.snd h
  have spoke {p q : Leaf m} (same : s=t) (heq : s*leafY p=t*leafY q) : p=q := by
    rw [← same] at heq
    apply leafY_inj
    exact_mod_cast (mul_left_cancel₀ hs.ne' heq)
  cases e <;> cases f <;> simp only [atTime] at x y
  all_goals first
    | exact congrArg Segment.left (spoke (by linarith) y)
    | exact congrArg Segment.right (spoke (by linarith) y)
    | exact congrArg Segment.vertical (lowerY_inj (same_level _ _ hs hs' ht ht' y))
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
end PlanarRainbow464
