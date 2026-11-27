import Forts
import PlaneBasis

namespace Book567.Drawing
open SimpleGraph AutoGraphPowerBurning
open scoped unitInterval

/-- Four consecutive levels, in order: plain page, first leaf, support, second leaf. -/
private def level {n} (i : Fin n) (u : Fin 4) : ℕ :=
  4*i.val + (![0,2,1,3] : Fin 4 → ℕ) u

private theorem level_inj {n} {i j : Fin n} {u v : Fin 4} (h : level i u = level j v) :
    i = j ∧ u = v := by
  let slot : Fin 4 → ℕ := ![0,2,1,3]
  have small (a : Fin 4) : slot a < 4 := by fin_cases a <;> decide
  change 4*i.val + slot u = 4*j.val + slot v at h
  have hi : i = j := Fin.ext (by have := small u; have := small v; omega)
  subst j
  refine ⟨rfl, ?_⟩
  have he : slot u = slot v := Nat.add_left_cancel h
  fin_cases u <;> fin_cases v <;> first | rfl | simp [slot] at he

private noncomputable def point {n} : V n → Plane
  | .inl false => (-1,0)
  | .inl true => (1,0)
  | .inr (i,u) => (0,(level i u : ℝ)+1)

private theorem point_inj {n} : Function.Injective (@point n) := by
  rintro (b|⟨i,u⟩) (c|⟨j,v⟩) eq
  · cases b <;> cases c <;> norm_num [point] at eq ⊢
  · cases b <;> norm_num [point] at eq
  · cases c <;> norm_num [point] at eq
  · have y := congrArg Prod.snd eq
    change (level i u : ℝ)+1=(level j v : ℝ)+1 at y
    obtain ⟨rfl,rfl⟩ := level_inj (i:=i) (j:=j) (u:=u) (v:=v) (by exact_mod_cast add_right_cancel y)
    rfl

private inductive Segment where
  | spine
  | left (h : ℕ)
  | right (h : ℕ)
  | vertical (h : ℕ)

private noncomputable def start : Segment → Plane
  | .spine | .left _ => (-1,0)
  | .right _ => (1,0)
  | .vertical h => (0,(h:ℝ)+1)
private noncomputable def finish : Segment → Plane
  | .spine => (1,0)
  | .left h | .right h => (0,(h:ℝ)+1)
  | .vertical h => (0,(h:ℝ)+2)

private def Ends {n} (e : Segment) (a b : V n) :=
  (point a = start e ∧ point b = finish e) ∨ (point b = start e ∧ point a = finish e)

private theorem orient {n} {a b : V n} (edge : (graph n).Adj a b) : ∃ e, Ends e a b := by
  have spoke (z : Bool) (i : Fin n) (u : Fin 4) : ∃ e, Ends e (hub z) (site i u) := by
    cases z
    · exact ⟨.left _,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨.right _,Or.inl ⟨rfl,rfl⟩⟩
  rcases a with z|⟨i,u⟩ <;> rcases b with w|⟨j,v⟩
  · cases z <;> cases w
    · exact (edge rfl).elim
    · exact ⟨.spine,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨.spine,Or.inr ⟨rfl,rfl⟩⟩
    · exact (edge rfl).elim
  · exact spoke z j v
  · obtain ⟨e,he⟩ := spoke w i u
    exact ⟨e,he.symm⟩
  · obtain ⟨rfl,h⟩ := edge
    have consecutive : level i u + 1 = level i v ∨ level i v + 1 = level i u := by
      fin_cases u <;> fin_cases v <;> simp [level,inside] at h ⊢
    have up {x y : Fin 4} (s : level i x + 1 = level i y) :
        point (site i x) = start (.vertical (level i x)) ∧
        point (site i y) = finish (.vertical (level i x)) := by
      refine ⟨rfl,?_⟩
      simp [point,site,finish,← s]; ring
    rcases consecutive with s|s
    · exact ⟨_,Or.inl (up s)⟩
    · exact ⟨_,Or.inr (up s)⟩

private noncomputable def atTime : Segment → ℝ → Plane
  | .spine,t => (2*t-1,0)
  | .left h,t => (t-1,t*((h:ℝ)+1))
  | .right h,t => (1-t,t*((h:ℝ)+1))
  | .vertical h,t => (0,(h:ℝ)+1+t)

private theorem interpolate (e : Segment) (s : ℝ) :
    mix (start e) (finish e) s = atTime e s := by
  cases e <;> ext <;> simp [mix,start,finish,atTime] <;> ring

private theorem normalize {n} {a b : V n} (h : (graph n).Adj a b)
    {t : ℝ} (ht : 0<t) (ht' : t<1) :
    ∃ e r, Ends e a b ∧ 0<r ∧ r<1 ∧ mix (point a) (point b) t = atTime e r := by
  obtain ⟨e,ends⟩ := orient h
  rcases ends with pair|pair
  · exact ⟨e,t,Or.inl pair,ht,ht',by rw [pair.1,pair.2,interpolate]⟩
  · refine ⟨e,1-t,Or.inr pair,by linarith,by linarith,?_⟩
    rw [pair.1,pair.2,← interpolate]
    ext <;> simp [mix] <;> ring

private theorem avoid {n} (e : Segment) (v : V n) {s : ℝ} (hs : 0<s) (hs' : s<1) :
    atTime e s ≠ point v := by
  intro meet
  have x := congrArg Prod.fst meet
  have y := congrArg Prod.snd meet
  rcases v with b|⟨i,u⟩
  · cases b <;> cases e <;> simp [point,atTime] at x <;> linarith
  · cases e with
    | spine => simp [point,atTime] at y; linarith [Nat.cast_nonneg (α:=ℝ) (level i u)]
    | left h => simp [point,atTime] at x; linarith
    | right h => simp [point,atTime] at x; linarith
    | vertical h =>
      apply between_levels h (level i u) hs hs'
      change (h:ℝ)+1+s=(level i u:ℝ)+1 at y
      linarith

private theorem unique (e f : Segment) {s t : ℝ} (hs : 0<s) (hs' : s<1)
    (ht : 0<t) (ht' : t<1) (eq : atTime e s = atTime f t) : e=f := by
  have x := congrArg Prod.fst eq
  have y := congrArg Prod.snd eq
  have spoke {i j : ℕ} (same : s=t) (v : s*((i:ℝ)+1)=t*((j:ℝ)+1)) : i=j := by
    rw [← same] at v
    exact_mod_cast add_right_cancel (mul_left_cancel₀ hs.ne' v)
  have positive (i : ℕ) {r : ℝ} (hr : 0<r) : 0<r*((i:ℝ)+1) := by positivity
  cases e <;> cases f <;> simp only [atTime] at x y
  all_goals first
    | rfl
    | exact congrArg Segment.left (spoke (by linarith) y)
    | exact congrArg Segment.right (spoke (by linarith) y)
    | exact congrArg Segment.vertical (same_level _ _ hs hs' ht ht' (by linarith only [y]))
    | linarith
    | rename_i h; exact (positive h hs).ne' y |>.elim
    | rename_i h; exact (positive h ht).ne y |>.elim

noncomputable def bookDrawing (n : ℕ) : PlaneDrawing (graph n) where
  pos := point
  pos_injective := point_inj
  arc a b _ := segmentPath (point a) (point b)
  embedded _ _ e := ((segmentPath _ _).continuous.isClosedEmbedding
    (segment_injective (fun h => e.ne (point_inj h)))).isEmbedding
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
    have same := unique q q' hr hr' hr2 hr2' (shape.symm.trans (meet.trans shape'))
    subst q'
    rcases ends with ⟨a1,b1⟩|⟨b1,a1⟩ <;> rcases ends' with ⟨c1,d1⟩|⟨d1,c1⟩
    all_goals first
      | exact Or.inl ⟨point_inj (a1.trans c1.symm),point_inj (b1.trans d1.symm)⟩
      | exact Or.inr ⟨point_inj (a1.trans d1.symm),point_inj (b1.trans c1.symm)⟩

theorem family383 (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ Fintype.card (V n) ∧ (graph n).Connected ∧ Planar (graph n) ∧
    subTotal? (graph n) = some 2 ∧ power (graph n) = n+1 ∧ ¬ power (graph n) ≤ 2 := by
  obtain ⟨ord,_,conn,sub,pow,bad⟩ := family567 n hn
  exact ⟨ord,conn,⟨bookDrawing n⟩,sub,pow,bad⟩

#print axioms bookDrawing
#print axioms family383
end Book567.Drawing
