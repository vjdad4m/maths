import AutoGraphForgePlanar
import Witness2535

namespace AutoGraphForge2535
open SimpleGraph
open AutoGraphForgePlanar (Plane PlaneDrawing Planar)
open scoped unitInterval
set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- Three strips, each containing one fan; the bridges join adjacent strips. -/
def grid (v : V) : ℤ × ℤ :=
  (4 * v.1.val + (if v.2 = 0 then 0 else if v.2 = 1 then 2 else 1),
    if Hub v then ([-1,-7,-16,-15,9,-9] : List ℤ)[2*v.1.val+v.2.val]! else (v.2.val : ℤ) - 1)

private def det {K : Type*} [CommRing K] (a b c : K × K) : K :=
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)

/-- Two points lie on one weak side of a line, with at least one strictly off it. -/
private def side {K : Type*} [Zero K] [LE K] [LT K] (u v : K) : Prop :=
  (0 ≤ u ∧ 0 ≤ v ∧ (0 < u ∨ 0 < v)) ∨ (u ≤ 0 ∧ v ≤ 0 ∧ (u < 0 ∨ v < 0))

private instance (u v : ℤ) : Decidable (side u v) := by unfold side; infer_instance

private theorem grid_injective : Function.Injective grid := by
  have h : ∀ u v : V, grid u = grid v → u = v := by decide
  exact fun _ _ => h _ _

private theorem grid_vertex : ∀ a b : V, graph.Adj a b → ∀ v : V,
    v ≠ a → v ≠ b → det (grid a) (grid b) (grid v) ≠ 0 := by decide

private theorem grid_edges : ∀ a b : V, graph.Adj a b → ∀ c d : V, graph.Adj c d →
    ¬((a=c ∧ b=d) ∨ (a=d ∧ b=c)) →
    side (det (grid a) (grid b) (grid c)) (det (grid a) (grid b) (grid d)) ∨
    side (det (grid c) (grid d) (grid a)) (det (grid c) (grid d) (grid b)) := by decide

noncomputable def point (v : V) : Plane := ((grid v).1, (grid v).2)

private theorem point_injective : Function.Injective point := by
  intro u v eq
  apply grid_injective
  simp only [point,Prod.mk.injEq] at eq
  exact Prod.ext (by exact_mod_cast eq.1) (by exact_mod_cast eq.2)

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

private theorem det_mix (a b c d : Plane) (s : ℝ) :
    det a b (mix c d s) = (1-s)*det a b c + s*det a b d := by
  unfold det mix
  ring

private theorem det_on (a b : Plane) (s : ℝ) : det a b (mix a b s) = 0 := by
  rw [det_mix]
  unfold det
  ring

private theorem det_cast (a b c : V) :
    det (point a) (point b) (point c) = (det (grid a) (grid b) (grid c) : ℤ) := by
  unfold det point
  push_cast
  rfl

private theorem side_cast {u v : ℤ} (h : side u v) : side (u : ℝ) (v : ℝ) := by
  unfold side at h ⊢
  exact_mod_cast h

private theorem weighted_nonzero {u v s : ℝ} (h : side u v) (hs : 0<s) (ht : s<1) :
    (1-s)*u+s*v ≠ 0 := by
  have h' : 0 < 1-s := sub_pos.mpr ht
  rcases h with ⟨hu,hv,hp|hp⟩ | ⟨hu,hv,hn|hn⟩
  · exact ne_of_gt (add_pos_of_pos_of_nonneg (mul_pos h' hp) (mul_nonneg hs.le hv))
  · exact ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg h'.le hu) (mul_pos hs hp))
  · exact ne_of_lt (add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg h' hn) (mul_nonpos_of_nonneg_of_nonpos hs.le hv))
  · exact ne_of_lt (add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos h'.le hu) (mul_neg_of_pos_of_neg hs hn))

private theorem different_points {a b : V} (e : graph.Adj a b) : point a ≠ point b :=
  fun h => e.ne (point_injective h)

/-- A common interior point is impossible when both endpoints of the second
segment lie on one weak side of the first line, at least one strictly. -/
private theorem exclude {a b c d : V} {s t : I}
    (h : side (det (grid a) (grid b) (grid c)) (det (grid a) (grid b) (grid d)))
    (ht : 0 < (t:ℝ)) (ht' : (t:ℝ) < 1)
    (meet : mix (point a) (point b) s = mix (point c) (point d) t) : False := by
  have eq := congrArg (det (point a) (point b)) meet
  rw [det_on,det_mix,det_cast,det_cast] at eq
  exact weighted_nonzero (side_cast h) ht ht' eq.symm

noncomputable def bridgeDrawing : PlaneDrawing graph where
  pos := point
  pos_injective := point_injective
  arc a b _ := segmentPath (point a) (point b)
  embedded _ _ e := ((segmentPath _ _).continuous.isClosedEmbedding
    (segment_injective (different_points e))).isEmbedding
  reverse_arc := by
    intro a b _
    apply Path.ext
    funext t
    change mix (point b) (point a) t = mix (point a) (point b) (1-(t:ℝ))
    apply Prod.ext <;> change _ = _ <;> dsimp [mix] <;> ring
  avoids_vertex := by
    intro a b e v s hs ht meet
    let arc := segmentPath (point a) (point b)
    have inj := segment_injective (different_points e)
    by_cases va : v=a
    · subst v
      have h : s=0 := inj (meet.trans arc.source.symm)
      subst s
      norm_num at hs
    by_cases vb : v=b
    · subst v
      have h : s=1 := inj (meet.trans arc.target.symm)
      subst s
      norm_num at ht
    have eq := congrArg (det (point a) (point b)) meet
    change det _ _ (mix _ _ _) = _ at eq
    rw [det_on,det_cast] at eq
    exact grid_vertex a b e v va vb (by exact_mod_cast eq.symm)
  interiors := by
    intro a b c d e f s t hs hs' ht ht' meet
    by_contra diff
    rcases grid_edges a b e c d f diff with h | h
    · exact exclude h ht ht' meet
    · exact exclude h hs hs' meet.symm

theorem planar_witness : Planar graph := ⟨bridgeDrawing⟩


/-- The claimed additive slack of two still fails on connected planar graphs. -/
theorem counterexample :
    2 ≤ Fintype.card V ∧ graph.Connected ∧ Planar graph ∧
      Graffiti324.residue graph + 2 < StarCone.forcing graph 2 :=
  ⟨by decide, connected, planar_witness, by rw [residue_exact,forcing_exact]; decide⟩

theorem row2535_false :
    ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (G : SimpleGraph U) [DecidableRel G.Adj],
      2 ≤ Fintype.card U → G.Connected → Planar G →
      StarCone.forcing G 2 ≤ Graffiti324.residue G + 2) := by
  intro h
  exact (not_le_of_gt counterexample.2.2.2) (h V graph counterexample.1 connected planar_witness)

#print axioms planar_witness
#print axioms counterexample
#print axioms row2535_false
end AutoGraphForge2535
