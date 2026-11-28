import ChainClasses
import AutoGraphForgePlanar

namespace TwinForcing
open SimpleGraph
open AutoGraphForgePlanar (Plane PlaneDrawing Planar)
open scoped unitInterval

private def col {n m : ℕ} : PageVertex n m → ℕ
  | .inl (i,b) => 3*i.val + 2*b.toNat
  | .inr (i,_) => 3*i.val + 1

private def height {n m : ℕ} : PageVertex n m → ℕ
  | .inl _ => 0
  | .inr (_,p) => p.val + 1

private theorem grid_injective {n m : ℕ} {a b : PageVertex n m}
    (hx : col a = col b) (hy : height a = height b) : a = b := by
  rcases a with ⟨i,s⟩|⟨i,p⟩ <;> rcases b with ⟨j,t⟩|⟨j,q⟩
  · cases s <;> cases t <;> simp [col] at hx
    · exact congrArg Sum.inl (Prod.ext (Fin.ext (by change i.val = j.val; omega)) rfl)
    · omega
    · omega
    · exact congrArg Sum.inl (Prod.ext (Fin.ext (by change i.val = j.val; omega)) rfl)
  · simp [height] at hy
  · simp [height] at hy
  · simp [col] at hx
    simp [height] at hy
    exact congrArg Sum.inr (Prod.ext (Fin.ext (by change i.val = j.val; omega)) (Fin.ext hy))

private theorem zero_height_of_col {n m : ℕ} {v : PageVertex n m}
    (h : col v % 3 ≠ 1) : height v = 0 := by
  cases v with
  | inl v => rfl
  | inr v => exact (h (by rcases v with ⟨i,p⟩; simp [col])).elim

private abbrev F (n m : ℕ) := chainGraph n m false

private theorem edge_columns {n m : ℕ} {a b : PageVertex n m}
    (e : (F n m).Adj a b) : col a + 1 = col b ∨ col b + 1 = col a := by
  rcases a with ⟨i,s⟩|⟨i,p⟩ <;> rcases b with ⟨j,t⟩|⟨j,q⟩
  · change chainHubAdj false (i,s) (j,t) at e
    rcases e with ⟨bad,_,_⟩|⟨rfl,rfl,k⟩|⟨rfl,rfl,k⟩
    · cases bad
    · left; change i.val+1 = j.val at k; simp [col]; omega
    · right; change j.val+1 = i.val at k; simp [col]; omega
  · change i = j at e
    subst j
    cases s <;> simp [col]
  · change j = i at e
    subst j
    cases t <;> simp [col]
  · exact e.elim

private noncomputable def point {n m : ℕ} (v : PageVertex n m) : Plane :=
  ((col v : ℝ), (height v : ℝ))

private theorem point_injective {n m : ℕ} : Function.Injective (@point n m) := by
  intro a b e
  apply grid_injective
  · exact_mod_cast (show (col a : ℝ) = col b from congrArg Prod.fst e)
  · exact_mod_cast (show (height a : ℝ) = height b from congrArg Prod.snd e)

private noncomputable def mix (a b : Plane) (s : ℝ) : Plane :=
  ((1-s)*a.1+s*b.1, (1-s)*a.2+s*b.2)

private theorem mix_swap (a b : Plane) (s : ℝ) :
    mix b a (1-s) = mix a b s := by
  apply Prod.ext <;> dsimp [mix] <;> ring

private noncomputable def segment (a b : Plane) : Path a b where
  toFun t := mix a b t
  continuous_toFun := by unfold mix; fun_prop
  source' := by simp [mix]
  target' := by simp [mix]

private theorem forward_x {n m : ℕ} {a b : PageVertex n m}
    (h : col a + 1 = col b) (s : ℝ) :
    (mix (point a) (point b) s).1 = (col a : ℝ) + s := by
  have h' : (col a : ℝ) + 1 = col b := by exact_mod_cast h
  dsimp [mix,point]
  rw [← h']
  ring

private theorem interior_vertex_forward {n m : ℕ} {a b : PageVertex n m}
    (h : col a + 1 = col b) (v : PageVertex n m) {s : ℝ}
    (hs : 0 < s) (ht : s < 1) : mix (point a) (point b) s ≠ point v := by
  intro e
  have eq := congrArg Prod.fst e
  rw [forward_x h] at eq
  change (col a : ℝ) + s = col v at eq
  have lt : (col a : ℝ) < col v := by linarith
  have gt : (col v : ℝ) < (col a : ℝ) + 1 := by linarith
  exact (not_lt_of_ge (Nat.succ_le_of_lt (by exact_mod_cast lt))) (by exact_mod_cast gt)

private theorem interiors_forward {n m : ℕ} {a b c d : PageVertex n m}
    (h : col a + 1 = col b) (k : col c + 1 = col d) {s t : ℝ}
    (hs : 0 < s) (hs' : s < 1) (ht : 0 < t) (ht' : t < 1)
    (eq : mix (point a) (point b) s = mix (point c) (point d) t) :
    a = c ∧ b = d := by
  have xx := congrArg Prod.fst eq
  rw [forward_x h, forward_x k] at xx
  have ac : col a = col c := by
    rcases lt_trichotomy (col a) (col c) with e|e|e
    · have ne : (col a : ℝ)+1 ≤ col c := by exact_mod_cast (Nat.succ_le_of_lt e)
      linarith
    · exact e
    · have ne : (col c : ℝ)+1 ≤ col a := by exact_mod_cast (Nat.succ_le_of_lt e)
      linarith
  have bd : col b = col d := by omega
  rw [ac,add_right_inj] at xx
  subst t
  have yy := congrArg Prod.snd eq
  change (1-s)*(height a : ℝ)+s*(height b : ℝ) =
    (1-s)*(height c : ℝ)+s*(height d : ℝ) at yy
  by_cases ha : col a % 3 = 1
  · have cross : col b % 3 ≠ 1 := by omega
    have hb := zero_height_of_col cross
    have hd := zero_height_of_col (v := d) (bd ▸ cross)
    rw [hb,hd] at yy
    have ey : (height a : ℝ) = height c := by
      apply mul_left_cancel₀ (show (1-s) ≠ 0 by linarith)
      simpa using yy
    exact ⟨grid_injective ac (by exact_mod_cast ey), grid_injective bd (hb.trans hd.symm)⟩
  · have za := zero_height_of_col ha
    have zc := zero_height_of_col (v := c) (ac ▸ ha)
    rw [za,zc] at yy
    have ey : (height b : ℝ) = height d := by
      apply mul_left_cancel₀ hs.ne'
      simpa using yy
    exact ⟨grid_injective ac (za.trans zc.symm), grid_injective bd (by exact_mod_cast ey)⟩

noncomputable def fanDrawing (n m : ℕ) : PlaneDrawing (F n m) where
  pos := point
  pos_injective := point_injective
  arc a b _ := segment (point a) (point b)
  embedded a b e := by
    apply ((segment (point a) (point b)).continuous.isClosedEmbedding ?_).isEmbedding
    intro s t eq
    apply Subtype.ext
    change mix (point a) (point b) (s : ℝ) = mix (point a) (point b) t at eq
    have hx := congrArg Prod.fst eq
    rcases edge_columns e with h|h
    · rw [forward_x h, forward_x h] at hx
      linarith
    · rw [← mix_swap _ _ (s : ℝ), ← mix_swap _ _ (t : ℝ), forward_x h, forward_x h] at hx
      linarith
  reverse_arc := by
    intro a b _
    apply Path.ext
    funext t
    change mix (point b) (point a) (t : ℝ) = mix (point a) (point b) (1-(t:ℝ))
    simpa only [sub_sub_cancel] using mix_swap (point a) (point b) (1-(t:ℝ))
  avoids_vertex := by
    intro a b e v s hs ht
    change mix (point a) (point b) (s : ℝ) ≠ point v
    rcases edge_columns e with h|h
    · exact interior_vertex_forward h v hs ht
    · rw [← mix_swap]
      exact interior_vertex_forward h v (by linarith) (by linarith)
  interiors := by
    intro a b c d e f s t hs hs' ht ht' eq
    change mix (point a) (point b) (s : ℝ) = mix (point c) (point d) (t : ℝ) at eq
    rcases edge_columns e with h|h <;> rcases edge_columns f with k|k
    · exact Or.inl (interiors_forward h k hs hs' ht ht' eq)
    · rw [← mix_swap (point c) (point d)] at eq
      exact Or.inr (interiors_forward h k hs hs' (by linarith) (by linarith) eq)
    · rw [← mix_swap (point a) (point b)] at eq
      obtain ⟨bc,ad⟩ := interiors_forward h k (by linarith) (by linarith) ht ht' eq
      exact Or.inr ⟨ad,bc⟩
    · rw [← mix_swap (point a) (point b), ← mix_swap (point c) (point d)] at eq
      obtain ⟨bd,ac⟩ := interiors_forward h k (by linarith) (by linarith) (by linarith) (by linarith) eq
      exact Or.inl ⟨ac,bd⟩

theorem fan_chain_planar (n m : ℕ) : Planar (F n m) := ⟨fanDrawing n m⟩

theorem fan_chain_triangle_free (n m : ℕ) : (F n m).CliqueFree 3 :=
  (fan_chain_two_colorable n m).cliqueFree (by decide)

theorem fan_gap_unbounded (M : ℕ) :
    ∃ (G : SimpleGraph (PageVertex (M+3) (4*M+9))) (dec : DecidableRel G.Adj),
      G.Connected ∧ G.Colorable 2 ∧ G.CliqueFree 3 ∧ Planar G ∧
      Graffiti324.residue G + M < @StarCone.forcing _ _ _ G dec 2 := by
  let G := F (M+3) (4*M+9)
  refine ⟨G,inferInstance,chain_connected (by omega) (by omega) false,
    fan_chain_two_colorable _ _,fan_chain_triangle_free _ _,fan_chain_planar _ _,?_⟩
  rw [show StarCone.forcing G 2 = graphResidue G + (2*M*M+8*M+7) from
    fan_chain_forcing_excess M, graphResidue_eq_residue]
  omega

#print axioms fan_chain_planar
#print axioms fan_chain_triangle_free
#print axioms fan_gap_unbounded
end TwinForcing
