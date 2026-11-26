import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

import Mathlib.Topology.Path
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Standalone counterexamples to Ján Pastorek's AutoGraphForge normalized lines
303 and 1908 at commit 4d1a8afc99447cacd2328cca20e47b6493e8dbc5.
The ring of five diamonds, the operation models, and the exact invariant proofs
are reproduced from AutoGraphForgeDiamonds.lean; planarity is proved below by
a drawing of the ring in the real plane. -/
namespace AutoGraphPowerBurning

inductive Observed {V : Type*} (G : SimpleGraph V) (S : Finset V) : V → Prop where
  | root {v} (h : v ∈ S) : Observed G S v
  | neighbor {v w} (h : w ∈ S) (hvw : G.Adj v w) : Observed G S v
  | force {v w} (hvw : G.Adj v w) (hw : Observed G S w)
      (rest : ∀ u, G.Adj w u → u ≠ v → Observed G S u) : Observed G S v

noncomputable def power {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ S : Finset V, n = S.card ∧ ∀ v, Observed G S v}

def Burns {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ source : Fin k → V, ∀ v, ∃ t : Fin k, ∃ p : G.Walk (source t) v,
    p.length ≤ k - 1 - t.val

noncomputable def burning {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | Burns G k}

end AutoGraphPowerBurning

namespace AutoGraphForgeDiamonds
open SimpleGraph Finset AutoGraphPowerBurning
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
abbrev V := Fin 5 × Fin 4

def edges (a b : V) : Prop :=
  (a.1 = b.1 ∧ a.2 ≠ b.2 ∧ (a.2 = 1 ∨ a.2 = 2 ∨ b.2 = 1 ∨ b.2 = 2)) ∨
  (a.2 = 3 ∧ b.2 = 0 ∧ a.1 + 1 = b.1) ∨ (b.2 = 3 ∧ a.2 = 0 ∧ b.1 + 1 = a.1)
instance (a b : V) : Decidable (edges a b) := by unfold edges; infer_instance

def graph : SimpleGraph V where
  Adj := edges
  symm := by change ∀ a b : V, edges a b → edges b a; decide
  loopless := by change ∀ a : V, ¬ edges a a; decide

instance (a b : V) : Decidable (graph.Adj a b) := inferInstanceAs (Decidable (edges a b))

/-- The source predicate forbidding an induced claw. -/
def ClawFree {U : Type*} (G : SimpleGraph U) := ∀ v a b c : U,
  G.Adj v a → G.Adj v b → G.Adj v c → a ≠ b → a ≠ c → b ≠ c →
  G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

theorem clawFree : ClawFree graph := by
  have check : ∀ v a : V, graph.Adj v a → ∀ b : V, graph.Adj v b → ∀ c : V, graph.Adj v c →
      a ≠ b → a ≠ c → b ≠ c → graph.Adj a b ∨ graph.Adj a c ∨ graph.Adj b c := by decide
  exact fun v a b c ha hb hc => check v a ha b hb c hc

theorem cubic : graph.IsRegularOfDegree 3 := by
  have h : ∀ a : V, (univ.filter (edges a)).card = 3 := by decide
  intro a
  rw [SimpleGraph.degree, neighborFinset_eq_filter]
  exact h a

private def middle (i : Fin 5) (v : V) : Prop := v.1 = i ∧ (v.2=1 ∨ v.2=2)
private instance (i : Fin 5) (v : V) : Decidable (middle i v) := by unfold middle; infer_instance

/-- In a seedless diamond the two middle vertices form an unobserved fort. -/
private theorem missed (S : Finset V) (i : Fin 5) (miss : ∀ v ∈ S, v.1 ≠ i)
    {v : V} (obs : Observed graph S v) : ¬ middle i v := by
  have neighbors : ∀ (i : Fin 5) (v : V), middle i v → ∀ w : V, graph.Adj v w → w.1=i := by decide
  have twin : ∀ (i : Fin 5) (v : V), middle i v → ∀ w : V, graph.Adj v w → ¬middle i w →
      ∃ u : V, u ≠ v ∧ middle i u ∧ graph.Adj w u := by decide
  induction obs with
  | root hv => exact fun h => miss _ hv h.1
  | neighbor hw e => exact fun h => miss _ hw (neighbors _ _ h _ e)
  | @force v w e _ _ ihw ihrest =>
    intro hv
    obtain ⟨u,ne,hu,wu⟩ := twin i v hv w e ihw
    exact ihrest u wu ne hu

theorem power_exact : power graph = 5 := by
  classical
  let sizes := {n | ∃ S : Finset V, n = S.card ∧ ∀ v, Observed graph S v}
  have all : sizes.Nonempty := ⟨_,univ,rfl,fun x => .root (mem_univ x)⟩
  obtain ⟨S,cost,full⟩ := Nat.sInf_mem all
  change power graph = S.card at cost
  have covers : S.image Prod.fst = univ := by
    apply eq_univ_of_forall
    intro i
    by_contra h
    have no : ∀ v ∈ S, v.1 ≠ i := fun v hv hi => h (mem_image.mpr ⟨v,hv,hi⟩)
    exact missed S i no (full (i,1)) ⟨rfl,Or.inl rfl⟩
  have lo := card_image_le (f := Prod.fst) (s := S)
  rw [covers,card_univ,Fintype.card_fin,← cost] at lo
  apply Nat.le_antisymm _ lo
  let sel : Fin 5 ↪ V := ⟨fun i => (i,1),fun _ _ e => congrArg Prod.fst e⟩
  let D := univ.map sel
  apply Nat.sInf_le (s := sizes)
  refine ⟨D, by simp [D], ?_⟩
  intro v
  have seed : (v.1,1) ∈ D := mem_map.mpr ⟨v.1,mem_univ _,rfl⟩
  by_cases h : v.2 = 1
  · exact .root (show v ∈ D from (show (v.1,1) = v from Prod.ext rfl h.symm) ▸ seed)
  · apply Observed.neighbor seed
    exact Or.inl ⟨rfl,h,Or.inr (Or.inr (Or.inl rfl))⟩

private def within : ℕ → V → V → Bool
  | 0, u, v => decide (u = v)
  | n+1, u, v => decide (u = v ∨ ∃ w : V, graph.Adj u w ∧ within n w v = true)

private theorem walk_of_within {n : ℕ} {u v : V} (h : within n u v = true) :
    ∃ p : graph.Walk u v, p.length ≤ n := by
  induction n generalizing u v with
  | zero =>
    have e : u=v := of_decide_eq_true h
    subst v
    exact ⟨.nil,by simp⟩
  | succ n ih =>
    change decide (_ ∨ _) = true at h
    rcases of_decide_eq_true h with rfl | ⟨w,uw,hit⟩
    · exact ⟨.nil,by simp⟩
    · obtain ⟨p,hp⟩ := ih hit
      exact ⟨.cons uw p,by simpa using hp⟩

private def source (t : Fin 4) : V :=
  if t = 0 then (0,0) else if t = 1 then (1,3) else if t = 2 then (3,0) else (3,3)

private theorem four_rounds : Burns graph 4 := by
  have cover : ∀ v : V, ∃ t : Fin 4, within (3-t.val) (source t) v = true := by decide
  refine ⟨source,fun v => ?_⟩
  obtain ⟨t,h⟩ := cover v
  exact ⟨t,walk_of_within h⟩


theorem burning_upper : burning graph ≤ 4 := Nat.sInf_le (s := {k | Burns graph k}) four_rounds

private theorem within_of_walk {u v : V} (p : graph.Walk u v) (n : ℕ) (le : p.length ≤ n) :
    within n u v = true := by
  induction p generalizing n with
  | nil =>
    cases n with
    | zero => simp [within]
    | succ n => simp [within]
  | cons e p ih =>
    cases n with
    | zero => simp at le
    | succ n =>
      apply decide_eq_true
      exact Or.inr ⟨_,e,ih n (by simpa using le)⟩

theorem burning_exact : burning graph = 4 := by
  classical
  apply le_antisymm burning_upper
  by_contra bad
  have witness : ({k | Burns graph k} : Set ℕ).Nonempty := ⟨4,four_rounds⟩
  let k := burning graph
  have hk : k ≤ 3 := by dsimp [k]; omega
  obtain ⟨start,cover⟩ := (show Burns graph k from Nat.sInf_mem witness)
  let ignite (t : Fin 3) := if h : t.val < k then start ⟨t.val,h⟩ else (0,0)
  let ball (t : Fin 3) := univ.filter (fun v => within (2-t.val) (ignite t) v = true)
  have all : univ.biUnion ball = univ := by
    apply eq_univ_of_forall
    intro v
    obtain ⟨t,p,len⟩ := cover v
    let j : Fin 3 := ⟨t.val,by have := t.isLt; omega⟩
    apply mem_biUnion.mpr
    refine ⟨j,mem_univ _, mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    change within (2-t.val) (if h : t.val < k then start ⟨t.val,h⟩ else (0,0)) v = true
    rw [dif_pos t.isLt]
    exact within_of_walk p _ (by omega)
  have every : ∀ (t : Fin 3) (w : V),
      (univ.filter (fun v => within (2-t.val) w v = true)).card ≤ (if t=0 then 10 else if t=1 then 4 else 1) := by decide
  have big := card_biUnion_le (s := (univ : Finset (Fin 3))) (t := ball)
  rw [all,card_univ] at big
  have few := sum_le_sum (s := (univ : Finset (Fin 3))) (fun t _ => every t (ignite t))
  change ∑ t, (ball t).card ≤ _ at few
  have sum : (∑ t : Fin 3, if t=0 then 10 else if t=1 then 4 else 1) = 15 := by decide
  rw [sum] at few
  have n : Fintype.card V = 20 := by decide
  omega

end AutoGraphForgeDiamonds

/-! The two catalogue claims for planar graphs are refuted by an actual drawing
in the real plane. All edge arcs are topological embeddings of the unit interval. -/
namespace AutoGraphForgePlanar
open SimpleGraph AutoGraphForgeDiamonds AutoGraphPowerBurning
open scoped unitInterval
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

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

def grid (v : V) : ℤ × ℤ :=
  let k : ℤ := 4 * v.1.val
  let x := k + (if v.2=0 then 0 else if v.2=3 then 2 else 1)
  (x, x*x + if v.2=1 then 2 else 0)

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

noncomputable def ringDrawing : PlaneDrawing graph where
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

theorem planar_ring : Planar graph := ⟨ringDrawing⟩

/-- Normalized line 303, raw 318, record d7c7a4aa. -/
theorem counterexample_line303 : 2 ≤ Fintype.card V ∧ ClawFree graph ∧ Planar graph ∧
    ¬power graph ≤ burning graph :=
  ⟨by decide,clawFree,planar_ring,by have := power_exact; have := burning_exact; omega⟩

/-- Normalized line 1908, raw 1972, record 8fe7481e. -/
theorem counterexample_line1908 : 2 ≤ Fintype.card V ∧ Planar graph ∧
    (∃ d, graph.IsRegularOfDegree d) ∧ ¬power graph ≤ burning graph :=
  ⟨by decide,planar_ring,⟨3,cubic⟩,by have := power_exact; have := burning_exact; omega⟩

/-- The universal conjectures themselves, with the hypotheses of the pinned rows. -/
theorem line303_false : ¬ ∀ (U : Type) [Fintype U] (G : SimpleGraph U),
    2 ≤ Fintype.card U → ClawFree G → Planar G → power G ≤ burning G := by
  intro all
  exact counterexample_line303.2.2.2 (all V graph (by decide) clawFree planar_ring)

theorem line1908_false : ¬ ∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Planar G → (∃ d, G.IsRegularOfDegree d) → power G ≤ burning G := by
  intro all
  exact counterexample_line1908.2.2.2 (all V graph (by decide) planar_ring ⟨3,cubic⟩)

#print axioms power_exact
#print axioms burning_exact
#print axioms planar_ring
#print axioms counterexample_line303
#print axioms counterexample_line1908
#print axioms line303_false
#print axioms line1908_false
end AutoGraphForgePlanar

