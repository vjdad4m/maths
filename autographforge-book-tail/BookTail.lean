import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Lattice
import Mathlib.Topology.Path
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Ján Pastorek's normalized rows 187, 221 and 877. A book with a pendant path. -/
namespace BookTail
open SimpleGraph Finset
open scoped unitInterval
set_option maxHeartbeats 3200000
set_option maxRecDepth 16384

/-- Consecutive indices of a simple cycle in either direction, including its closing edge. -/
def consecutive {k : ℕ} (i j : Fin k) : Prop :=
  i.val+1 = j.val ∨ j.val+1 = i.val ∨
    (i.val=0 ∧ j.val+1=k) ∨ (j.val=0 ∧ i.val+1=k)

/-- The usual forbidden-induced-cycle definition of a chordal graph. -/
def Chordal {U : Type*} (G : SimpleGraph U) : Prop :=
  ∀ k, 4 ≤ k → ¬∃ f : Fin k ↪ U, ∀ i j, G.Adj (f i) (f j) ↔ consecutive i j



/-- The two neighbors of an index on an induced cycle of length at least four
are distinct and are not consecutive to one another. -/
private theorem cycle_neighbors {k : ℕ} (hk : 4 ≤ k) (i : Fin k) :
    ∃ p s : Fin k, consecutive i p ∧ consecutive i s ∧ p ≠ s ∧ ¬consecutive p s := by
  let near (a b : ℕ) := a+1=b ∨ b+1=a ∨ (a=0 ∧ b+1=k) ∨ (b=0 ∧ a+1=k)
  have build (a b : ℕ) (ha : a<k) (hb : b<k)
      (check : near i.val a ∧ near i.val b ∧ a≠b ∧ ¬near a b) :
      ∃ p s : Fin k, consecutive i p ∧ consecutive i s ∧ p≠s ∧ ¬consecutive p s :=
    ⟨⟨a,ha⟩,⟨b,hb⟩,check.1,check.2.1,fun e => check.2.2.1 (congrArg Fin.val e),check.2.2.2⟩
  by_cases first : i.val=0
  · exact build (k-1) 1 (by omega) (by omega) (by dsimp [near]; omega)
  by_cases last : i.val+1=k
  · exact build (i.val-1) 0 (by omega) (by omega) (by dsimp [near]; omega)
  · exact build (i.val-1) (i.val+1) (by omega) (by omega) (by dsimp [near]; omega)

/-- An elimination order certifies the forbidden-induced-cycle definition. -/
theorem chordal_of_elimination {U : Type*} (G : SimpleGraph U) (r : U → ℕ)
    (clique : ∀ x y z, G.Adj x y → G.Adj x z → y≠z →
      r y ≤ r x → r z ≤ r x → G.Adj y z) : Chordal G := by
  rintro k hk ⟨f,cyc⟩
  have nonempty : (univ : Finset (Fin k)).Nonempty := ⟨⟨0,by omega⟩,mem_univ _⟩
  obtain ⟨i,_,top⟩ := exists_max_image univ (fun j => r (f j)) nonempty
  obtain ⟨p,s,ip,is,ne,gap⟩ := cycle_neighbors hk i
  exact gap ((cyc p s).mp (clique (f i) (f p) (f s) ((cyc i p).mpr ip) ((cyc i s).mpr is)
    (f.injective.ne ne) (top p (mem_univ _)) (top s (mem_univ _))))

abbrev V := Fin 11

/-- Vertices 0 and 1 are the common edge, 2 through 4 are the third vertices
of the triangles, and 5 through 10 are the pendant path, attached to 0. -/
def edge (x y : V) :=
  (x<2 ∧ y<5 ∧ x≠y) ∨ (y<2 ∧ x<5 ∧ x≠y) ∨
  (x=0 ∧ y=5) ∨ (x=5 ∧ y=0) ∨ (5≤x.val ∧ x.val+1=y.val) ∨ (5≤y.val ∧ y.val+1=x.val)

instance (x y : V) : Decidable (edge x y) := by unfold edge; infer_instance

def graph : SimpleGraph V where
  Adj := edge
  symm := by change ∀ x y, edge x y → edge y x; decide
  loopless := by change ∀ x, ¬edge x x; decide

instance (x y : V) : Decidable (graph.Adj x y) := inferInstanceAs (Decidable (edge x y))

theorem chordal : Chordal graph := chordal_of_elimination graph Fin.val (by decide)

theorem noK4 : graph.CliqueFree 4 := by
  have check : ∀ a b : V, graph.Adj a b → ∀ c : V, graph.Adj a c → graph.Adj b c →
      ∀ d : V, graph.Adj a d → graph.Adj b d → ¬graph.Adj c d := by decide
  by_contra bad
  obtain ⟨f⟩ := (not_cliqueFree_iff _).mp bad
  have adj (i j : Fin 4) (ne : i≠j) : graph.Adj (f i) (f j) := f.map_adj_iff.mpr ne
  exact check (f 0) (f 1) (adj 0 1 (by decide)) (f 2) (adj 0 2 (by decide))
    (adj 1 2 (by decide)) (f 3) (adj 0 3 (by decide)) (adj 1 3 (by decide)) (adj 2 3 (by decide))

noncomputable def degreesDesc {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)

noncomputable def slater {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  sInf {t | Fintype.card U ≤ t + ((degreesDesc G).take t).sum}

theorem slater_exact : slater graph = 2 := by
  let L : List ℕ := [5,4,2,2,2,2,2,2,2,2,1]
  have degreeList : degreesDesc graph = L := by
    unfold degreesDesc
    rw [Finset.val_univ_fin,Multiset.map_coe,Multiset.coe_sort]
    have eq : (List.finRange 11).map (fun v => graph.degree v) = L := by decide
    rw [eq,List.mergeSort_eq_self (· ≥ ·) (by decide)]
  unfold slater
  rw [degreeList,Fintype.card_fin]
  let costs : Set ℕ := {k | 11 ≤ k + (L.take k).sum}
  have feasible : 2 ∈ costs := by decide
  apply Nat.le_antisymm (Nat.sInf_le (s := costs) feasible)
  have good := Nat.sInf_mem (show costs.Nonempty from ⟨_,feasible⟩)
  change 2 ≤ sInf costs
  by_cases hi : 2 ≤ sInf costs
  · exact hi
  exfalso
  obtain h | h := (show sInf costs=0 ∨ sInf costs=1 by omega)
  · rw [h] at good
    exact (show 0 ∉ costs by decide) good
  · rw [h] at good
    exact (show 1 ∉ costs by decide) good

/-- A walk attaining the table entry exists if a neighbor decreases it by one. -/
theorem metric_certificate {U : Type*} {G : SimpleGraph U} (d : U → U → ℕ)
    (zero : ∀ x y, d x y=0 ↔ x=y)
    (edgeBound : ∀ x y z, G.Adj y z → d x z ≤ d x y+1)
    (down : ∀ x y, x≠y → ∃ z, G.Adj z y ∧ d x z+1=d x y) :
    (∀ x y, G.Reachable x y) ∧ ∀ x y, G.dist x y=d x y := by
  have attained (x y : U) : ∃ p : G.Walk x y, p.length=d x y := by
    generalize hv : d x y = k
    induction k generalizing y with
    | zero =>
      obtain rfl := (zero x y).mp hv
      exact ⟨.nil,rfl⟩
    | succ k ih =>
      have ne : x≠y := by rintro rfl; have := (zero x x).mpr rfl; omega
      obtain ⟨z,zy,drop⟩ := down x y ne
      obtain ⟨p,eq⟩ := ih z (by omega)
      exact ⟨p.concat zy,by simp [eq]⟩
  have lower {u v : U} (p : G.Walk u v) (x : U) : d x v ≤ d x u+p.length := by
    induction p with
    | nil => simp
    | cons e p ih =>
      have step := edgeBound x _ _ e
      simp only [Walk.length_cons]
      omega
  have reach (x y : U) : G.Reachable x y := (attained x y).choose.reachable
  refine ⟨reach,fun x y => ?_⟩
  obtain ⟨p,eq⟩ := attained x y
  obtain ⟨q,short⟩ := (reach x y).exists_walk_length_eq_dist
  have lb := lower q x
  rw [(zero x x).mpr rfl,zero_add,short] at lb
  exact le_antisymm ((SimpleGraph.dist_le p).trans_eq eq) lb

private def hubDist (v : V) := if v=0 then 0 else if v.val<5 then 1 else v.val-4

private def distanceTable (u v : V) :=
  if u=v then 0 else if 5≤u.val ∧ 5≤v.val then max u.val v.val - min u.val v.val
  else if 5≤u.val ∨ 5≤v.val then hubDist u + hubDist v else if edge u v then 1 else 2

private theorem metric : (∀ x y, graph.Reachable x y) ∧ ∀ x y, graph.dist x y = distanceTable x y := @metric_certificate V graph distanceTable (by decide) (by decide) (by decide)

theorem connected : graph.Connected := ⟨metric.1⟩

noncomputable def eccentricity {U : Type*} [Fintype U] (G : SimpleGraph U) (u : U) := univ.sup (G.dist u)
noncomputable def radius {U : Type*} [Fintype U] (G : SimpleGraph U) := sInf (Set.range (eccentricity G))
noncomputable def diameter {U : Type*} [Fintype U] (G : SimpleGraph U) := univ.sup (eccentricity G)

/-- Source wrappers assign positive infinity on disconnected inputs. -/
noncomputable def sourceValue {U : Type*} (G : SimpleGraph U) (q : ℕ) : WithTop ℚ := by
  classical
  exact if G.Connected then ↑(q : ℚ) else ⊤

private def ecc (u : V) := univ.sup (distanceTable u)

private theorem eccentricity_eq (u : V) : eccentricity graph u = ecc u := by
  unfold eccentricity ecc
  exact congrArg (fun f : V → ℕ => univ.sup f) (funext (metric.2 u))

theorem diameter_exact : diameter graph = 7 := by
  have eq : eccentricity graph = ecc := funext eccentricity_eq
  unfold diameter
  rw [eq]
  decide

theorem radius_exact : radius graph = 4 := by
  have eq : eccentricity graph = ecc := funext eccentricity_eq
  unfold radius
  rw [eq]
  have hit : 4 ∈ Set.range ecc := ⟨7,by decide⟩
  have lower : ∀ x : V, 4 ≤ ecc x := by decide
  obtain ⟨x,hx⟩ := Nat.sInf_mem (show (Set.range ecc).Nonempty from ⟨_,hit⟩)
  exact le_antisymm (Nat.sInf_le hit) ((lower x).trans_eq hx)

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

private def grid (v : V) : ℤ × ℤ := if v=0 then (0,0) else if v=1 then (12,0) else if v.val<5 then (6, (v.val : ℤ)^2)
  else let j := (v.val : ℤ)-4; (-j,100*j^2+17*j)

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

noncomputable def witnessDrawing : PlaneDrawing graph where
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

theorem row187_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Chordal G → Planar G →
    sourceValue G (radius G) ≤ ↑((2 : ℚ)*slater G-1)) := by
  intro claim
  have h := claim V graph (by decide) chordal ⟨witnessDrawing⟩
  norm_num [sourceValue,connected,radius_exact,slater_exact] at h
  exact (by decide : ¬((4 : WithTop ℚ) ≤ 3)) h

theorem row221_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Chordal G → Planar G →
    sourceValue G (diameter G) ≤ ↑((4 : ℚ)*slater G-2)) := by
  intro claim
  have h := claim V graph (by decide) chordal ⟨witnessDrawing⟩
  norm_num [sourceValue,connected,diameter_exact,slater_exact] at h
  exact (by decide : ¬((7 : WithTop ℚ) ≤ 6)) h

theorem row877_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → G.CliqueFree 4 → Chordal G →
    sourceValue G (radius G) ≤ ↑((3/2 : ℚ)*slater G)) := by
  intro claim
  have h := claim V graph (by decide) noK4 chordal
  norm_num [sourceValue,connected,radius_exact,slater_exact] at h
  exact (by decide : ¬((4 : WithTop ℚ) ≤ 3)) h

#print axioms chordal_of_elimination
#print axioms metric_certificate
#print axioms connected
#print axioms slater_exact
#print axioms radius_exact
#print axioms diameter_exact
#print axioms witnessDrawing
#print axioms row187_false
#print axioms row221_false
#print axioms row877_false
end BookTail
