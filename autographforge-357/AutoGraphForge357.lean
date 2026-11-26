import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Path
import Mathlib.Topology.Algebra.Ring.Real

/-! Ján Pastorek, AutoGraphForge line 357, ID 67666b8b. The rainbow objective
and the one-color-per-vertex constraint follow the pinned GraphCalc ILP. -/
namespace AutoGraphForge357
open Finset SimpleGraph Function
open scoped BigOperators unitInterval
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000

section Forcing
variable {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U) [DecidableRel G.Adj]

/-- The simultaneous step and fixed iteration count from the pinned GraphInvariants.lean. -/
def step (S : Finset U) : Finset U :=
  S ∪ univ.filter (fun w => w ∉ S ∧ ∃ v ∈ S, G.neighborFinset v \ S = {w})
def Total (S : Finset U) : Prop :=
  (step G)^[Fintype.card U] S = univ ∧ ∀ v ∈ S, ∃ w ∈ S, G.Adj v w
noncomputable def totalNumber := sInf {k | ∃ S : Finset U, S.card = k ∧ Total G S}

private theorem grew (S : Finset U) : S ⊆ step G S := subset_union_left

private theorem forced {S : Finset U} {w : U} (hw : w ∈ step G S \ S) :
    ∃ v ∈ S, G.neighborFinset v \ S = {w} := by
  obtain ⟨inside,out⟩ := mem_sdiff.mp hw
  exact (mem_filter.mp ((mem_union.mp inside).resolve_left out)).2.2

private def spent (B S : Finset U) := B.filter (fun b => G.neighborFinset b ⊆ S)

/-- Once a vertex forces its unique remaining neighbor, it cannot force again.
If a vertex cover is initially blue, every subsequent force comes from the cover. -/
private theorem spent_step (B S : Finset U) (sub : B ⊆ S)
    (cover : ∀ v w, G.Adj v w → w ∉ B → v ∈ B) :
    (step G S).card + (spent G B S).card ≤ S.card + (spent G B (step G S)).card := by
  classical
  let T := step G S
  let old := spent G B S
  let new := spent G B T
  have st : S ⊆ T := grew G S
  have nested : old ⊆ new := fun v hv => by
    obtain ⟨hb,hn⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨hb,hn.trans st⟩
  have pick (w : U) (hw : w ∈ T \ S) :
      ∃ v ∈ new \ old, G.neighborFinset v \ S = {w} := by
    obtain ⟨v,_,eq⟩ := forced G hw
    have ww : w ∈ G.neighborFinset v \ S := eq.symm ▸ mem_singleton_self w
    obtain ⟨adj,white⟩ := mem_sdiff.mp ww
    have vb := cover v w ((G.mem_neighborFinset v _).mp adj) (fun hb => white (sub hb))
    have completed : G.neighborFinset v ⊆ T := by
      intro u hu
      by_cases old' : u ∈ S
      · exact st old'
      · have x := mem_sdiff.mpr ⟨hu,old'⟩
        rw [eq,mem_singleton] at x
        exact x ▸ (mem_sdiff.mp hw).1
    exact ⟨v,mem_sdiff.mpr ⟨mem_filter.mpr ⟨vb,completed⟩,
      fun hold => white ((mem_filter.mp hold).2 adj)⟩,eq⟩
  choose f hf he using pick
  have le : (T \ S).card ≤ (new \ old).card := by
    apply card_le_card_of_injOn (fun w => if h : w ∈ T \ S then f w h else w)
    · intro w hw
      simpa [hw] using hf w hw
    · intro w hw u hu eq
      change w ∈ T \ S at hw
      change u ∈ T \ S at hu
      simp only [dif_pos hw,dif_pos hu] at eq
      have a := he w hw
      rw [eq,he u hu] at a
      exact (singleton_inj.mp a).symm
  have a := card_sdiff_add_card_eq_card st
  have b := card_sdiff_add_card_eq_card nested
  change T.card + old.card ≤ S.card + new.card
  omega

theorem cover_forcing_bound (B S : Finset U) (sub : B ⊆ S)
    (cover : ∀ v w, G.Adj v w → w ∉ B → v ∈ B)
    (full : (step G)^[Fintype.card U] S = univ) : Fintype.card U ≤ S.card+B.card := by
  have inv (k : ℕ) : B ⊆ (step G)^[k] S ∧
      ((step G)^[k] S).card ≤ S.card + (spent G B ((step G)^[k] S)).card := by
    induction k with
    | zero => exact ⟨sub,by simp⟩
    | succ k ih =>
      rw [iterate_succ_apply']
      exact ⟨ih.1.trans (grew _ _),by have a := spent_step G B _ ih.1 cover; omega⟩
  have b := (inv (Fintype.card U)).2
  rw [full,card_univ] at b
  exact b.trans (Nat.add_le_add_left (card_le_card (filter_subset _ _)) _)

/-- An initially missed fort remains entirely uncolored at every round. -/
theorem hits_fort (F S : Finset U) (non : F.Nonempty)
    (fort : ∀ v ∉ F, ∀ w ∈ F, G.Adj v w → ∃ u ∈ F, u ≠ w ∧ G.Adj v u)
    (full : (step G)^[Fintype.card U] S = univ) : ∃ v ∈ F, v ∈ S := by
  by_contra! miss
  have blocked (k : ℕ) : ∀ v ∈ F, v ∉ (step G)^[k] S := by
    induction k with
    | zero => exact miss
    | succ k ih =>
      rw [iterate_succ_apply']
      intro w hw joined
      obtain ⟨v,hv,eq⟩ := forced G (mem_sdiff.mpr ⟨joined,ih w hw⟩)
      have adj := (mem_sdiff.mp (eq.symm ▸ mem_singleton_self w)).1
      obtain ⟨u,hu,ne,vu⟩ := fort v (fun mf => ih _ mf hv) w hw ((G.mem_neighborFinset _ _).mp adj)
      have other := mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr vu,ih u hu⟩
      rw [eq,mem_singleton] at other
      exact ne other
  obtain ⟨w,hw⟩ := non
  have fail := blocked (Fintype.card U) w hw
  exact fail (full.symm ▸ mem_univ w)
end Forcing

abbrev V := Fin 26

private def incidence (v h : V) : Prop :=
  (6 ≤ v.val ∧ v.val < 14 ∧ (h.val = (v.val-6)%4 ∨ h.val = (v.val-5)%4 ∨
    h.val = 4+(v.val-6)/4)) ∨ (14 ≤ v.val ∧ h.val = (v.val-14)/2)
private instance (v h : V) : Decidable (incidence v h) := by unfold incidence; infer_instance

def graph : SimpleGraph V where
  Adj a b := incidence a b ∨ incidence b a
  symm := fun _ _ h => h.symm
  loopless := by change ∀ a : V, ¬(incidence a a ∨ incidence a a); decide
instance (a b : V) : Decidable (graph.Adj a b) := inferInstanceAs (Decidable (incidence a b ∨ incidence b a))

private def hubs := univ.filter (fun v : V => v.val < 6)
private def leaves (b : V) := univ.filter (fun v : V => 14 ≤ v.val ∧ (v.val-14)/2 = b.val)

private theorem mandatory_hubs (S : Finset V) (h : Total graph S) : hubs ⊆ S := by
  intro b hb
  have pair : ∀ b ∈ hubs, (leaves b).Nonempty ∧
      (∀ v ∉ leaves b, ∀ w ∈ leaves b, graph.Adj v w →
        ∃ u ∈ leaves b, u ≠ w ∧ graph.Adj v u) ∧
      (∀ w ∈ leaves b, ∀ v, graph.Adj w v → v=b) := by decide
  obtain ⟨w,hw,seed⟩ := hits_fort graph (leaves b) S (pair _ hb).1 (pair _ hb).2.1 h.1
  obtain ⟨v,hv,e⟩ := h.2 w seed
  exact (pair _ hb).2.2 _ hw _ e ▸ hv

private def startSet := univ.filter (fun v : V => v.val < 14 ∨ v.val%2=0)

private theorem total_witness : Total graph startSet := by
  have one : step graph startSet = univ := by
    simp only [step,neighborFinset_eq_filter]
    decide
  have fixed : step graph univ = univ := by simp [step]
  constructor
  · change (step graph)^[25+1] startSet = _
    rw [iterate_succ_apply,one,iterate_fixed fixed]
  · change ∀ v ∈ startSet, ∃ w ∈ startSet, graph.Adj v w
    decide

theorem total_exact : totalNumber graph = 20 := by
  let sizes := {k | ∃ S : Finset V, S.card=k ∧ Total graph S}
  have cardS : startSet.card=20 := by decide
  have witness : 20 ∈ sizes := ⟨_,cardS,total_witness⟩
  obtain ⟨S,cost,h⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨_,witness⟩)
  change S.card = totalNumber graph at cost
  have cover : ∀ v w : V, graph.Adj v w → w ∉ hubs → v ∈ hubs := by decide
  have lower := cover_forcing_bound graph hubs S (mandatory_hubs S h) cover h.1
  have hb : hubs.card = 6 := by decide
  rw [Fintype.card_fin,hb,cost] at lower
  exact le_antisymm (Nat.sInf_le (s := sizes) witness) (by omega)

/-- GraphCalc permits exactly one of the three colors, or 0 (uncolored).
An uncolored vertex sees all three colors. -/
def Rainbow {U : Type*} (G : SimpleGraph U) (f : U → Fin 4) : Prop :=
  ∀ v, f v = 0 → ∀ c : Fin 4, c ≠ 0 → ∃ w, G.Adj v w ∧ f w = c
def weight {U : Type*} [Fintype U] (f : U → Fin 4) : ℕ := (univ.filter (fun v => f v ≠ 0)).card
noncomputable def rainbowNumber {U : Type*} [Fintype U] (G : SimpleGraph U) :=
  sInf {k | ∃ f : U → Fin 4, weight f = k ∧ Rainbow G f}

private def palette (v : V) : Fin 4 :=
  if v.val < 4 then (if v.val%2=0 then 1 else 2) else
  if v.val < 6 then 3 else if v.val < 14 then 0 else 1

private def first (i : Fin 18) : V :=
  if i.val < 6 then ⟨i.val,by omega⟩ else ⟨i.val+8,by omega⟩
private def second (i : Fin 18) : V :=
  if i.val < 6 then
    match i.val with
    | 0 => 6 | 1 => 7 | 2 => 12 | 3 => 13 | 4 => 8 | _ => 10
  else first i

private theorem rainbow_lower (f : V → Fin 4) (rain : Rainbow graph f) : 18 ≤ weight f := by
  let colored := univ.filter (fun v => f v ≠ 0)
  have allcolors (v : V) (hv : f v = 0) (c : Fin 4) (hc : c ≠ 0) :
      c ∈ (graph.neighborFinset v).image f := by
    obtain ⟨w,e,hw⟩ := rain v hv c hc
    exact mem_image.mpr ⟨w,(graph.mem_neighborFinset v w).mpr e,hw⟩
  have three (v : V) (hv : f v=0) : 3 ≤ graph.degree v := by
    have sub : (univ.erase (0 : Fin 4)) ⊆ (graph.neighborFinset v).image f :=
      fun c hc => allcolors v hv c (ne_of_mem_erase hc)
    exact (show 3 = (univ.erase (0 : Fin 4)).card by decide) ▸
      ((card_le_card sub).trans card_image_le)
  have four (v w : V) (hv : f v=0) (hw : f w=0) (e : graph.Adj v w) : 4 ≤ graph.degree v := by
    have all : (graph.neighborFinset v).image f = univ := by
      apply eq_univ_of_forall
      intro c
      by_cases hc : c=0
      · exact mem_image.mpr ⟨w,(graph.mem_neighborFinset v w).mpr e,hw.trans hc.symm⟩
      · exact allcolors v hv c hc
    have h := card_image_le (s := graph.neighborFinset v) (f := f)
    simpa [all] using h
  have structure' : ∀ i : Fin 18,
      ((univ.filter (graph.Adj (first i))).card < 3) ∨
      (graph.Adj (second i) (first i) ∧ (univ.filter (graph.Adj (second i))).card < 4) := by decide
  have hits (i : Fin 18) : f (first i) ≠ 0 ∨ f (second i) ≠ 0 := by
    by_contra! miss
    rcases structure' i with small | ⟨e,small⟩
    · have h := three _ miss.1
      rw [SimpleGraph.degree,neighborFinset_eq_filter] at h
      exact (Nat.not_lt_of_ge h) small
    · have h := four _ _ miss.2 miss.1 e
      rw [SimpleGraph.degree,neighborFinset_eq_filter] at h
      exact (Nat.not_lt_of_ge h) small
  let pick (i : Fin 18) := if f (first i) ≠ 0 then first i else second i
  have sep : ∀ i j : Fin 18, i ≠ j →
      first i ≠ first j ∧ first i ≠ second j ∧ second i ≠ first j ∧ second i ≠ second j := by decide
  have inj : Function.Injective pick := by
    intro i j e
    by_cases eq : i = j
    · exact eq
    exfalso
    obtain ⟨ll,lr,rl,rr⟩ := sep i j eq
    dsimp [pick] at e
    split at e <;> split at e <;> contradiction
  have covered : univ.map ⟨pick,inj⟩ ⊆ colored := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := mem_map.mp hu
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change f (if f (first i) ≠ 0 then first i else second i) ≠ 0
    split
    · assumption
    · exact (hits i).resolve_left (by assumption)
  simpa [colored,weight] using card_le_card covered

theorem rainbow_exact : rainbowNumber graph = 18 := by
  let sizes := {k | ∃ f : V → Fin 4, weight f=k ∧ Rainbow graph f}
  have valid : Rainbow graph palette := by unfold Rainbow; decide
  have wit : 18 ∈ sizes := ⟨palette,by decide, valid⟩
  obtain ⟨f,cost,hr⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨18,wit⟩)
  change weight f = rainbowNumber graph at cost
  exact le_antisymm (Nat.sInf_le (s := sizes) wit) (by rw [← cost]; exact rainbow_lower f hr)
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

private def grid (v : V) : ℤ × ℤ :=
  ![(295,104),(1,1),(559,397),(756,145),(596,264),(880,61),
    (422,320),(421,339),(619,276),(362,160),(203,75),(959,3),(783,156),(760,122),
    (236,121),(265,145),(375,379),(403,362),(504,418),(523,437),(622,183),
    (639,195),(583,222),(564,197),(905,18),(880,44)] v

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


theorem counterexample_line357 : 2 ≤ Fintype.card V ∧ Planar graph ∧
    totalNumber graph = 20 ∧ rainbowNumber graph = 18 ∧ ¬totalNumber graph ≤ rainbowNumber graph :=
  ⟨by decide,⟨witnessDrawing⟩,total_exact,rainbow_exact,by rw [total_exact,rainbow_exact]; decide⟩

theorem line357_false : ¬∀ (U : Type) [Fintype U] [DecidableEq U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Planar G → totalNumber G ≤ rainbowNumber G := by
  intro all
  exact counterexample_line357.2.2.2.2 (all V graph (by decide) ⟨witnessDrawing⟩)

#print axioms total_exact
#print axioms rainbow_exact
#print axioms witnessDrawing
#print axioms line357_false
end AutoGraphForge357

