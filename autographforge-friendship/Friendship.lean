import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Path
import Mathlib.Topology.Algebra.Ring.Real

/-! The row 373 definitions below implement GraphCalc's PSD rule. The final
theorems refute the pinned AutoGraphForge rows on a friendship graph.
For the published PSD formula see Hogben, Lin and Shader, Theorem 9.44(11)
(doi:10.1090/surv/270). -/
namespace AutoGraphForge373
open SimpleGraph Finset
open Classical
noncomputable section
variable {V : Type*} (G : SimpleGraph V)

/-- Same predicate as upstream IsCographClass and published line 378. -/
def Cograph := ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d →
  ¬G.Adj a c → ¬G.Adj b d → G.Adj a d

/-- Two vertices in the same component of the induced white graph. -/
def WhiteConnected (B : Set V) (a b : V) : Prop :=
  ∃ (ha : a ∉ B) (hb : b ∉ B),
    (G.induce Bᶜ).Reachable ⟨a, ha⟩ ⟨b, hb⟩

def step (B : Set V) : Set V := {w | w ∈ B ∨ w ∉ B ∧ ∃ v ∈ B, G.Adj v w ∧
  ∀ u, G.Adj v u → WhiteConnected G B w u → u = w}

def round (S : Finset V) : ℕ → Set V
  | 0 => ↑S
  | n+1 => step G (round S n)

def PSDSet (S : Finset V) : Prop := ∃ n, ∀ v, v ∈ round G S n

def psd : ℕ := sInf {n | ∃ S : Finset V, n = S.card ∧ PSDSet G S}

end
end AutoGraphForge373

namespace AutoGraphForgeFriendship
open Finset SimpleGraph AutoGraphForge373
open scoped BigOperators unitInterval
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 2048

abbrev Vertex (n : ℕ) := Option (Fin n × Bool)
abbrev leaf {n : ℕ} (i : Fin n) (b : Bool) : Vertex n := some (i,b)

def edges {n : ℕ} : Vertex n → Vertex n → Prop
  | none, none => False
  | none, some _ | some _, none => True
  | some (i,b), some (j,c) => i = j ∧ b ≠ c

instance {n} (x y : Vertex n) : Decidable (edges x y) := by
  cases x <;> cases y <;> unfold edges <;> infer_instance

def fan (n : ℕ) : SimpleGraph (Vertex n) where
  Adj := edges
  symm := by
    rintro (_|⟨i,b⟩) (_|⟨j,c⟩) h <;> try exact h
    exact ⟨h.1.symm,h.2.symm⟩
  loopless := by rintro (_|⟨i,b⟩) h; exact h; exact h.2 rfl

instance (n : ℕ) : DecidableRel (fan n).Adj := fun x y => inferInstanceAs (Decidable (edges x y))

variable {n : ℕ}

private theorem neighbors (i : Fin n) (b : Bool) (x : Vertex n) :
    (fan n).Adj (leaf i b) x ↔ x = none ∨ x = leaf i (!b) := by
  rcases x with _ | ⟨j,c⟩
  · simp [fan,edges]
  · cases b <;> cases c <;> simp [fan,edges,eq_comm]

private theorem mate_edge (i : Fin n) (b : Bool) : (fan n).Adj (leaf i b) (leaf i (!b)) :=
  (neighbors i b _).mpr (Or.inr rfl)

private theorem white_edge {G : SimpleGraph (Vertex n)} {B : Set (Vertex n)} {a b}
    (ha : a ∉ B) (hb : b ∉ B) (ab : G.Adj a b) : WhiteConnected G B a b :=
  ⟨ha,hb,(show (G.induce Bᶜ).Adj ⟨a,ha⟩ ⟨b,hb⟩ from ab).reachable⟩

/-- A pair of unseeded peripheral vertices stays white forever. -/
private theorem meets_petal {S : Finset (Vertex n)} (full : PSDSet (fan n) S) (i : Fin n) :
    ∃ b, leaf i b ∈ S := by
  classical
  by_contra! missed
  have never (k : ℕ) : ∀ b, leaf i b ∉ round (fan n) S k := by
    induction k with
    | zero => exact missed
    | succ k ih =>
      intro b hb
      rcases hb with old | ⟨_,v,black,adj,only⟩
      · exact ih b old
      · rcases (neighbors i b v).mp adj.symm with rfl | rfl
        · have eq := only (leaf i (!b)) (show (fan n).Adj none (leaf i (!b)) from True.intro)
            (white_edge (ih b) (ih (!b)) (mate_edge i b))
          exact (mate_edge i b).ne' eq
        · exact ih (!b) black
  obtain ⟨k,all⟩ := full
  exact never k false (all _)

private def chosen (pick : Fin n → Bool) : Finset (Vertex n) :=
  univ.map ⟨fun i => leaf i (pick i),fun _ _ h => congrArg Prod.fst (Option.some.inj h)⟩

@[simp] private theorem chosen_card (p : Fin n → Bool) : (chosen p).card = n := by simp [chosen]

@[simp] private theorem hub_not_chosen (p : Fin n → Bool) : none ∉ chosen p := by simp [chosen]

@[simp] private theorem chosen_iff (p : Fin n → Bool) (i : Fin n) (b : Bool) :
    leaf i b ∈ chosen p ↔ p i = b := by simp [chosen]

/-- With just one seed per petal, every black vertex sees the hub and its mate
in the same white component. -/
private theorem stalled (p : Fin n → Bool) :
    step (fan n) (↑(chosen p)) = (↑(chosen p) : Set (Vertex n)) := by
  ext w
  constructor
  · rintro (old | ⟨_,v,vb,vw,unique⟩)
    · exact old
    · rcases v with _ | ⟨i,b⟩
      · exact (hub_not_chosen p vb).elim
      · have col := (chosen_iff p i b).mp vb
        have mw : leaf i (!b) ∉ chosen p := by
          rw [chosen_iff,col]
          cases b <;> decide
        have hw := hub_not_chosen p
        have hm : (fan n).Adj none (leaf i (!b)) := True.intro
        rcases (neighbors i b w).mp vw with rfl | rfl
        · exact hm.ne' (unique _ (mate_edge i b) (white_edge hw mw hm)) |>.elim
        · exact hm.ne (unique _ (show (fan n).Adj (leaf i b) none from True.intro)
            (white_edge mw hw hm.symm)) |>.elim
  · exact fun h => Or.inl h

theorem friendship_psd (n : ℕ) : psd (fan n) = n+1 := by
  classical
  let p : Fin n → Bool := fun _ => false
  let A := insert none (chosen p)
  have count : A.card = n+1 := by simp [A]
  have feasible : PSDSet (fan n) A := by
    refine ⟨1,?_⟩
    rintro (_|⟨i,b⟩)
    · exact Or.inl (mem_insert_self _ _)
    · by_cases h : leaf i b ∈ A
      · exact Or.inl h
      · have hb : b = true := by
          cases b
          · exact (h (mem_insert_of_mem ((chosen_iff p i false).mpr rfl))).elim
          · rfl
        subst b
        refine Or.inr ⟨h,leaf i false,mem_insert_of_mem ((chosen_iff p i false).mpr rfl),
          mate_edge i false,?_⟩
        rintro u e ⟨_,uw,_⟩
        rcases (neighbors i false u).mp e with rfl | rfl
        · exact (uw (mem_insert_self _ _)).elim
        · rfl
  let sizes := {k | ∃ S : Finset (Vertex n), k=S.card ∧ PSDSet (fan n) S}
  have hit : n+1 ∈ sizes := ⟨A,count.symm,feasible⟩
  obtain ⟨S,cost,full⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨_,hit⟩)
  apply Nat.le_antisymm (Nat.sInf_le (s := sizes) hit)
  rw [cost]
  apply Nat.le_of_not_gt
  intro small
  choose pick seeds using meets_petal full
  have sub : chosen pick ⊆ S := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_map.mp hx
    exact seeds i
  have le : S.card ≤ (chosen pick).card := by rw [chosen_card]; omega
  have same := eq_of_subset_of_card_le sub le
  obtain ⟨k,all⟩ := full
  have stays (t : ℕ) : round (fan n) S t = (↑(chosen pick) : Set (Vertex n)) := by
    induction t with
    | zero => rw [← same]; rfl
    | succ t ih => exact (congrArg (step (fan n)) ih).trans (stalled pick)
  have hub := all none
  rw [stays k] at hub
  exact hub_not_chosen pick hub

abbrev V := Vertex 7
abbrev graph := fan 7

def Eulerian {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ ∀ v, Even (G.degree v)

def meanDegree {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : ℚ :=
  ((∑ v, G.degree v : ℕ) : ℚ) / Fintype.card U

/-- Consecutive indices of a simple cycle in either direction, including its closing edge. -/
def consecutive {k : ℕ} (i j : Fin k) : Prop :=
  i.val+1 = j.val ∨ j.val+1 = i.val ∨
    (i.val=0 ∧ j.val+1=k) ∨ (j.val=0 ∧ i.val+1=k)

/-- The usual forbidden-induced-cycle definition of a chordal graph. -/
def Chordal {U : Type*} (G : SimpleGraph U) : Prop :=
  ∀ k, 4 ≤ k → ¬∃ f : Fin k ↪ U, ∀ i j, G.Adj (f i) (f j) ↔ consecutive i j

theorem friendship_connected (n : ℕ) : (fan n).Connected := by
  have hub (v : Vertex n) : (fan n).Reachable v none := by
    cases v with
    | none => exact .refl _
    | some x => exact (show (fan n).Adj (some x) none from True.intro).reachable
  exact ⟨fun v w => (hub v).trans (hub w).symm⟩

theorem friendship_cograph (n : ℕ) : Cograph (fan n) := by
  intro a b c d ab bc cd ac bd
  rcases b with _ | ⟨i,t⟩
  · rcases d with _ | d
    · exact ab
    · exact (bd True.intro).elim
  rcases (neighbors i t c).mp bc with rfl | rfl
  · rcases a with _ | a
    · exact cd
    · exact (ac True.intro).elim
  · rcases (neighbors i t a).mp ab.symm with rfl | rfl
    · exact (ac True.intro).elim
    · exact cd

theorem connected : graph.Connected := friendship_connected 7
theorem cograph : Cograph graph := friendship_cograph 7

theorem chordal : Chordal graph := by
  have shortcut : ∀ a b : V, graph.Adj a b → ∀ c : V, graph.Adj b c → a ≠ c →
      ∀ d : V, graph.Adj c d → b ≠ d → graph.Adj a c ∨ graph.Adj b d := by decide
  rintro k hk ⟨f,adj⟩
  let a : Fin k := ⟨0,by omega⟩
  let b : Fin k := ⟨1,by omega⟩
  let c : Fin k := ⟨2,by omega⟩
  let d : Fin k := ⟨3,by omega⟩
  have ac : a ≠ c := fun h => by have := congrArg Fin.val h; simp [a,c] at this
  have bd : b ≠ d := fun h => by have := congrArg Fin.val h; simp [b,d] at this
  rcases shortcut _ _ ((adj a b).mpr (Or.inl rfl)) _ ((adj b c).mpr (Or.inl rfl))
      (fun h => ac (f.injective h)) _ ((adj c d).mpr (Or.inl rfl)) (fun h => bd (f.injective h))
      with h | h
  · have x := (adj a c).mp h
    simp [consecutive,a,c] at x
    omega
  · have x := (adj b d).mp h
    simp [consecutive,b,d] at x

theorem degree_values : ∀ v : V, graph.degree v = if v = none then 14 else 2 := by decide

theorem eulerian : Eulerian graph := by
  refine ⟨connected,fun v => ?_⟩
  rw [degree_values]
  split <;> decide

theorem minimum_degree : graph.minDegree = 2 := by
  refine Nat.le_antisymm ((graph.minDegree_le_degree (leaf 0 false)).trans ?_)
    (graph.le_minDegree_of_forall_le_degree 2 ?_)
  · decide
  · intro v
    rw [degree_values]
    split <;> decide

theorem edge_count : graph.edgeFinset.card = 21 := by decide
theorem mean_degree : meanDegree graph = 14/5 := by
  have degrees : (∑ v, graph.degree v) = 42 := by decide
  unfold meanDegree
  rw [degrees,show Fintype.card V = 15 by decide]
  norm_num
theorem order_bound : 2 ≤ Fintype.card V := by decide

theorem k4free : graph.CliqueFree 4 := by
  rw [cliqueFree_iff]
  refine ⟨fun f => ?_⟩
  have no : ∀ a b : V, graph.Adj a b → ∀ c : V, graph.Adj a c → graph.Adj b c →
      ∀ d : V, graph.Adj a d → graph.Adj b d → ¬graph.Adj c d := by decide
  exact no (f 0) (f 1) (f.map_adj_iff.mpr (show (⊤ : SimpleGraph (Fin 4)).Adj 0 1 by decide))
    (f 2) (f.map_adj_iff.mpr (show (⊤ : SimpleGraph (Fin 4)).Adj 0 2 by decide))
    (f.map_adj_iff.mpr (show (⊤ : SimpleGraph (Fin 4)).Adj 1 2 by decide))
    (f 3) (f.map_adj_iff.mpr (show (⊤ : SimpleGraph (Fin 4)).Adj 0 3 by decide))
    (f.map_adj_iff.mpr (show (⊤ : SimpleGraph (Fin 4)).Adj 1 3 by decide))
    (f.map_adj_iff.mpr (show (⊤ : SimpleGraph (Fin 4)).Adj 2 3 by decide))

theorem clique_number : graph.cliqueNum = 3 := by
  have lower : graph.IsNClique 3 {none,leaf 0 false,leaf 0 true} := by decide
  have lo := lower.1.card_le_cliqueNum
  rw [lower.2] at lo
  obtain ⟨_,large⟩ := graph.exists_isNClique_cliqueNum
  by_contra bad
  have upper := k4free.mono (show 4 ≤ graph.cliqueNum by omega)
  exact upper _ large

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
  let j : ℤ := match v with
    | none => 0
    | some (i,b) => 1 + 2 * (i.val : ℤ) + (if b then 1 else 0)
  (j,j*j)

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

/-- The singleton palette, weight and optimum used in the 357 and 1080 proofs. -/
def Rainbow {U : Type*} (G : SimpleGraph U) (f : U → Fin 4) : Prop :=
  ∀ v, f v = 0 → ∀ c : Fin 4, c ≠ 0 → ∃ w, G.Adj v w ∧ f w = c
def weight {U : Type*} [Fintype U] (f : U → Fin 4) : ℕ := (univ.filter (fun v => f v ≠ 0)).card
noncomputable def rainbowNumber {U : Type*} [Fintype U] (G : SimpleGraph U) :=
  sInf {k | ∃ f : U → Fin 4, weight f = k ∧ Rainbow G f}

/-- GraphCalc colors the complement. Each color class is a clique of G. -/
def CliquePartition {U : Type*} (G : SimpleGraph U) (k : ℕ) : Prop :=
  ∃ f : U → Fin k, ∀ a b, f a = f b → a ≠ b → G.Adj a b

noncomputable def vertexCliqueCover {U : Type*} (G : SimpleGraph U) : ℕ :=
  sInf {k | CliquePartition G k}

theorem cliquePartition_iff_complement_colorable {U : Type*} (G : SimpleGraph U) (k : ℕ) :
    CliquePartition G k ↔ Nonempty (Gᶜ →g (⊤ : SimpleGraph (Fin k))) := by
  constructor
  · rintro ⟨f,h⟩
    exact ⟨⟨f,fun {a b} e eq =>
      ((G.compl_adj a b).mp e).2 (h a b eq ((G.compl_adj a b).mp e).1)⟩⟩
  · rintro ⟨f⟩
    refine ⟨f,fun a b eq ne => ?_⟩
    by_contra missing
    exact f.map_rel ((G.compl_adj a b).mpr ⟨ne,missing⟩) eq

theorem friendship_clique_cover (hn : 1 ≤ n) : vertexCliqueCover (fan n) = n := by
  let f : Vertex n → Fin n := fun v => v.elim ⟨0,by omega⟩ Prod.fst
  have feasible : CliquePartition (fan n) n := by
    refine ⟨f,?_⟩
    rintro (_|⟨i,b⟩) (_|⟨j,c⟩) eq ne
    · exact (ne rfl).elim
    · trivial
    · trivial
    · change i = j at eq
      subst j
      exact ⟨rfl, fun h => ne (by rw [h])⟩
  apply Nat.le_antisymm (Nat.sInf_le (s := {k | CliquePartition (fan n) k}) feasible)
  obtain ⟨color,proper⟩ := Nat.sInf_mem (s := {k | CliquePartition (fan n) k}) ⟨_,feasible⟩
  have inj : Function.Injective (fun i : Fin n => color (leaf i false)) := by
    intro i j same
    by_contra ne
    have adj := proper _ _ same (fun h => ne (congrArg Prod.fst (Option.some.inj h)))
    exact adj.2 rfl
  simpa [vertexCliqueCover] using Fintype.card_le_of_injective _ inj

private def petals (n : ℕ) : Finset (Vertex n) :=
  univ.map ⟨some,Option.some_injective _⟩

@[simp] private theorem petals_card (n : ℕ) : (petals n).card = 2*n := by
  simp [petals,Nat.mul_comm]

private def paint : Vertex n → Fin 4
  | none => 0
  | some (i,b) => if i.val=0 then (if b then 1 else 2) else 3

private theorem paint_leaf (i : Fin n) (b : Bool) : paint (leaf i b) ≠ 0 := by
  cases b <;> simp [paint] <;> split <;> decide

private theorem painted_weight : weight (paint (n := n)) = 2*n := by
  have same : univ.filter (fun v : Vertex n => paint v ≠ 0) = petals n := by
    ext v
    rcases v with _ | ⟨i,b⟩
    · simp [petals,paint]
    · simp [petals,paint_leaf]
  rw [weight,same,petals_card]

private theorem paint_valid (hn : 2 ≤ n) : Rainbow (fan n) paint := by
  rintro (_|⟨i,b⟩) blank c pos
  · let i : Fin n := ⟨0,by omega⟩
    let j : Fin n := ⟨1,by omega⟩
    have cases' : c=1 ∨ c=2 ∨ c=3 := by omega
    rcases cases' with rfl | rfl | rfl
    · exact ⟨leaf i true,True.intro,rfl⟩
    · exact ⟨leaf i false,True.intro,rfl⟩
    · exact ⟨leaf j true,True.intro,rfl⟩
  · exact (paint_leaf i b blank).elim

theorem friendship_rainbow (hn : 2 ≤ n) : rainbowNumber (fan n) = 2*n := by
  classical
  let costs := {k | ∃ f : Vertex n → Fin 4, weight f = k ∧ Rainbow (fan n) f}
  have good : 2*n ∈ costs := ⟨paint,painted_weight,paint_valid hn⟩
  apply Nat.le_antisymm (Nat.sInf_le (s := costs) good)
  obtain ⟨f,eq,valid⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨_,good⟩)
  have leaves (i : Fin n) (b : Bool) : f (leaf i b) ≠ 0 := by
    intro blank
    have seen (c : Fin 4) (pos : c ≠ 0) : f none = c ∨ f (leaf i (!b)) = c := by
      obtain ⟨w,adj,col⟩ := valid _ blank c pos
      rcases (neighbors i b w).mp adj with rfl | rfl
      · exact Or.inl col
      · exact Or.inr col
    rcases seen 1 (by decide) with h|h <;>
      rcases seen 2 (by decide) with g|g <;>
      rcases seen 3 (by decide) with s|s <;> omega
  have sub : petals n ⊆ univ.filter (fun v => f v ≠ 0) := by
    intro v hv
    obtain ⟨⟨i,b⟩,_,rfl⟩ := mem_map.mp hv
    exact mem_filter.mpr ⟨mem_univ _,leaves i b⟩
  rw [← eq,← petals_card]
  exact card_le_card sub

theorem row2595_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U),
    2 ≤ Fintype.card U → Cograph G → G.Connected →
    (vertexCliqueCover G : ℚ) ≤ (2/5 : ℚ)*rainbowNumber G+39/5) := by
  intro claim
  have h := claim (Vertex 40) (fan 40) (by simp) (friendship_cograph _) (friendship_connected _)
  rw [friendship_clique_cover (by decide),friendship_rainbow (by decide)] at h
  norm_num at h

theorem row2602_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U),
    2 ≤ Fintype.card U → Cograph G →
    (vertexCliqueCover G : ℚ) ≤ (5/11 : ℚ)*rainbowNumber G+84/11) := by
  intro claim
  have h := claim (Vertex 85) (fan 85) (by simp) (friendship_cograph _)
  rw [friendship_clique_cover (by decide),friendship_rainbow (by decide)] at h
  norm_num at h

#print axioms friendship_clique_cover
#print axioms friendship_rainbow
#print axioms row2595_false
#print axioms row2602_false

theorem witness_psd : psd graph = 8 := friendship_psd 7

theorem row2054_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → G.Connected → Planar G → psd G ≤ G.minDegree + 4) := by
  intro claim
  have h := claim V graph order_bound connected ⟨witnessDrawing⟩
  rw [witness_psd,minimum_degree] at h
  omega

theorem row2290_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → G.Connected → (psd G : ℚ) ≤ (1/4 : ℚ) * G.edgeFinset.card + 9/4) := by
  intro claim
  have h := claim V graph order_bound connected
  rw [witness_psd,edge_count] at h
  norm_num at h

theorem row2304_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U),
    2 ≤ Fintype.card U → G.Connected → Planar G → psd G ≤ G.cliqueNum + 4) := by
  intro claim
  have h := claim V graph order_bound connected ⟨witnessDrawing⟩
  rw [witness_psd,clique_number] at h
  omega

theorem row2380_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → G.CliqueFree 4 → Eulerian G → psd G ≤ G.minDegree + 4) := by
  intro claim
  have h := claim V graph order_bound k4free eulerian
  rw [witness_psd,minimum_degree] at h
  omega

theorem row2405_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Eulerian G → Planar G → (psd G : ℚ) ≤ (1/2 : ℚ)*G.minDegree+5) := by
  intro claim
  have h := claim V graph order_bound eulerian ⟨witnessDrawing⟩
  rw [witness_psd,minimum_degree] at h
  norm_num at h

theorem row2537_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U),
    2 ≤ Fintype.card U → Chordal G → G.Connected → psd G ≤ G.cliqueNum + 3) := by
  intro claim
  have h := claim V graph order_bound chordal connected
  rw [witness_psd,clique_number] at h
  omega

theorem row2590_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Chordal G → G.Connected → (psd G : ℚ) ≤ (11/8 : ℚ)*meanDegree G+9/4) := by
  intro claim
  have h := claim V graph order_bound chordal connected
  rw [witness_psd,mean_degree] at h
  norm_num at h

theorem row2600_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Cograph G → Eulerian G → (psd G : ℚ) ≤ (11/18 : ℚ)*meanDegree G+49/9) := by
  intro claim
  have h := claim V graph order_bound cograph eulerian
  rw [witness_psd,mean_degree] at h
  norm_num at h

#print axioms friendship_psd
#print axioms witnessDrawing
#print axioms row2054_false
#print axioms row2290_false
#print axioms row2304_false
#print axioms row2380_false
#print axioms row2405_false
#print axioms row2537_false
#print axioms row2590_false
#print axioms row2600_false

end AutoGraphForgeFriendship
