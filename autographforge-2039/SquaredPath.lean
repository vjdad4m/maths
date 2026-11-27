import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Lattice
import Mathlib.Combinatorics.SimpleGraph.Clique
import Lean.Elab.Tactic.Omega

/-! A finite connected counterexample to AutoGraphForge physical row 2039. -/
namespace SquaredPath2039
open SimpleGraph Finset

noncomputable def degreesDesc {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)

noncomputable def slater {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  sInf {t | Fintype.card U ≤ t + ((degreesDesc G).take t).sum}

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

noncomputable def eccentricity {U : Type*} [Fintype U] (G : SimpleGraph U) (u : U) := univ.sup (G.dist u)
noncomputable def diameter {U : Type*} [Fintype U] (G : SimpleGraph U) := univ.sup (eccentricity G)

/-- AutoGraphForge's separate diameter wrapper represents an undefined value by infinity. -/
noncomputable def sourceDiameter {U : Type*} [Fintype U] (G : SimpleGraph U) : WithTop ℚ := by
  classical
  exact if G.Connected then ((diameter G : ℚ) : WithTop ℚ) else ⊤

/-- The induced-claw predicate from the checked row 371 proof. -/
def ClawFree {U : Type*} (G : SimpleGraph U) := ∀ v a b c : U,
  G.Adj v a → G.Adj v b → G.Adj v c → a ≠ b → a ≠ c → b ≠ c →
  G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

/-- If each neighborhood can be partitioned into two cliques, three distinct
neighbors of a vertex cannot be pairwise nonadjacent. -/
theorem clawFree_of_two_cliques {U : Type*} (G : SimpleGraph U) (side : U → U → Bool)
    (clique : ∀ v x y, G.Adj v x → G.Adj v y → x ≠ y →
      side v x = side v y → G.Adj x y) : ClawFree G := by
  intro v a b c ha hb hc hab hac hbc
  have pigeonhole : ∀ i j k : Bool, i = j ∨ i = k ∨ j = k := by decide
  rcases pigeonhole (side v a) (side v b) (side v c) with h | h | h
  · exact Or.inl (clique v a b ha hb hab h)
  · exact Or.inr (Or.inl (clique v a c ha hc hac h))
  · exact Or.inr (Or.inr (clique v b c hb hc hbc h))

abbrev V := Fin 10
def gap (a b : ℕ) := max a b - min a b

/-- The path 0,...,9, with an extra edge between each pair at separation two
inside the initial segment 0,...,5. -/
def linked (x y : V) := gap x.val y.val = 1 ∨
  (max x.val y.val ≤ 5 ∧ gap x.val y.val = 2)

def graph : SimpleGraph V where
  Adj := linked
  symm x y h := by simpa only [linked,gap,max_comm y.val x.val,min_comm y.val x.val] using h
  loopless x := by simp [linked,gap]

instance : DecidableRel graph.Adj := fun x y => inferInstanceAs
  (Decidable (gap x.val y.val = 1 ∨ (max x.val y.val ≤ 5 ∧ gap x.val y.val = 2)))

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- A shortest path traverses the squared segment two edges of the original
path at a time, and traverses the tail one edge at a time. -/
def distance (x y : V) := (gap (min x.val 5) (min y.val 5) + 1) / 2 +
  gap (x.val - 5) (y.val - 5)

theorem metric : (∀ x y, graph.Reachable x y) ∧ ∀ x y, graph.dist x y = distance x y :=
  metric_certificate distance (by decide) (by decide) (by decide)

theorem connected : graph.Connected := ⟨metric.1⟩

/-- Neighbors to the left of a vertex form a clique, as do neighbors to its right. -/
theorem claw_free : ClawFree graph :=
  clawFree_of_two_cliques graph (fun v x => decide (x < v)) (by decide)

def color (x : V) : Fin 3 := ⟨x.val % 3,Nat.mod_lt _ (by decide)⟩

/-- Every edge has label difference one or two, so residues modulo three
properly color the vertices. Four mutually adjacent vertices cannot occur. -/
theorem k4_free : graph.CliqueFree 4 := by
  have proper : ∀ x y, graph.Adj x y → color x ≠ color y := by decide
  by_contra no
  obtain ⟨f⟩ := (not_cliqueFree_iff 4).mp no
  have inj : Function.Injective (fun i : Fin 4 => color (f i)) := by
    intro i j eq
    by_contra ne
    exact proper _ _ (f.map_adj_iff.mpr ((top_adj i j).mpr ne)) eq
  have count := Fintype.card_le_of_injective _ inj
  simp at count

theorem slater_exact : slater graph = 2 := by
  let L := [4,4,3,3,3,2,2,2,2,1]
  have sorted : degreesDesc graph = L := by
    unfold degreesDesc
    rw [Finset.val_univ_fin, Multiset.map_coe, Multiset.coe_sort]
    have degrees : (List.finRange 10).map (fun v => graph.degree v) =
        [2,3,4,4,3,3,2,2,2,1] := by decide
    rw [degrees]
    simp [List.mergeSort,L]
  unfold slater
  rw [sorted,Fintype.card_fin]
  let costs : Set ℕ := {k | 10 ≤ k + (L.take k).sum}
  have good : 2 ∈ costs := by decide
  apply le_antisymm (Nat.sInf_le (s := costs) good)
  have attained := Nat.sInf_mem (show costs.Nonempty from ⟨2,good⟩)
  change 2 ≤ sInf costs
  by_contra! small
  have below : ∀ k : Fin 2, k.val ∉ costs := by decide
  exact below ⟨_,small⟩ attained

theorem diameter_exact : diameter graph = 7 := by
  have eq : graph.dist = distance := funext (fun x => funext (metric.2 x))
  unfold diameter eccentricity
  rw [eq]
  decide

theorem row2039_connected_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U)
    [DecidableRel G.Adj], 2 ≤ Fintype.card U → G.CliqueFree 4 → ClawFree G → G.Connected →
    (diameter G : ℚ) ≤ (43/15 : ℚ)*slater G + 4/15) := by
  intro claim
  have bound := claim V graph (by decide) k4_free claw_free connected
  rw [diameter_exact,slater_exact] at bound
  norm_num at bound

theorem row2039_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U)
    [DecidableRel G.Adj], 2 ≤ Fintype.card U → G.CliqueFree 4 → ClawFree G →
    sourceDiameter G ≤ (((43/15 : ℚ)*slater G + 4/15 : ℚ) : WithTop ℚ)) := by
  intro claim
  apply row2039_connected_false
  intro U _ G _ hn hk hf hc
  simpa only [sourceDiameter,if_pos hc,WithTop.coe_le_coe] using claim U G hn hk hf

#print axioms connected
#print axioms k4_free
#print axioms claw_free
#print axioms slater_exact
#print axioms diameter_exact
#print axioms row2039_connected_false
#print axioms row2039_false

end SquaredPath2039
