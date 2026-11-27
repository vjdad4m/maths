import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! A line graph refuting AutoGraphForge physical row 895, ID 32e0aa97.
Definitions and the distance certificate are reused from the row 33 and
shared-hub developments. The module has no local imports. -/

namespace LineBouquet

open SimpleGraph Finset

def Burns {U : Type*} (G : SimpleGraph U) (k : ℕ) : Prop :=
  ∃ source : Fin k → U, ∀ v, ∃ t : Fin k, ∃ p : G.Walk (source t) v,
    p.length ≤ k - 1 - t.val

noncomputable def burning {U : Type*} (G : SimpleGraph U) : ℕ := sInf {k | Burns G k}

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

/-- The Euler criterion used by NetworkX for the undirected connected case. -/
def Eulerian {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ ∀ u, G.degree u % 2 = 0


/-- The induced-claw predicate from the checked row 371 proof. -/
def ClawFree {U : Type*} (G : SimpleGraph U) := ∀ v a b c : U,
  G.Adj v a → G.Adj v b → G.Adj v c → a ≠ b → a ≠ c → b ≠ c →
  G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

abbrev V := Fin 14

/-- Edges 0–3 of the four-cycle, followed by the ten edges in cyclic order
around the ten-cycle. Vertex 0 is the only common original vertex. -/
def endpoints (x : V) : ℕ × ℕ :=
  match x.val with
  | 0 => (0,2)
  | 1 => (1,2)
  | 2 => (0,3)
  | 3 => (1,3)
  | 4 => (0,4)
  | 13 => (12,0)
  | i => (i-1,i)

/-- Adjacency in the line graph is intersection of two distinct edges. -/
def meet (x y : V) : Bool :=
  let a := endpoints x
  let b := endpoints y
  x != y && (a.1 == b.1 || a.1 == b.2 || a.2 == b.1 || a.2 == b.2)

def graph : SimpleGraph V where
  Adj x y := meet x y = true
  symm := by
    have h : ∀ x y, meet x y = true → meet y x = true := by decide
    exact fun x y => h x y
  loopless := by
    have h : ∀ x, meet x x ≠ true := by decide
    exact h

instance : DecidableRel graph.Adj := fun x y => inferInstanceAs (Decidable (meet x y = true))

/-- Distance from a small-cycle edge to the nearer of the two ten-cycle
edges incident with the shared vertex. -/
def entry (x : V) : ℕ := if x = 0 ∨ x = 2 then 1 else 2

/-- Distance within the ten-cycle from edge y to the nearer entry edge. -/
def toEntry (y : V) : ℕ := min (y.val - 4) (13 - y.val)

def d (x y : V) : ℕ :=
  if x = y then 0
  else if x.val < 4 then
    if y.val < 4 then (if meet x y then 1 else 2) else entry x + toEntry y
  else if y.val < 4 then entry y + toEntry x
  else
    let gap := max x.val y.val - min x.val y.val
    min gap (10 - gap)

set_option maxRecDepth 10000
set_option maxHeartbeats 6000000

theorem metric : (∀ x y, graph.Reachable x y) ∧ ∀ x y, graph.dist x y = d x y :=
  metric_certificate d (by decide) (by decide) (by decide)

theorem eulerian : Eulerian graph := ⟨⟨metric.1⟩, by decide⟩

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

/-- Classify neighbors of a line-graph vertex by the endpoint where the
corresponding original edges meet. Each class is a clique. -/
def side (v x : V) : Bool :=
  (endpoints v).1 == (endpoints x).1 || (endpoints v).1 == (endpoints x).2

theorem claw_free : ClawFree graph := clawFree_of_two_cliques graph side (by decide)

theorem slater_exact : slater graph = 3 := by
  let L : List ℕ := List.replicate 4 4 ++ List.replicate 10 2
  have degreeList : degreesDesc graph = L := by
    unfold degreesDesc
    rw [Finset.val_univ_fin, Multiset.map_coe, Multiset.coe_sort]
    have degrees : (List.finRange 14).map (fun v => graph.degree v) =
        [4,2,4,2,4,2,2,2,2,2,2,2,2,4] := by decide
    rw [degrees]
    simp [List.mergeSort, L]
  unfold slater
  rw [degreeList, Fintype.card_fin]
  let costs : Set ℕ := {k | 14 ≤ k + (L.take k).sum}
  have good : 3 ∈ costs := by decide
  apply le_antisymm (Nat.sInf_le (s := costs) good)
  have attained := Nat.sInf_mem (show costs.Nonempty from ⟨3, good⟩)
  change 3 ≤ sInf costs
  by_contra! small
  have low : ∀ i : Fin 3, i.val ∉ costs := by decide
  exact low ⟨sInf costs, small⟩ attained

def cycleVertices : Finset V := univ.filter (fun x => 4 ≤ x.val)
def cycleBall (x : V) (r : ℕ) := cycleVertices.filter (fun y => d x y ≤ r)

/-- No radius-r ball covers more than 2r+1 of the ten cycle edges.
At radius at least five this follows from the cycle's order alone. -/
theorem ball_capacity (x : V) (r : ℕ) : (cycleBall x r).card ≤ 2*r + 1 := by
  by_cases small : r < 5
  · have check : ∀ v : V, ∀ i : Fin 5, (cycleBall v i.val).card ≤ 2*i.val + 1 := by decide
    exact check x ⟨r, small⟩
  · have bound := card_le_card (filter_subset (fun y => d x y ≤ r) cycleVertices)
    have size : cycleVertices.card = 10 := by decide
    change (cycleBall x r).card ≤ cycleVertices.card at bound
    omega

theorem burns_lower {k : ℕ} (h : Burns graph k) : 4 ≤ k := by
  by_contra! small
  obtain ⟨source, cover⟩ := h
  let rad (i : Fin k) := k - 1 - i.val
  let balls (i : Fin k) := cycleBall (source i) (rad i)
  have sub : cycleVertices ⊆ univ.biUnion balls := by
    intro w hw
    obtain ⟨i,p,hp⟩ := cover w
    refine mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨hw,?_⟩⟩
    exact (metric.2 _ _ ▸ dist_le p).trans hp
  have caps (i : Fin k) : (balls i).card ≤ 2*rad i + 1 :=
    ball_capacity (source i) (rad i)
  have size : cycleVertices.card = 10 := by decide
  have widths : ∀ n : Fin 4, (∑ i : Fin n.val, (2*(n.val-1-i.val)+1)) ≤ 9 := by decide
  have impossible : 10 ≤ 9 := calc
    10 = cycleVertices.card := size.symm
    _ ≤ (univ.biUnion balls).card := card_le_card sub
    _ ≤ ∑ i : Fin k, (balls i).card := card_biUnion_le
    _ ≤ ∑ i : Fin k, (2*rad i+1) := sum_le_sum (fun i _ => caps i)
    _ ≤ 9 := widths ⟨k, small⟩
  omega

theorem burns_four : Burns graph 4 := by
  let schedule (t : Fin 4) : V :=
    if t = 0 then 0 else if t = 1 then 5 else if t = 2 then 8 else 10
  have cover : ∀ w : V, ∃ t : Fin 4, d (schedule t) w ≤ 4-1-t.val := by decide
  refine ⟨schedule,fun w => ?_⟩
  obtain ⟨t,ht⟩ := cover w
  obtain ⟨p,hp⟩ := (metric.1 (schedule t) w).exists_walk_length_eq_dist
  exact ⟨t,p,by rw [hp,metric.2]; exact ht⟩

theorem burning_exact : burning graph = 4 := by
  have h : 4 ∈ {k | Burns graph k} := burns_four
  exact le_antisymm (Nat.sInf_le h) (burns_lower (Nat.sInf_mem ⟨4,h⟩))

theorem row895_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → ClawFree G → Eulerian G →
      2 * (burning G : ℚ) + (-4) ≤ (slater G : ℚ)) := by
  intro claim
  have h := claim V graph (by decide) claw_free eulerian
  rw [burning_exact, slater_exact] at h
  norm_num at h

#print axioms eulerian
#print axioms claw_free
#print axioms slater_exact
#print axioms ball_capacity
#print axioms burning_exact
#print axioms row895_false

end LineBouquet
