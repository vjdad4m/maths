import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Lattice
import Lean.Elab.Tactic.Omega

namespace EulerianChainRecovered
open SimpleGraph Finset
set_option maxHeartbeats 5000000
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

abbrev V := Fin 13

/-- Five consecutive odd cliques; consecutive cliques share their common endpoint. -/
def edge (x y : V) : Prop := x ≠ y ∧
  (x.val ≤ 2 ∧ y.val ≤ 2 ∨
   2 ≤ x.val ∧ x.val ≤ 4 ∧ 2 ≤ y.val ∧ y.val ≤ 4 ∨
   4 ≤ x.val ∧ x.val ≤ 8 ∧ 4 ≤ y.val ∧ y.val ≤ 8 ∨
   8 ≤ x.val ∧ x.val ≤ 10 ∧ 8 ≤ y.val ∧ y.val ≤ 10 ∨
   10 ≤ x.val ∧ 10 ≤ y.val)

instance (x y : V) : Decidable (edge x y) := by unfold edge; infer_instance

def graph : SimpleGraph V where
  Adj := edge
  symm := by change ∀ x y, edge x y → edge y x; decide
  loopless := by change ∀ x, ¬edge x x; decide

instance (x y : V) : Decidable (graph.Adj x y) := inferInstanceAs (Decidable (edge x y))

theorem chordal : Chordal graph := chordal_of_elimination graph Fin.val (by decide)

noncomputable def degreesDesc {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)

noncomputable def slater {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  sInf {t | Fintype.card U ≤ t + ((degreesDesc G).take t).sum}

theorem slater_exact : slater graph = 2 := by
  let L : List ℕ := [6,6,4,4,4,4,4,2,2,2,2,2,2]
  have degreeList : degreesDesc graph = L := by
    unfold degreesDesc
    rw [Finset.val_univ_fin,Multiset.map_coe,Multiset.coe_sort]
    have eq : (List.finRange 13).map (fun v => graph.degree v) = [2,2,4,2,6,4,4,4,6,2,4,2,2] := by decide
    rw [eq]
    simp [List.mergeSort,L]
  unfold slater
  rw [degreeList,Fintype.card_fin]
  let costs : Set ℕ := {k | 13 ≤ k + (L.take k).sum}
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

private def table : List (List ℕ) := [
  [0,1,1,2,2,3,3,3,3,4,4,5,5],
  [1,0,1,2,2,3,3,3,3,4,4,5,5],
  [1,1,0,1,1,2,2,2,2,3,3,4,4],
  [2,2,1,0,1,2,2,2,2,3,3,4,4],
  [2,2,1,1,0,1,1,1,1,2,2,3,3],
  [3,3,2,2,1,0,1,1,1,2,2,3,3],
  [3,3,2,2,1,1,0,1,1,2,2,3,3],
  [3,3,2,2,1,1,1,0,1,2,2,3,3],
  [3,3,2,2,1,1,1,1,0,1,1,2,2],
  [4,4,3,3,2,2,2,2,1,0,1,2,2],
  [4,4,3,3,2,2,2,2,1,1,0,1,1],
  [5,5,4,4,3,3,3,3,2,2,1,0,1],
  [5,5,4,4,3,3,3,3,2,2,1,1,0]]

private def distanceTable (u v : V) := ((table[u.val]?).getD [])[v.val]?.getD 0

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
theorem radius_exact : radius graph = 3 := by
  have eq : eccentricity graph = ecc := funext eccentricity_eq
  unfold radius
  rw [eq]
  have hit : 3 ∈ Set.range ecc := ⟨6,by decide⟩
  have lower : ∀ x : V, 3 ≤ ecc x := by decide
  obtain ⟨x,hx⟩ := Nat.sInf_mem (show (Set.range ecc).Nonempty from ⟨_,hit⟩)
  exact le_antisymm (Nat.sInf_le hit) ((lower x).trans_eq hx)

/-- Connected and every vertex has even degree, the Euler criterion used by the source. -/
def Eulerian {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ ∀ u, G.degree u % 2 = 0

theorem eulerian : Eulerian graph := ⟨connected, by decide⟩

/-- Maximum distance sum for a triple of distinct vertices. -/
noncomputable def triameter {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U) : ℕ :=
  univ.sup fun a => (univ.erase a).sup fun b => ((univ.erase a).erase b).sup fun c =>
    G.dist a b + G.dist b c + G.dist c a

private def tableTriameter : ℕ := (univ : Finset V).sup fun a =>
  (univ.erase a).sup fun b => ((univ.erase a).erase b).sup fun c =>
    distanceTable a b + distanceTable b c + distanceTable c a

theorem triameter_exact : triameter graph = 11 := by
  have tab : graph.dist = distanceTable := funext fun x => funext (metric.2 x)
  unfold triameter
  rw [tab]
  change tableTriameter = 11
  decide

theorem row501_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Chordal G → Eulerian G → radius G ≤ slater G) := by
  intro h
  have contra := h V graph (by decide) chordal eulerian
  rw [radius_exact,slater_exact] at contra
  omega

theorem row764_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Chordal G → Eulerian G → triameter G ≤ 4 * slater G + 2) := by
  intro h
  have contra := h V graph (by decide) chordal eulerian
  rw [triameter_exact,slater_exact] at contra
  omega

#print axioms connected
#print axioms chordal
#print axioms eulerian
#print axioms slater_exact
#print axioms radius_exact
#print axioms triameter_exact
#print axioms row501_false
#print axioms row764_false
end EulerianChainRecovered
