import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Equality examples on Mathlib's canonical pathGraph 10 and cycleGraph 17.
The definitions of burning and Slater number are the published #33 ones.
The shortest-walk certificate is from the shared-hub and #501/#764 proofs. -/
namespace PathCycleSharpness
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


set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

def ClawFree {U : Type*} (G : SimpleGraph U) := ∀ v a b c : U,
  G.Adj v a → G.Adj v b → G.Adj v c → a ≠ b → a ≠ c → b ≠ c →
  G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

def Eulerian {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  G.Connected ∧ ∀ u, G.degree u % 2 = 0

def Subcubic {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] :=
  ∀ v, G.degree v ≤ 3

def ball {U : Type*} [Fintype U] (d : U → U → ℕ) (x : U) (r : ℕ) :=
  univ.filter (fun v => d x v ≤ r)

/-- A concrete covering schedule and upper bounds on ball sizes certify both
sides of the burning number. The lower bound applies to every shorter schedule. -/
theorem burning_certificate {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U)
    (d : U → U → ℕ) (metric : (∀ x y, G.Reachable x y) ∧ ∀ x y, G.dist x y = d x y)
    (k : ℕ) (schedule : Fin k → U)
    (cover : ∀ v, ∃ i, d (schedule i) v ≤ k-1-i.val)
    (capacity : ∀ x, ∀ r : Fin k, (ball d x r.val).card ≤ 2*r.val+1)
    (tooSmall : ∀ t : Fin k, (∑ i : Fin t.val, (2*(t.val-1-i.val)+1)) < Fintype.card U) :
    burning G = k := by
  have upper : Burns G k := by
    refine ⟨schedule,fun v => ?_⟩
    obtain ⟨i,hi⟩ := cover v
    obtain ⟨p,hp⟩ := (metric.1 _ _).exists_walk_length_eq_dist
    exact ⟨i,p,by rw [hp,metric.2]; exact hi⟩
  have attained := Nat.sInf_mem (show {j | Burns G j}.Nonempty from ⟨k,upper⟩)
  change Burns G (burning G) at attained
  apply le_antisymm (Nat.sInf_le (s := {j | Burns G j}) upper)
  by_contra! small
  change burning G < k at small
  let t := burning G
  obtain ⟨source,covers⟩ := attained
  let balls (i : Fin t) := ball d (source i) (t-1-i.val)
  have sub : univ ⊆ univ.biUnion balls := by
    intro v _
    obtain ⟨i,p,hp⟩ := covers v
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,
      (metric.2 _ _ ▸ dist_le p).trans hp⟩⟩
  have caps (i : Fin t) : (balls i).card ≤ 2*(t-1-i.val)+1 :=
    capacity _ ⟨_,by dsimp [t]; omega⟩
  have count := (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum (fun i _ => caps i)))
  have impossible := tooSmall ⟨t,small⟩
  rw [card_univ] at count
  exact (Nat.not_le_of_gt impossible) count

theorem slater_certificate {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj]
    (l : List ℕ) (seq : degreesDesc G = l) (k : ℕ)
    (good : Fintype.card U ≤ k + (l.take k).sum)
    (small : ∀ t : Fin k, t.val + (l.take t.val).sum < Fintype.card U) : slater G = k := by
  unfold slater
  rw [seq]
  let costs : Set ℕ := {t | Fintype.card U ≤ t + (l.take t).sum}
  apply le_antisymm (Nat.sInf_le (s := costs) good)
  by_contra! low
  exact (Nat.not_le_of_gt (small ⟨_,low⟩)) (Nat.sInf_mem (show costs.Nonempty from ⟨k,good⟩))

def lineDistance {n : ℕ} (x y : Fin n) := max x.val y.val - min x.val y.val

end PathCycleSharpness
