import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Written on the Wall II #439.
The graph is the order-21 witness of Claude Opus 5 (AI Village), commit a600543.
Siddhant Dubey's earlier dossier reports an order-19 witness.
-/

namespace Graffiti439

open Finset SimpleGraph
open scoped BigOperators

section Invariants

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A dissociation set has at most one neighbor within the set at every selected vertex. -/
def IsDissociation (D : Finset V) : Prop :=
  ∀ v ∈ D, ((G.neighborFinset v) ∩ D).card ≤ 1

instance (D : Finset V) : Decidable (IsDissociation G D) := by
  unfold IsDissociation
  infer_instance

private theorem degree_induce_eq (D : Finset V) (v : (D : Set V)) :
    (G.induce (D : Set V)).degree v = ((G.neighborFinset v.val) ∩ D).card := by
  have he :
      ((G.induce (D : Set V)).neighborFinset v).map (Function.Embedding.subtype _) =
        G.neighborFinset v.val ∩ D := by
    ext w
    simp only [mem_map, SimpleGraph.mem_neighborFinset, mem_inter]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu,u.property⟩
    · rintro ⟨hw,hm⟩
      exact ⟨⟨w,hm⟩,hw,rfl⟩
  rw [← he, card_map]
  rfl

/-- Formula for the 2-independence condition in catalogue definition 118. -/
theorem isDissociation_iff (D : Finset V) :
    IsDissociation G D ↔ (G.induce (D : Set V)).maxDegree ≤ 1 := by
  constructor
  · intro h
    apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro v
    rw [degree_induce_eq]
    exact h v.val v.property
  · intro h v hv
    rw [← degree_induce_eq G D ⟨v,hv⟩]
    exact ((G.induce (D : Set V)).degree_le_maxDegree ⟨v,hv⟩).trans h

def dissociationNumber : ℕ :=
  (univ.powerset.filter (IsDissociation G)).sup Finset.card

theorem le_dissociationNumber (D : Finset V) (hD : IsDissociation G D) :
    D.card ≤ dissociationNumber G :=
  Finset.le_sup (f := Finset.card)
    (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ D),hD⟩)

theorem dissociationNumber_le (k : ℕ)
    (h : ∀ D, IsDissociation G D → D.card ≤ k) : dissociationNumber G ≤ k :=
  Finset.sup_le fun _ hD => h _ (mem_filter.mp hD).2

def maxDegreeVertices : Finset V := univ.filter (fun v => G.degree v = G.maxDegree)

/-- The union of the open neighborhoods of vertices in M, as in definition 46. -/
def openNeighborhood (M : Finset V) : Finset V :=
  univ.filter (fun v => ∃ w ∈ M, G.Adj v w)

/-- The exact Caro–Wei sum of definition 121. -/
def caroWei : ℚ := ∑ v : V, 1 / ((G.degree v : ℚ) + 1)

def catalogueRhs : ℤ :=
  ((openNeighborhood G (maxDegreeVertices G)).card : ℤ) +
    Int.floor (2 * (caroWei G - 1))

end Invariants

abbrev Vertex := Fin 21

/-- The first twelve vertices subdivide the cube edges, the next eight
are the cube's original vertices, and vertex 20 is a pendant at 12.
Consecutive pairs of subdividing vertices form the added perfect matching. -/
private def edges : Finset (Vertex × Vertex) :=
  {(0,12),(0,13),(1,16),(1,17),(2,12),(2,16),
   (3,13),(3,14),(4,17),(4,18),(5,13),(5,17),
   (6,14),(6,15),(7,18),(7,19),(8,14),(8,18),
   (9,15),(9,12),(10,19),(10,16),(11,15),(11,19),
   (0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(20,12)}

private def witnessAdj (u v : Vertex) : Prop := (u,v) ∈ edges ∨ (v,u) ∈ edges

instance (u v : Vertex) : Decidable (witnessAdj u v) := by
  unfold witnessAdj
  infer_instance

def witness : SimpleGraph Vertex where
  Adj := witnessAdj
  symm := by intro _ _ h; exact h.symm
  loopless := by
    change ∀ u : Vertex, ¬ witnessAdj u u
    decide

instance : DecidableRel witness.Adj := fun u v =>
  inferInstanceAs (Decidable (witnessAdj u v))

private def parent : Vertex → Vertex := ![0,0,12,13,5,13,15,6,9,12,16,15,0,0,3,9,1,1,8,10,12]
private def depth : Vertex → ℕ := ![0,1,2,2,3,2,4,5,3,2,3,4,1,1,3,3,2,2,4,4,2]

private theorem parent_adj : ∀ v : Vertex, v ≠ 0 → witness.Adj (parent v) v := by decide

private theorem parent_depth : ∀ v : Vertex, v ≠ 0 → depth (parent v) < depth v := by
  decide

theorem witness_connected : witness.Connected := by
  have reach : ∀ n, ∀ v, depth v = n → witness.Reachable 0 v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hr : v = 0
      · subst v
        exact Reachable.refl _
      · exact (ih (depth (parent v)) (hv ▸ parent_depth v hr) (parent v) rfl).trans
          (parent_adj v hr).reachable
  exact (connected_iff_exists_forall_reachable witness).mpr ⟨0,fun v => reach _ v rfl⟩

private def degreeProfile (v : Vertex) : ℕ := if v = 12 then 4 else if v = 20 then 1 else 3

theorem degree_values : ∀ v, witness.degree v = degreeProfile v := by decide

theorem maxDegree_eq : witness.maxDegree = 4 := by
  apply le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    simp only [degree_values]
    decide
  · calc
      4 = witness.degree 12 := by decide
      _ ≤ witness.maxDegree := witness.degree_le_maxDegree _

theorem maxDegreeVertices_eq : maxDegreeVertices witness = {12} := by
  ext v
  simp only [maxDegreeVertices, mem_filter, mem_univ, true_and, mem_singleton,
    maxDegree_eq, degree_values]
  exact (by decide : ∀ v : Vertex, degreeProfile v = 4 ↔ v = 12) v

theorem neighborhood_eq : openNeighborhood witness (maxDegreeVertices witness) = {0,2,9,20} := by
  rw [maxDegreeVertices_eq]
  decide

theorem caroWei_eq : caroWei witness = 109 / 20 := by
  have hterm (v : Vertex) :
      (1 : ℚ) / ((witness.degree v : ℚ) + 1) =
        1 / 4 + (if v = 12 then 1 / 5 - 1 / 4 else 0) +
          (if v = 20 then 1 / 2 - 1 / 4 else 0) := by
    rw [degree_values]
    have h12 : (12 : Vertex) ≠ 20 := by decide
    have h20 := Ne.symm h12
    by_cases hw : v = 12 <;> by_cases hp : v = 20
    · exact (h12 (hw.symm.trans hp)).elim
    all_goals norm_num [degreeProfile, hw, hp, h12, h20]
  simp_rw [caroWei, hterm, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num [nsmul_eq_mul]

theorem floor_eq : Int.floor (2 * (caroWei witness - 1)) = 8 := by
  rw [caroWei_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num

theorem rhs_eq : catalogueRhs witness = 12 := by
  rw [catalogueRhs, neighborhood_eq, floor_eq]
  decide

private def dissociationWitness : Finset Vertex := univ.filter (fun v => v.val < 12 ∨ v = 20)

theorem dissociationWitness_ok : IsDissociation witness dissociationWitness := by decide

/-- Counting edges crossing from A to B by their endpoint in either set. -/
private theorem crossing_sum_comm (A B : Finset Vertex) :
    (∑ v ∈ A, (B.filter (witness.Adj v)).card) =
      ∑ w ∈ B, (A.filter (witness.Adj w)).card := by
  have hcard (S : Finset Vertex) (v : Vertex) :
      (S.filter (witness.Adj v)).card = ∑ w ∈ S, if witness.Adj v w then 1 else 0 :=
    (Finset.sum_boole (α := ℕ) (witness.Adj v) S).symm
  simp_rw [hcard]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  exact Finset.sum_congr rfl fun v _ => by simp only [witness.adj_comm v w]

private theorem crossing_lower (D : Finset Vertex) (hD : IsDissociation witness D)
    {v : Vertex} (hv : v ∈ D) (hp : v ≠ 20) :
    2 ≤ (Dᶜ.filter (witness.Adj v)).card := by
  have he : Dᶜ.filter (witness.Adj v) = (witness.neighborFinset v) \ D := by
    ext w
    simp [and_comm]
  rw [he]
  have hin := hD v hv
  have ht := Finset.card_inter_add_card_sdiff (witness.neighborFinset v) D
  change ((witness.neighborFinset v) ∩ D).card +
    ((witness.neighborFinset v) \ D).card = witness.degree v at ht
  have hd : 3 ≤ witness.degree v := by
    rw [degree_values]
    unfold degreeProfile
    split <;> simp_all
  omega

private theorem crossing_upper (A : Finset Vertex) (v : Vertex) :
    (A.filter (witness.Adj v)).card ≤ 3 + (if v = 12 then 1 else 0) := by
  calc
    (A.filter (witness.Adj v)).card ≤ (witness.neighborFinset v).card :=
      Finset.card_le_card fun _ h => by
        exact (witness.mem_neighborFinset _ _).mpr (mem_filter.mp h).2
    _ = witness.degree v := rfl
    _ ≤ _ := by
      rw [degree_values]
      unfold degreeProfile
      split
      · decide
      · split <;> decide

private theorem dissociation_upper (D : Finset Vertex) (hD : IsDissociation witness D) :
    D.card ≤ 13 := by
  let A := D.erase 20
  let B := Dᶜ
  have hlow : A.card * 2 ≤ ∑ v ∈ A, (B.filter (witness.Adj v)).card := by
    rw [← Nat.nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro v hv
    exact crossing_lower D hD (mem_erase.mp hv).2 (mem_erase.mp hv).1
  have hhigh : (∑ v ∈ B, (A.filter (witness.Adj v)).card) ≤ B.card * 3 + 1 := by
    calc
      _ ≤ ∑ v ∈ B, (3 + (if v = 12 then 1 else 0)) :=
        Finset.sum_le_sum fun v _ => crossing_upper A v
      _ = B.card * 3 + (if 12 ∈ B then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, Finset.sum_ite_eq']
      _ ≤ B.card * 3 + 1 := by split <;> omega
  have hA : D.card ≤ A.card + 1 := by
    by_cases hp : (20 : Vertex) ∈ D
    · have hh := Finset.card_erase_add_one hp
      exact hh.ge
    · simp [A, erase_eq_of_not_mem hp]
  have hB : B.card + D.card = 21 := by
    exact Finset.card_compl_add_card D
  rw [crossing_sum_comm] at hlow
  omega

theorem dissociationNumber_eq : dissociationNumber witness = 13 := by
  apply le_antisymm
  · exact dissociationNumber_le witness 13 dissociation_upper
  · have hh : dissociationWitness.card = 13 := by decide
    rw [← hh]
    exact le_dissociationNumber witness dissociationWitness dissociationWitness_ok

theorem counterexample439 :
    witness.Connected ∧ 3 < Fintype.card Vertex ∧
      catalogueRhs witness < (dissociationNumber witness : ℤ) := by
  refine ⟨witness_connected,by decide,?_⟩
  rw [rhs_eq, dissociationNumber_eq]
  decide

theorem conjecture439_false :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 3 < Fintype.card V →
        (dissociationNumber G : ℤ) ≤ catalogueRhs G := by
  intro h
  exact (not_le_of_gt counterexample439.2.2) (h Vertex witness witness_connected (by decide))

#print axioms isDissociation_iff
#print axioms witness_connected
#print axioms maxDegreeVertices_eq
#print axioms neighborhood_eq
#print axioms caroWei_eq
#print axioms floor_eq
#print axioms dissociationNumber_eq
#print axioms conjecture439_false

end Graffiti439
