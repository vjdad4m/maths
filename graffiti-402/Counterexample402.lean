import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Lattice
import Lean.Elab.Tactic.Omega

/-!
# Written on the Wall II, conjecture 402

This formalizes the 11-vertex counterexample previously given by
Claude Opus 5 at AI Village (graffiti-verification README, section 7ba).
A triangle at the hub is joined to an independent five-set via three
vertices adjacent to the hub and to each of the five vertices.

The result has two-domination number 5 and total domination number 2.
Its minimum-degree vertices are adjacent to each other, and no vertex
has exactly one maximum-degree neighbor. The claimed upper bound is 4.
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti402
open Finset SimpleGraph

section Definitions
variable {V : Type*} (G : SimpleGraph V)

def TotalDominates (D : Finset V) : Prop := ∀ v, ∃ u ∈ D, G.Adj v u

def TwoDominates (D : Finset V) : Prop :=
  ∀ v, v ∈ D ∨ ∃ x y, x ∈ D ∧ y ∈ D ∧ x ≠ y ∧ G.Adj v x ∧ G.Adj v y

noncomputable def totalDominationNumber : ℕ :=
  sInf {n : ℕ | ∃ D, TotalDominates G D ∧ (D : Finset V).card = n}

noncomputable def twoDominationNumber : ℕ :=
  sInf {n : ℕ | ∃ D, TwoDominates G D ∧ (D : Finset V).card = n}

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

def minimumDegreeVertices : Finset V :=
  univ.filter fun v => ∀ w, G.degree v ≤ G.degree w

def maximumDegreeVertices : Finset V :=
  univ.filter fun v => ∀ w, G.degree w ≤ G.degree v

/-- An isolate of the induced minimum-degree graph has no neighbor
among the minimum-degree vertices. -/
def minimumDegreeIsolates : Finset V :=
  (minimumDegreeVertices G).filter fun v => ∀ w, w ∈ minimumDegreeVertices G → ¬G.Adj v w

def exactlyOneMaximumNeighbor : Finset V :=
  univ.filter fun v => (G.neighborFinset v ∩ maximumDegreeVertices G).card = 1
end Definitions

abbrev Vertex := Fin 11

def side (v : Vertex) : Prop := 8 ≤ v.val

def base (v : Vertex) : Prop := v.val ≤ 5

def adj (v w : Vertex) : Prop :=
  (side v ∧ base w) ∨ (side w ∧ base v) ∨
    ((v = 0 ∨ v = 6 ∨ v = 7) ∧ (w = 0 ∨ w = 6 ∨ w = 7) ∧ v ≠ w)

instance (v : Vertex) : Decidable (side v) := by unfold side; infer_instance
instance (v : Vertex) : Decidable (base v) := by unfold base; infer_instance
instance (v w : Vertex) : Decidable (adj v w) := by unfold adj; infer_instance

def witness : SimpleGraph Vertex where
  Adj := adj
  symm := by
    intro v w h
    rcases h with h | h | ⟨hv,hw,hne⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hw,hv,hne.symm⟩)
  loopless := by change ∀ v : Vertex, ¬adj v v; decide

instance : DecidableRel witness.Adj := fun v w => inferInstanceAs (Decidable (adj v w))

private theorem joins : ∀ v : Vertex, v = 0 ∨ witness.Adj 0 v ∨ witness.Adj 8 v := by decide

theorem witness_connected : witness.Connected := by
  apply (connected_iff_exists_forall_reachable witness).mpr
  refine ⟨0,fun v => ?_⟩
  rcases joins v with rfl | h | h
  · exact Reachable.rfl
  · exact h.reachable
  · exact (show witness.Adj 0 8 by decide).reachable.trans h.reachable

theorem no_isolates : minimumDegreeIsolates witness = ∅ := by decide
theorem no_unique_max_neighbor : exactlyOneMaximumNeighbor witness = ∅ := by decide

private instance (D : Finset Vertex) : Decidable (TotalDominates witness D) := by
  unfold TotalDominates
  infer_instance

private instance (D : Finset Vertex) : Decidable (TwoDominates witness D) := by
  unfold TwoDominates
  infer_instance

theorem total_eq : totalDominationNumber witness = 2 := by
  have h : TotalDominates witness {0,8} := by decide
  have hcard : ({0,8} : Finset Vertex).card = 2 := by decide
  apply le_antisymm (Nat.sInf_le (show 2 ∈ {n : ℕ | ∃ D, TotalDominates witness D ∧ D.card = n} from ⟨{0,8},h,hcard⟩))
  have hn : {n : ℕ | ∃ D, TotalDominates witness D ∧ (D : Finset Vertex).card = n}.Nonempty :=
    ⟨2,_,h,hcard⟩
  obtain ⟨D,hD,hDcard⟩ := Nat.sInf_mem hn
  change 2 ≤ sInf _
  rw [← hDcard]
  obtain ⟨x,hx,_⟩ := hD 0
  obtain ⟨y,hy,hxy⟩ := hD x
  exact one_lt_card.mpr ⟨x,hx,y,hy,hxy.ne⟩

private def five : Finset Vertex := {0,6,8,9,10}

private def A : Finset Vertex := {8,9,10}
private def B : Finset Vertex := {1,2,3,4,5}
private def C : Finset Vertex := {0,6,7}

private theorem B_only_A : ∀ v ∈ B, ∀ w, witness.Adj v w → w ∈ A := by decide
private theorem triangle_only_C : ∀ v : Vertex, v = 6 ∨ v = 7 →
    ∀ w, witness.Adj v w → w ∈ C := by decide
private theorem A_only_hub_of_union : ∀ v ∈ A, ∀ w ∈ A ∪ C,
    witness.Adj v w → w = 0 := by decide

private theorem intersect_lower (D Z : Finset Vertex) {x y : Vertex}
    (hxD : x ∈ D) (hyD : y ∈ D) (hxZ : x ∈ Z) (hyZ : y ∈ Z) (hne : x ≠ y) :
    2 ≤ (D ∩ Z).card := by
  have h := card_le_card (show {x,y} ⊆ D ∩ Z from
    insert_subset (mem_inter.mpr ⟨hxD,hxZ⟩)
      (singleton_subset_iff.mpr (mem_inter.mpr ⟨hyD,hyZ⟩)))
  rwa [card_pair hne] at h

private theorem no_small (D : Finset Vertex) (hD : TwoDominates witness D) : 5 ≤ D.card := by
  by_contra hn
  have hA : 2 ≤ (D ∩ A).card := by
    by_contra hlt
    have hsub : B ⊆ D := by
      intro v hv
      rcases hD v with had | ⟨x,y,hx,hy,hne,hvx,hvy⟩
      · exact had
      · exact (hlt (intersect_lower D A hx hy (B_only_A v hv x hvx)
          (B_only_A v hv y hvy) hne)).elim
    have hc : B.card = 5 := by decide
    have hle := card_le_card hsub
    omega
  have hC : 2 ≤ (D ∩ C).card := by
    by_cases h6 : (6 : Vertex) ∈ D
    · by_cases h7 : (7 : Vertex) ∈ D
      · exact intersect_lower D C h6 h7 (by decide) (by decide) (by decide)
      · obtain ⟨x,y,hx,hy,hne,hvx,hvy⟩ := (hD 7).resolve_left h7
        exact intersect_lower D C hx hy (triangle_only_C 7 (Or.inr rfl) x hvx)
          (triangle_only_C 7 (Or.inr rfl) y hvy) hne
    · obtain ⟨x,y,hx,hy,hne,hvx,hvy⟩ := (hD 6).resolve_left h6
      exact intersect_lower D C hx hy (triangle_only_C 6 (Or.inl rfl) x hvx)
        (triangle_only_C 6 (Or.inl rfl) y hvy) hne
  have hdis : Disjoint (D ∩ A) (D ∩ C) := by
    have hd : Disjoint A C := by decide
    exact disjoint_left.mpr fun x h₁ h₂ => (disjoint_left.mp hd) (mem_inter.mp h₁).2 (mem_inter.mp h₂).2
  let R := (D ∩ A) ∪ (D ∩ C)
  have hR : R.card = (D ∩ A).card + (D ∩ C).card := card_union_of_disjoint hdis
  have hsub : R ⊆ D := union_subset inter_subset_left inter_subset_left
  have htotal := card_le_card hsub
  have heq : R = D := eq_of_subset_of_card_le hsub (by omega)
  have hDA (x : Vertex) (hx : x ∈ D) : x ∈ A ∪ C := by
    rw [← heq] at hx
    rcases mem_union.mp hx with h | h
    · exact mem_union_left _ (mem_inter.mp h).2
    · exact mem_union_right _ (mem_inter.mp h).2
  have hmiss : ∃ a ∈ A, a ∉ D := by
    by_contra hnone
    have hh : A ⊆ D := by
      intro a ha
      by_cases hm : a ∈ D
      · exact hm
      · exact (hnone ⟨a,ha,hm⟩).elim
    have hc : A.card = 3 := by decide
    have hp := card_le_card (show A ⊆ D ∩ A from fun a ha => mem_inter.mpr ⟨hh ha,ha⟩)
    omega
  obtain ⟨a,ha,hnD⟩ := hmiss
  obtain ⟨x,y,hx,hy,hne,hvx,hvy⟩ := (hD a).resolve_left hnD
  exact hne ((A_only_hub_of_union a ha x (hDA x hx) hvx).trans
    (A_only_hub_of_union a ha y (hDA y hy) hvy).symm)

theorem two_eq : twoDominationNumber witness = 5 := by
  have h : TwoDominates witness five := by decide
  have hc : five.card = 5 := by decide
  apply le_antisymm (Nat.sInf_le (show 5 ∈ {n : ℕ | ∃ D, TwoDominates witness D ∧ D.card = n} from ⟨five,h,hc⟩))
  have hn : {n : ℕ | ∃ D, TwoDominates witness D ∧ (D : Finset Vertex).card = n}.Nonempty :=
    ⟨5,_,h,hc⟩
  obtain ⟨D,hD,hDcard⟩ := Nat.sInf_mem hn
  change 5 ≤ sInf _
  rw [← hDcard]
  exact no_small D hD

theorem counterexample402 : witness.Connected ∧ 2 < Fintype.card Vertex ∧
    2 * ((minimumDegreeIsolates witness).card + (exactlyOneMaximumNeighbor witness).card +
      totalDominationNumber witness) < twoDominationNumber witness := by
  refine ⟨witness_connected,by decide,?_⟩
  rw [no_isolates,no_unique_max_neighbor,total_eq,two_eq]
  decide

#print axioms counterexample402

end Graffiti402
