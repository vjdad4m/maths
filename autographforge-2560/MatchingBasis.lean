import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.SimpleGraph.Finite
/-! Matching existence and extension from the published row 371 proof, and
regular balanced bicliques from row 1883. The sources are pinned in README.md. -/
namespace Graffiti326
open Finset SimpleGraph
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel G.Adj

def HasMatching (G : SimpleGraph V) (k : ℕ) :=
  ∃ f : Fin k × Bool ↪ V, ∀ i, G.Adj (f (i,false)) (f (i,true))

local instance (G : SimpleGraph V) : DecidablePred (HasMatching G) := Classical.decPred _

private def feasibleMatchingSizes (G : SimpleGraph V) : Finset ℕ :=
  (range (Fintype.card V / 2+1)).filter (HasMatching G)

private theorem matchingSizes_nonempty (G : SimpleGraph V) :
    (feasibleMatchingSizes G).Nonempty := by
  use 0
  simp only [feasibleMatchingSizes, mem_filter, mem_range]
  refine ⟨by omega, ⟨⟨fun p => Fin.elim0 p.1, ?_⟩, ?_⟩⟩
  · intro p; exact Fin.elim0 p.1
  · intro i; exact Fin.elim0 i

def matchingNumber (G : SimpleGraph V) : ℕ :=
  (feasibleMatchingSizes G).max' (matchingSizes_nonempty G)

theorem matchingNumber_attained (G : SimpleGraph V) : HasMatching G (matchingNumber G) := by
  exact (Finset.mem_filter.1 (Finset.max'_mem (feasibleMatchingSizes G)
    (matchingSizes_nonempty G))).2

theorem matchingNumber_upper {G : SimpleGraph V} {k : ℕ} (hk : HasMatching G k) :
    k ≤ matchingNumber G := by
  obtain ⟨f,hf⟩ := hk
  have hk' : 2*k ≤ Fintype.card V := by
    simpa [Nat.mul_comm] using Fintype.card_le_of_injective f f.injective
  apply Finset.le_max'
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ⟨f,hf⟩⟩

def support {k : ℕ} (f : Fin k × Bool ↪ V) : Finset V :=
  univ.map f

omit [Fintype V] in
theorem mem_support {k : ℕ} (f : Fin k × Bool ↪ V) {v : V} :
    v ∈ support f ↔ ∃ i b, f (i,b) = v := by
  simp [support, Prod.exists]

omit [Fintype V] in
theorem matching_extend_support {G : SimpleGraph V} {k : ℕ} {f : Fin k × Bool ↪ V}
    (hf : ∀ i, G.Adj (f (i,false)) (f (i,true))) {x y : V}
    (hx : x ∉ support f) (hy : y ∉ support f) (ha : G.Adj x y) :
    ∃ f' : Fin (k+1) × Bool ↪ V, (∀ i, G.Adj (f' (i,false)) (f' (i,true))) ∧
      support f' ⊆ insert x (insert y (support f)) := by
  let F (i : Fin (k+1)) (b : Bool) :=
    Fin.lastCases (motive := fun _ => V) (if b then y else x) (fun j => f (j,b)) i
  have hX (i : Fin k) (b : Bool) : f (i,b) ∈ support f := (mem_support f).mpr ⟨i,b,rfl⟩
  have hfin : Function.Injective (fun p : Fin (k+1) × Bool => F p.1 p.2) := by
    rintro ⟨i,b⟩ ⟨j,c⟩ he
    change F i b = F j c at he
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩ | rfl
    · simp only [F, Fin.lastCases_castSucc] at he
      obtain e := f.injective he
      cases e
      rfl
    · simp only [F, Fin.lastCases_castSucc, Fin.lastCases_last] at he
      cases c
      · change f (i,b) = x at he
        exact (hx (he ▸ hX i b)).elim
      · change f (i,b) = y at he
        exact (hy (he ▸ hX i b)).elim
    · simp only [F, Fin.lastCases_castSucc, Fin.lastCases_last] at he
      cases b
      · change x = f (j,c) at he
        exact (hx (he.symm ▸ hX j c)).elim
      · change y = f (j,c) at he
        exact (hy (he.symm ▸ hX j c)).elim
    · simp only [F, Fin.lastCases_last] at he
      cases b <;> cases c <;> simp_all [ha.ne,ha.ne.symm]
  let f' : Fin (k+1) × Bool ↪ V := ⟨fun p => F p.1 p.2,hfin⟩
  refine ⟨f', ?_, ?_⟩
  · intro i
    change G.Adj (F i false) (F i true)
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl
    · simpa [F] using hf i
    · simpa [F] using ha
  · intro z hz
    obtain ⟨i,b,rfl⟩ := (mem_support f').mp hz
    change F i b ∈ _
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl
    · simp only [F, Fin.lastCases_castSucc]
      exact mem_insert_of_mem (mem_insert_of_mem (hX i b))
    · cases b <;> simp [F]

omit [Fintype V] in
theorem matching_extend {G : SimpleGraph V} {k : ℕ} {f : Fin k × Bool ↪ V}
    (hf : ∀ i, G.Adj (f (i,false)) (f (i,true))) {x y : V}
    (hx : x ∉ support f) (hy : y ∉ support f) (ha : G.Adj x y) :
    HasMatching G (k+1) := by
  obtain ⟨f',hf',_⟩ := matching_extend_support hf hx hy ha
  exact ⟨f',hf'⟩

end
end Graffiti326

namespace AutoGraphForge1080
open Finset SimpleGraph
open Classical
noncomputable section
abbrev Vertex (n : ℕ) := Bool × Fin n

def biclique (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := x.1 ≠ y.1
  symm := fun _ _ h => h.symm
  loopless := fun _ => not_ne_iff.mpr rfl

end
end AutoGraphForge1080

namespace AutoGraphForge378
open SimpleGraph Graffiti326
variable {V : Type*} (G : SimpleGraph V)
def HasMaximalMatching (k : ℕ) : Prop :=
  ∃ f : Fin k × Bool ↪ V, (∀ i, G.Adj (f (i,false)) (f (i,true))) ∧
    ∀ u ∉ support f, ∀ v ∉ support f, ¬G.Adj u v
noncomputable def minMaximalMatching := sInf {k | HasMaximalMatching G k}
end AutoGraphForge378

namespace AutoGraphForge1883
open SimpleGraph Finset Graffiti326 AutoGraphForge378 AutoGraphForge1080
variable {n k : ℕ}
/-- An edge of Kₙ,ₙ is specified by its left and right indices. The closed
line-graph neighborhood of an edge consists of exactly its row and column. -/
def DominatesEdges (left right : Fin k → Fin n) : Prop :=
  ∀ a b, (∃ i, left i = a) ∨ (∃ i, right i = b)

private theorem edge_domination_lower {left right : Fin k → Fin n}
    (covers : DominatesEdges left right) : n ≤ k := by
  classical
  have surj : Function.Surjective left ∨ Function.Surjective right := by
    by_cases h : Function.Surjective left
    · exact Or.inl h
    · obtain ⟨a,ha⟩ : ∃ a, ¬∃ i, left i = a := by simpa [Function.Surjective] using h
      exact Or.inr (fun b => (covers a b).resolve_left ha)
  rcases surj with h | h <;> simpa using Fintype.card_le_of_surjective _ h

/-- Every maximal matching saturates both parts. -/
theorem maximal_size {k : ℕ} (M : HasMaximalMatching (biclique n) k) : k = n := by
  classical
  obtain ⟨f,edges,maximal⟩ := M
  let index (b : Bool) (i : Fin k) : Fin n :=
    if (f (i,false)).1 = b then (f (i,false)).2 else (f (i,true)).2
  have covered {b : Bool} {a : Fin n} (h : (b,a) ∈ support f) : ∃ i, index b i = a := by
    obtain ⟨i,t,eq⟩ := (mem_support f).mp h
    refine ⟨i,?_⟩
    cases t with
    | false =>
      have side : (f (i,false)).1 = b := congrArg Prod.fst eq
      simpa only [index,if_pos side] using (show (f (i,false)).2 = a from congrArg Prod.snd eq)
    | true =>
      have side : (f (i,false)).1 ≠ b := fun bad => (edges i) (bad.trans (congrArg Prod.fst eq).symm)
      simpa only [index,if_neg side] using (show (f (i,true)).2 = a from congrArg Prod.snd eq)
  have dom : DominatesEdges (index false) (index true) := by
    intro a b
    by_cases ha : (false,a) ∈ support f
    · exact Or.inl (covered ha)
    by_cases hb : (true,b) ∈ support f
    · exact Or.inr (covered hb)
    exact (maximal _ ha _ hb (show false ≠ true by decide)).elim
  have lo := edge_domination_lower dom
  have hi := Fintype.card_le_of_injective f f.injective
  change Fintype.card (Fin k × Bool) ≤ Fintype.card (Bool × Fin n) at hi
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hi
  omega

theorem matching_exact (n : ℕ) : minMaximalMatching (biclique n) = n := by
  let diag : Fin n × Bool ↪ Vertex n := (Equiv.prodComm (Fin n) Bool).toEmbedding
  have both (v : Vertex n) : v ∈ support diag :=
    (mem_support diag).mpr ⟨v.2,v.1,rfl⟩
  have hit : HasMaximalMatching (biclique n) n :=
    ⟨diag,fun _ => Bool.false_ne_true,fun u hu => (hu (both u)).elim⟩
  exact maximal_size (Nat.sInf_mem (show {k | HasMaximalMatching (biclique n) k}.Nonempty from ⟨n,hit⟩))

instance (n : ℕ) : DecidableRel (biclique n).Adj := fun x y => inferInstanceAs (Decidable (x.1 ≠ y.1))

theorem regular_biclique (n : ℕ) : (biclique n).IsRegularOfDegree n := by
  intro v
  rw [← card_neighborFinset_eq_degree]
  let e : Fin n ↪ Vertex n := ⟨fun i => (!v.1,i), fun _ _ h => congrArg Prod.snd h⟩
  have h : (biclique n).neighborFinset v = univ.map e := by
    ext u
    rw [mem_neighborFinset,mem_map]
    change (v.1 ≠ u.1) ↔ _
    constructor
    · intro ne
      have dist : ∀ a b : Bool, a ≠ b → (!a) = b := by decide
      exact ⟨u.2,mem_univ _,Prod.ext (dist _ _ ne) rfl⟩
    · rintro ⟨i,_,rfl⟩
      change v.1 ≠ !v.1
      cases v.1 <;> decide
  simp [h]

end AutoGraphForge1883
