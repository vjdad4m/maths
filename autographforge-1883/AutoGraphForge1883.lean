import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Ján Pastorek's AutoGraphForge, normalized rows 1883, 2088 and 2427.
The balanced-biclique rainbow proof below is from the checked line 1080 file.
Only its relevant definitions and lemmas are reproduced for standalone replay. -/
namespace AutoGraphForge373
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
/-- Same predicate as upstream IsCographClass and published line 378. -/
def Cograph := ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d →
  ¬G.Adj a c → ¬G.Adj b d → G.Adj a d

end AutoGraphForge373

namespace AutoGraphForge357
open Finset SimpleGraph
/-- GraphCalc permits exactly one of the three colors, or 0 (uncolored).
An uncolored vertex sees all three colors. -/
def Rainbow {U : Type*} (G : SimpleGraph U) (f : U → Fin 4) : Prop :=
  ∀ v, f v = 0 → ∀ c : Fin 4, c ≠ 0 → ∃ w, G.Adj v w ∧ f w = c
def weight {U : Type*} [Fintype U] (f : U → Fin 4) : ℕ := (univ.filter (fun v => f v ≠ 0)).card
noncomputable def rainbowNumber {U : Type*} [Fintype U] (G : SimpleGraph U) :=
  sInf {k | ∃ f : U → Fin 4, weight f = k ∧ Rainbow G f}
end AutoGraphForge357

namespace AutoGraphForge1080
open Finset SimpleGraph AutoGraphForge373 AutoGraphForge357
open Classical
noncomputable section
abbrev Vertex (n : ℕ) := Bool × Fin n

def biclique (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := x.1 ≠ y.1
  symm := fun _ _ h => h.symm
  loopless := fun _ => not_ne_iff.mpr rfl

private theorem opp {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

theorem biclique_class (n : ℕ) : Cograph (biclique n) ∧
    Nonempty (biclique n →g (⊤ : SimpleGraph (Fin 2))) := by
  have chain : ∀ a b c d : Bool, a ≠ b → b ≠ c → c ≠ d → a ≠ d := by decide
  refine ⟨fun a b c d ab bc cd _ _ => chain a.1 b.1 c.1 d.1 ab bc cd, ?_⟩
  let sideColor (b : Bool) : Fin 2 := if b then 1 else 0
  have proper : ∀ a b, a ≠ b → sideColor a ≠ sideColor b := by decide
  exact ⟨⟨fun x => sideColor x.1, fun {x y} e => proper x.1 y.1 e⟩⟩

variable {n : ℕ}

private def part (b : Bool) : Finset (Vertex n) :=
  univ.map ⟨fun i => (b,i), fun _ _ h => congrArg Prod.snd h⟩

@[simp] private theorem mem_part {b : Bool} {x : Vertex n} : x ∈ part b ↔ x.1 = b := by
  rcases x with ⟨a,i⟩
  simp [part, Prod.mk.injEq, eq_comm]

@[simp] private theorem card_part (b : Bool) : (part (n := n) b).card = n := by simp [part]

private theorem missing (S : Finset (Vertex n)) (small : S.card < n) (b : Bool) :
    ∃ w ∈ part b, w ∉ S := by
  by_contra! no
  have h := card_le_card (show part b ⊆ S from no)
  simp only [card_part] at h
  omega

private def paint (v : Vertex n) : Fin 4 :=
  if h : v.2.val < 3 then ⟨v.2.val+1, by omega⟩ else 0

private theorem paint_rainbow (hn : 3 ≤ n) : Rainbow (biclique n) (paint (n := n)) := by
  intro v _ c nz
  have pos : 0 < c.val := Nat.pos_of_ne_zero (fun h => nz (Fin.ext h))
  let j : Fin n := ⟨c.val - 1, by omega⟩
  refine ⟨(!v.1,j),show v.1 ≠ !v.1 from by cases v.1 <;> decide,?_⟩
  apply Fin.ext
  simp [paint,j,show c.val - 1 < 3 by omega]
  omega

private theorem paint_cost : weight (paint (n := n)) ≤ 6 := by
  let T := univ.filter (fun v : Vertex n => paint v ≠ 0)
  have small (v : T) : v.val.2.val < 3 := by
    have nonzero := (mem_filter.mp v.property).2
    by_contra h
    exact nonzero (by simp [paint,h])
  let index (v : T) : Bool × Fin 3 := (v.val.1,⟨v.val.2.val,small v⟩)
  have inj : Function.Injective index := by
    intro a b e
    exact Subtype.ext (Prod.ext (congrArg (Prod.fst : Bool × Fin 3 → Bool) e) (Fin.ext (congrArg (fun p : Bool × Fin 3 => p.2.val) e)))
  have bound := Fintype.card_le_of_injective index inj
  change T.card ≤ 6
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] using bound

/-- With fewer than six colored vertices each part has an uncolored vertex,
so each opposite part must contain all three singleton colors. -/
private theorem rainbow_lower (hn : 6 ≤ n) {f : Vertex n → Fin 4} (hf : Rainbow (biclique n) f) :
    6 ≤ weight f := by
  let T := univ.filter (fun v => f v ≠ 0)
  change 6 ≤ T.card
  by_contra! low
  have witnesses (b : Bool) (c : Fin 3) : ∃ v : T, v.val.1 = b ∧ f v = c.succ := by
    obtain ⟨u,hu,un⟩ := missing T (by omega) (!b)
    have zero : f u = 0 := by
      by_contra h
      exact un (mem_filter.mpr ⟨mem_univ _,h⟩)
    obtain ⟨v,e,h⟩ := hf u zero c.succ (Fin.succ_ne_zero c)
    have side := opp (show v.1 ≠ u.1 from e.symm)
    rw [mem_part.mp hu,Bool.not_not] at side
    exact ⟨⟨v,mem_filter.mpr ⟨mem_univ _,h ▸ Fin.succ_ne_zero c⟩⟩,side,h⟩
  choose pick side color using witnesses
  let pickPair (p : Bool × Fin 3) := pick p.1 p.2
  have inj : Function.Injective pickPair := by
    rintro ⟨a,i⟩ ⟨b,j⟩ e
    change pick a i = pick b j at e
    apply Prod.ext
    · exact (side a i).symm.trans ((congrArg (fun v : T => v.val.1) e).trans (side b j))
    · exact Fin.succ_inj.mp ((color a i).symm.trans ((congrArg (fun v : T => f v) e).trans (color b j)))
  have bound := Fintype.card_le_of_injective pickPair inj
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Fintype.card_coe] at bound
  omega

theorem rainbow_biclique (hn : 6 ≤ n) : rainbowNumber (biclique n) = 6 := by
  let sizes := {k | ∃ f : Vertex n → Fin 4, weight f = k ∧ Rainbow (biclique n) f}
  have hit : weight (paint (n := n)) ∈ sizes := ⟨paint,rfl,paint_rainbow (by omega)⟩
  obtain ⟨f,cost,valid⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨_,hit⟩)
  change weight f = rainbowNumber (biclique n) at cost
  exact Nat.le_antisymm ((Nat.sInf_le (s := sizes) hit).trans paint_cost)
    ((rainbow_lower hn valid).trans cost.le)

end
end AutoGraphForge1080

namespace Graffiti326
open Finset
def support {V : Type*} {k : ℕ} (f : Fin k × Bool ↪ V) : Finset V := univ.map f
theorem mem_support {V : Type*} {k : ℕ} (f : Fin k × Bool ↪ V) {v : V} :
    v ∈ support f ↔ ∃ i b, f (i,b) = v := by
  simp [support, Prod.exists]
end Graffiti326

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
open AutoGraphForge373 AutoGraphForge357
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

private def edgeAt (i j : Fin n) : (biclique n).edgeSet :=
  ⟨s((false,i),(true,j)),show false ≠ true by decide⟩

private theorem edge_indexed (e : (biclique n).edgeSet) :
    ∃ i j, e = edgeAt i j := by
  obtain ⟨e,he⟩ := e
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨a,i⟩ := x
    obtain ⟨b,j⟩ := y
    change a ≠ b at he
    cases a <;> cases b
    · exact (he rfl).elim
    · exact ⟨i,j,rfl⟩
    · exact ⟨j,i,Subtype.ext Sym2.eq_swap⟩
    · exact (he rfl).elim

private theorem share_endpoint (i j a b : Fin n) :
    (∃ v, v ∈ (edgeAt i j).val ∧ v ∈ (edgeAt a b).val) ↔ i = a ∨ j = b := by
  simp [edgeAt,Sym2.mem_iff,or_and_right,Prod.mk.injEq]

/-- The closed-neighborhood domination predicate of the source line graph,
over the actual Mathlib edge set. Equality of edges allows the selected edge
itself in the closed neighborhood. -/
def EdgeDominating {V : Type*} (G : SimpleGraph V) (es : Fin k → G.edgeSet) : Prop :=
  ∀ e : G.edgeSet, ∃ i v, v ∈ (es i).val ∧ v ∈ e.val

theorem source_minimum (n : ℕ) :
    sInf {k | ∃ es : Fin k → (biclique n).edgeSet, EdgeDominating (biclique n) es} =
      minMaximalMatching (biclique n) := by
  rw [matching_exact]
  let sizes := {k | ∃ es : Fin k → (biclique n).edgeSet, EdgeDominating (biclique n) es}
  have hit : n ∈ sizes := by
    refine ⟨fun i => edgeAt i i, ?_⟩
    intro e
    obtain ⟨a,b,rfl⟩ := edge_indexed e
    exact ⟨a,(share_endpoint a a a b).mpr (Or.inl rfl)⟩
  obtain ⟨es,dom⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨n,hit⟩)
  choose left right rep using fun i => edge_indexed (es i)
  apply Nat.le_antisymm (Nat.sInf_le (s := sizes) hit)
  apply edge_domination_lower (left := left) (right := right)
  intro a b
  obtain ⟨i,common⟩ := dom (edgeAt a b)
  rw [rep i] at common
  rcases (share_endpoint _ _ _ _).mp common with h | h
  · exact Or.inl ⟨i,h⟩
  · exact Or.inr ⟨i,h⟩

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

theorem four_clique_free (n : ℕ) : (biclique n).CliqueFree 4 := by
  intro s hs
  have injective : Function.Injective (fun x : s => x.val.1) := by
    intro a b h
    apply Subtype.ext
    by_contra diff
    exact (show a.val.1 ≠ b.val.1 from hs.1 a.property b.property diff) h
  have card := Fintype.card_le_of_injective _ injective
  rw [Fintype.card_coe,Fintype.card_bool,hs.2] at card
  omega

theorem row1883_false : ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    2 ≤ Fintype.card V → G.CliqueFree 4 → (∃ d, G.IsRegularOfDegree d) →
    minMaximalMatching G ≤ rainbowNumber G) := by
  intro claim
  have h := claim (Vertex 7) (biclique 7) (by decide) (four_clique_free 7) ⟨7,regular_biclique 7⟩
  rw [matching_exact,rainbow_biclique (by decide : 6 ≤ 7)] at h
  omega

theorem row2088_false : ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    2 ≤ Fintype.card V → (minMaximalMatching G : ℚ) ≤ (1/3 : ℚ) * rainbowNumber G + 6) := by
  intro claim
  have h := claim (Vertex 9) (biclique 9) (by decide)
  rw [matching_exact,rainbow_biclique (by decide : 6 ≤ 9)] at h
  norm_num at h

theorem row2427_false : ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    2 ≤ Fintype.card V → Cograph G →
    (minMaximalMatching G : ℚ) ≤ (2/9 : ℚ) * rainbowNumber G + 20/3) := by
  intro claim
  have h := claim (Vertex 9) (biclique 9) (by decide) (biclique_class 9).1
  rw [matching_exact,rainbow_biclique (by decide : 6 ≤ 9)] at h
  norm_num at h

#print axioms maximal_size
#print axioms matching_exact
#print axioms source_minimum
#print axioms AutoGraphForge1080.rainbow_biclique
#print axioms row1883_false
#print axioms row2088_false
#print axioms row2427_false
end AutoGraphForge1883
