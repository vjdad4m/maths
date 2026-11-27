import HallRainbow
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Sum

/-! Hall's theorem with extra singleton slots, applied to the usual planar
bipartite edge budget. The Euler edge bound is an explicit hypothesis here.
The independent Row464 module proves its counterexample without this hypothesis. -/
namespace PlanarRainbow464
open Finset SimpleGraph HallRainbow1121
variable {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableEq U] [DecidableRel G.Adj]

/-- The neighbors in S of a vertex outside S. -/
def markedNeighbors (S : Finset U) (w : {v // v ∉ S}) : Finset ↥S :=
  univ.filter (fun u => G.Adj w.val u.val)

/-- The usual bipartite planar edge inequality on each nonempty set of zeros
and its marked neighbors. Only cross edges are counted. -/
def CrossEuler (S : Finset U) := ∀ (X : Finset {v // v ∉ S}), X.Nonempty →
  (∑ x ∈ X, (markedNeighbors G S x).card) + 4 ≤
    2 * (X.card + (X.biUnion (markedNeighbors G S)).card)

/-- Add d common extra slots to Hall's assignment. Each used extra slot holds
a singleton. The real slots hold either a single marked vertex or a matched edge. -/
theorem cover_of_deficit (S : Finset U) (d : ℕ)
    (bound : ∀ X : Finset {v // v ∉ S}, X.card ≤ (X.biUnion (markedNeighbors G S)).card+d) :
    Gᶜ.Colorable (S.card+d) := by
  classical
  let W := {v // v ∉ S}
  let N := markedNeighbors G S
  let choices (w : W) : Finset (↥S ⊕ Fin d) := (N w).disjSum univ
  have hall (X : Finset W) : X.card ≤ (X.biUnion choices).card := by
    rcases X.eq_empty_or_nonempty with rfl|hne
    · simp
    · have union : X.biUnion choices = (X.biUnion N).disjSum (univ : Finset (Fin d)) := by
        ext z
        rcases z with u|i
        · simp [choices]
        · simpa [choices] using hne
      simpa [union,N] using bound X
  obtain ⟨mate,inj,good⟩ := (all_card_le_biUnion_card_iff_existsInjective' choices).mp hall
  let color (v : U) : ↥S ⊕ Fin d := if h : v ∈ S then .inl ⟨v,h⟩ else mate ⟨v,h⟩
  have adjacent (w : W) (u : ↥S) (eq : mate w = .inl u) : G.Adj w.val u.val := by
    have h := good w
    simpa [choices,N,markedNeighbors,eq] using h
  have proper {x y : U} (edge : Gᶜ.Adj x y) : color x ≠ color y := by
    intro eq
    obtain ⟨ne,no⟩ := (G.compl_adj _ _).mp edge
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simp [color,hx,hy,ne] at eq
    · exact no (adjacent ⟨y,hy⟩ ⟨x,hx⟩ (by simpa [color,hx,hy] using eq.symm)).symm
    · exact no (adjacent ⟨x,hx⟩ ⟨y,hy⟩ (by simpa [color,hx,hy] using eq))
    · exact ne (congrArg Subtype.val (inj (by simpa [color,hx,hy] using eq)))
  let col : Gᶜ.Coloring (↥S ⊕ Fin d) := Coloring.mk color proper
  simpa using col.colorable

/-- A set giving at least three neighbors to every outside vertex admits a
clique cover of size at most |S| + (|S| - 4) under the cross-edge budget. -/
theorem cover_of_crossEuler (S : Finset U) (sparse : CrossEuler G S)
    (sees : ∀ w, 3 ≤ (markedNeighbors G S w).card) :
    vertexCliqueCover G ≤ S.card + (S.card-4) := by
  apply Nat.sInf_le
  apply cover_of_deficit
  intro X
  rcases X.eq_empty_or_nonempty with rfl|hne
  · simp
  · have demand := sum_le_sum (s := X) (fun w _ => sees w)
    simp only [sum_const,smul_eq_mul] at demand
    have budget := sparse X hne
    have cap : (X.biUnion (markedNeighbors G S)).card ≤ S.card := by
      simpa using (card_le_univ (X.biUnion (markedNeighbors G S)))
    omega

/-- The same inequality for a singleton three-rainbow labeling. -/
theorem rainbow_cover_of_crossEuler {f : U → Fin 4} (hf : Rainbow G f)
    (sparse : CrossEuler G (univ.filter (fun v => f v ≠ 0))) :
    vertexCliqueCover G ≤ weight f + (weight f-4) := by
  classical
  let S := univ.filter fun v => f v ≠ 0
  apply cover_of_crossEuler G S sparse
  intro w
  have zero : f w.val=0 := by simpa [S] using w.property
  have witness (j : Fin 3) := hf w.val zero j.succ (Fin.succ_ne_zero j)
  choose v edge label using witness
  let pick (j : Fin 3) : ↥S := ⟨v j,by simp [S,label]⟩
  have inj : Function.Injective pick := by
    intro a b eq
    have e : v a=v b := congrArg Subtype.val eq
    exact Fin.succ_injective _ ((label a).symm.trans ((congrArg f e).trans (label b)))
  have count : (univ : Finset (Fin 3)).card ≤ (markedNeighbors G S w).card := by
    apply card_le_card_of_injOn pick ?_ inj.injOn
    exact fun j _ => mem_filter.mpr ⟨mem_univ _,edge j⟩
  simpa using count

/-- Optimizer form, retaining the exact cross-edge hypothesis used above. -/
theorem sharp_bound
    (sparse : ∀ f : U → Fin 4, Rainbow G f → CrossEuler G (univ.filter (fun v => f v ≠ 0))) :
    vertexCliqueCover G ≤ rainbowNumber G 3 + (rainbowNumber G 3-4) := by
  let sizes := {n | ∃ f : U → Fin 4, weight f = n ∧ Rainbow G f}
  have feasible : sizes.Nonempty :=
    ⟨_,fun _ => 1,rfl,fun _ h => False.elim ((by decide : (1 : Fin 4) ≠ 0) h)⟩
  obtain ⟨f,cost,hf⟩ := Nat.sInf_mem feasible
  change weight f = rainbowNumber G 3 at cost
  rw [← cost]
  exact rainbow_cover_of_crossEuler G hf (sparse f hf)

#print axioms sharp_bound
#print axioms cover_of_deficit
#print axioms rainbow_cover_of_crossEuler
end PlanarRainbow464
