import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Nat.Lattice

/-! AutoGraphForge normalized row 1707, ID ae818342.
Mycielski's 1955 construction supplies the triangle-free cores. -/
namespace MycielskiRainbow1707
open SimpleGraph Finset
variable {V : Type*}

def TriangleFree (H : SimpleGraph V) := ∀ x y z, H.Adj x y → H.Adj y z → ¬ H.Adj z x

/-- The claw and singleton-rainbow conventions of row 720. -/
def ClawFree (G : SimpleGraph V) := ∀ v a b c, G.Adj v a → G.Adj v b → G.Adj v c →
  a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c
def Rainbow (G : SimpleGraph V) (f : V → Fin 4) := ∀ v, f v = 0 → ∀ c : Fin 4,
  c ≠ 0 → ∃ w, G.Adj v w ∧ f w = c
def weight [Fintype V] (f : V → Fin 4) := (univ.filter fun v => f v ≠ 0).card
noncomputable def rainbowNumber [Fintype V] (G : SimpleGraph V) :=
  sInf {k | ∃ f : V → Fin 4, weight f = k ∧ Rainbow G f}

/-- As in row 621, clique partitions are proper colorings of the complement. -/
noncomputable def vertexCliqueCover [Fintype V] (G : SimpleGraph V) :=
  sInf {n : ℕ | Gᶜ.Colorable n}

namespace Mycielski
abbrev Vert (V : Type*) := V ⊕ Option V
abbrev old (v : V) : Vert V := .inl v
abbrev shadow (v : V) : Vert V := .inr (some v)
abbrev apex : Vert V := .inr none

private def edge (H : SimpleGraph V) : Vert V → Vert V → Prop
  | .inl x, .inl y | .inl x, .inr (some y) | .inr (some x), .inl y => H.Adj x y
  | .inr none, .inr (some _) | .inr (some _), .inr none => True
  | _, _ => False

def graph (H : SimpleGraph V) : SimpleGraph (Vert V) where
  Adj := edge H
  symm := by
    rintro (a | (_ | a)) (b | (_ | b)) h <;> simp_all [edge, H.adj_comm]
  loopless := by rintro (a | (_ | a)) <;> simp [edge]

theorem triangle_free (H : SimpleGraph V) (ht : TriangleFree H) : TriangleFree (graph H) := by
  rintro (a | (_ | a)) (b | (_ | b)) (c | (_ | c)) hab hbc hca <;>
    simp_all only [graph, edge] <;> exact ht a b c hab hbc hca

/-- Give old vertices and their shadows the same color, and the apex a fresh color. -/
theorem extend {H : SimpleGraph V} {k : ℕ} (hc : H.Colorable k) : (graph H).Colorable (k+1) := by
  obtain ⟨c⟩ := hc
  let paint : Vert V → Fin (k+1)
    | .inl v | .inr (some v) => (c v).castSucc
    | .inr none => Fin.last k
  have last_ne (i : Fin k) : Fin.last k ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  refine ⟨Coloring.mk paint ?_⟩
  rintro (a | (_ | a)) (b | (_ | b)) h <;>
    simp_all [graph, edge, paint, Fin.castSucc_ne_last, last_ne] <;>
    exact c.valid h

/-- Recolor each old vertex of the apex color with its shadow's color. The
result still colors the old graph properly and completely avoids the apex color. -/
theorem reduce {H : SimpleGraph V} {k : ℕ} (hc : (graph H).Colorable (k+1)) :
    H.Colorable k := by
  classical
  obtain ⟨c⟩ := hc
  let a := c apex
  let paint (v : V) := if c (old v) = a then c (shadow v) else c (old v)
  have avoids (v : V) : paint v ≠ a := by
    by_cases h : c (old v) = a
    · simpa [paint,h,a] using c.valid (show (graph H).Adj (shadow v) apex from trivial)
    · simp [paint,h]
  have proper {x y : V} (h : H.Adj x y) : paint x ≠ paint y := by
    have oo := c.valid (show (graph H).Adj (old x) (old y) from h)
    by_cases hx : c (old x) = a <;> by_cases hy : c (old y) = a
    · exact False.elim (oo (hx.trans hy.symm))
    · simpa [paint,hx,hy] using c.valid (show (graph H).Adj (shadow x) (old y) from h)
    · simpa [paint,hx,hy] using c.valid (show (graph H).Adj (old x) (shadow y) from h)
    · simpa [paint,hx,hy] using oo
  choose smaller eq using fun v => Fin.exists_succAbove_eq (avoids v)
  exact ⟨Coloring.mk smaller (fun {x y} xy h => proper xy
    ((eq x).symm.trans ((congrArg a.succAbove h).trans (eq y))))⟩

/-- Starting at K₂ yields triangle-free graphs of chromatic numbers 2,3,4,...
and respective orders 2,5,11,... . -/
theorem cores (n : ℕ) : ∃ (U : Type) (_ : Fintype U) (H : SimpleGraph U),
    Fintype.card U + 1 = 3 * 2 ^ n ∧ TriangleFree H ∧
    H.Colorable (n+2) ∧ ¬H.Colorable (n+1) := by
  induction n with
  | zero =>
    refine ⟨Fin 2,inferInstance,⊤,by decide,?_,?_,?_⟩
    · unfold TriangleFree
      decide
    · exact ⟨Coloring.mk id (fun h => (top_adj _ _).mp h)⟩
    · change ¬(⊤ : SimpleGraph (Fin 2)).Colorable 1
      rintro ⟨c⟩
      exact c.valid (show (⊤ : SimpleGraph (Fin 2)).Adj 0 1 by decide) (Subsingleton.elim _ _)
  | succ n ih =>
    obtain ⟨U,inst,H,sz,ht,hc,hn⟩ := ih
    refine ⟨Vert U,inferInstance,graph H,?_,triangle_free H ht,extend hc,fun h => hn (reduce h)⟩
    simp only [Vert, Fintype.card_sum, Fintype.card_option, pow_succ]
    omega
end Mycielski

/-- H with three isolated vertices; its complement has three universal vertices. -/
private def coreAdj (H : SimpleGraph V) : V ⊕ Fin 3 → V ⊕ Fin 3 → Prop
  | .inl x, .inl y => H.Adj x y
  | _, _ => False

def padded (H : SimpleGraph V) : SimpleGraph (V ⊕ Fin 3) where
  Adj := coreAdj H
  symm := by rintro (a|a) (b|b) h <;> simp_all [coreAdj,H.adj_comm]
  loopless := by rintro (a|a) <;> simp [coreAdj]

abbrev witness (H : SimpleGraph V) := (padded H)ᶜ

theorem witness_clawfree {H : SimpleGraph V} (ht : TriangleFree H) : ClawFree (witness H) := by
  have tri : TriangleFree (padded H) := by
    rintro (a|a) (b|b) (c|c) ab bc ca <;> simp_all only [padded,coreAdj]
    exact ht _ _ _ ab bc ca
  intro _ a b c _ _ _ ab ac bc
  simp only [compl_adj,ab,ac,bc,true_and]
  by_contra! h
  exact tri a b c (h.1 ab) (h.2.2 bc) (h.2.1 ac).symm

theorem witness_connected (H : SimpleGraph V) : (witness H).Connected := by
  let hub : V ⊕ Fin 3 := .inr 0
  have reach (v : V ⊕ Fin 3) : (witness H).Reachable v hub := by
    by_cases h : v = hub
    · subst v; exact Reachable.rfl
    · apply Adj.reachable
      exact (compl_adj _ _ _).mpr ⟨h,by cases v <;> simp [hub,padded,coreAdj]⟩
  exact ⟨fun x y => (reach x).trans (reach y).symm⟩

private def palette : V ⊕ Fin 3 → Fin 4
  | .inl _ => 0
  | .inr i => i.succ

theorem witness_rainbow [Fintype V] (H : SimpleGraph V) : rainbowNumber (witness H) = 3 := by
  classical
  have valid : Rainbow (witness H) palette := by
    rintro (v|v) hv c hc
    · obtain ⟨i,rfl⟩ := Fin.exists_succ_eq.mpr hc
      exact ⟨.inr i, (compl_adj _ _ _).mpr ⟨by simp,by simp [padded,coreAdj]⟩, rfl⟩
    · exact (Fin.succ_ne_zero v hv).elim
  have cost : weight (@palette V) = 3 := by
    unfold weight
    rw [show (univ.filter fun v => palette v ≠ 0) =
        (univ : Finset (Fin 3)).map (Function.Embedding.inr : Fin 3 ↪ V ⊕ Fin 3) by
      ext v; cases v <;> simp [palette]]
    simp
  let sizes := {k | ∃ f : V ⊕ Fin 3 → Fin 4, weight f = k ∧ Rainbow (witness H) f}
  have upper : 3 ∈ sizes := ⟨_,cost,valid⟩
  obtain ⟨f,feq,hf⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨_,upper⟩)
  have lb : 3 ≤ weight f := by
    by_cases hz : ∃ v, f v = 0
    · obtain ⟨v,hv⟩ := hz
      obtain ⟨a,_,ha⟩ := hf v hv 1 (by decide)
      obtain ⟨b,_,hb⟩ := hf v hv 2 (by decide)
      obtain ⟨c,_,hc⟩ := hf v hv 3 (by decide)
      apply two_lt_card_iff.mpr
      refine ⟨a,b,c,by simp [ha],by simp [hb],by simp [hc],?_,?_,?_⟩
      · rintro rfl; rw [ha] at hb; exact (by decide : (1 : Fin 4) ≠ 2) hb
      · rintro rfl; rw [ha] at hc; exact (by decide : (1 : Fin 4) ≠ 3) hc
      · rintro rfl; rw [hb] at hc; exact (by decide : (2 : Fin 4) ≠ 3) hc
    · push_neg at hz
      simp [weight,hz]
  exact le_antisymm (Nat.sInf_le upper) (lb.trans_eq feq)

theorem witness_cover [Fintype V] {H : SimpleGraph V} {k : ℕ}
    (hc : H.Colorable (k+1)) (hn : ¬H.Colorable k) : vertexCliqueCover (witness H) = k+1 := by
  obtain ⟨c⟩ := hc
  let f : V ⊕ Fin 3 → Fin (k+1) := Sum.elim c (fun _ => 0)
  have upper : (padded H).Colorable (k+1) := by
    refine ⟨Coloring.mk f ?_⟩
    rintro (x|x) (y|y) h <;> simp_all only [padded,coreAdj, f, Sum.elim_inl]
    exact c.valid h
  have no : ¬(padded H).Colorable k := by
    rintro ⟨d⟩
    exact hn ⟨Coloring.mk (fun v => d (.inl v))
      (fun {x y} h => d.valid (show (padded H).Adj (.inl x) (.inl y) from h))⟩
  unfold vertexCliqueCover
  rw [compl_compl]
  have att := Nat.sInf_mem (s := {n | (padded H).Colorable n}) ⟨_,upper⟩
  apply le_antisymm (Nat.sInf_le upper)
  exact Nat.le_of_not_lt fun h => no (Colorable.mono (Nat.le_of_lt_succ h) att)

/-- A connected claw-free family with singleton rainbow number exactly 3 and
clique partition number exactly n+2, including order 14 when n=2. -/
theorem separation (n : ℕ) : ∃ (U : Type) (_ : Fintype U) (G : SimpleGraph U),
    Fintype.card U = 3 * 2 ^ n + 2 ∧ G.Connected ∧ ClawFree G ∧
    vertexCliqueCover G = n+2 ∧ rainbowNumber G = 3 := by
  obtain ⟨V,inst,H,sz,ht,hc,hn⟩ := Mycielski.cores n
  refine ⟨V ⊕ Fin 3,inferInstance,witness H,?_,witness_connected H,witness_clawfree ht,
    witness_cover hc hn,witness_rainbow H⟩
  simp only [Fintype.card_sum,Fintype.card_fin]
  omega

theorem row1707_witness : ∃ (U : Type) (_ : Fintype U) (G : SimpleGraph U),
    Fintype.card U = 14 ∧ G.Connected ∧ ClawFree G ∧ vertexCliqueCover G = 4 ∧
    rainbowNumber G = 3 := separation 2

theorem row1707_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U),
    2 ≤ Fintype.card U → ClawFree G → vertexCliqueCover G ≤ rainbowNumber G) := by
  intro claim
  obtain ⟨U,inst,G,sz,_,hf,hc,hr⟩ := row1707_witness
  have h := claim U G (by omega) hf
  rw [hc,hr] at h
  omega

#print axioms Mycielski.cores
#print axioms witness_cover
#print axioms witness_rainbow
#print axioms separation
#print axioms row1707_witness
#print axioms row1707_false
end MycielskiRainbow1707
