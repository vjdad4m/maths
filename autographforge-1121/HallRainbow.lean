import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice

/-! AutoGraphForge normalized physical row 1121, ID 6deb0d7d.
A local incidence bound gives a Hall matching into a dominating set. -/
namespace HallRainbow1121
open Finset SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- GraphCalc counts nonempty classes of a proper coloring of the complement. -/
noncomputable def vertexCliqueCover := sInf {n : ℕ | Gᶜ.Colorable n}

/-- GraphCalc uses a single label per vertex. Zero is the uncolored label. -/
def Rainbow {k : ℕ} (f : V → Fin (k+1)) := ∀ v, f v = 0 → ∀ c : Fin (k+1),
  c ≠ 0 → ∃ u, G.Adj v u ∧ f u = c

def weight {k : ℕ} (f : V → Fin (k+1)) := (univ.filter fun v => f v ≠ 0).card
noncomputable def rainbowNumber (k : ℕ) :=
  sInf {n | ∃ f : V → Fin (k+1), weight f = n ∧ Rainbow G f}

/-- Every vertex outside S has at least k neighbors in S. Each vertex of S
has at most k neighbors outside. Hall gives distinct adjacent representatives. -/
theorem match_outside [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) {k : ℕ} (hk : 0 < k)
    (demand : ∀ v ∉ S, k ≤ (S.filter (G.Adj v)).card)
    (capacity : ∀ u ∈ S, ((G.neighborFinset u) \ S).card ≤ k) :
    ∃ mate : {v // v ∉ S} → V, Function.Injective mate ∧
      ∀ x, mate x ∈ S ∧ G.Adj x.val (mate x) := by
  classical
  let neighbors (x : {v // v ∉ S}) := S.filter (G.Adj x.val)
  suffices hall : ∀ X : Finset {v // v ∉ S}, X.card ≤ (X.biUnion neighbors).card by
    obtain ⟨mate,inj,hn⟩ := (all_card_le_biUnion_card_iff_existsInjective' neighbors).mp hall
    exact ⟨mate,inj,fun x => mem_filter.mp (hn x)⟩
  intro X
  let N := X.biUnion neighbors
  let R (x : {v // v ∉ S}) (u : V) := G.Adj x.val u
  have left (x) (hx : x ∈ X) : k ≤ (N.bipartiteAbove R x).card := by
    apply (demand x.val x.property).trans (card_le_card ?_)
    intro u hu
    exact (mem_bipartiteAbove _).mpr ⟨mem_biUnion.mpr ⟨x,hx,hu⟩,(mem_filter.mp hu).2⟩
  have right (u) (hu : u ∈ N) : (X.bipartiteBelow R u).card ≤ k := by
    obtain ⟨x,_,hm⟩ := mem_biUnion.mp hu
    apply le_trans (card_le_card_of_injOn Subtype.val ?_ Subtype.val_injective.injOn)
      (capacity u (mem_filter.mp hm).1)
    intro y hy
    exact mem_sdiff.mpr ⟨(G.mem_neighborFinset u y.val).mpr ((mem_bipartiteBelow _).mp hy).2.symm,
      y.property⟩
  exact Nat.le_of_mul_le_mul_right (card_mul_le_card_mul R left right) hk

omit [Fintype V] in
/-- Matched pairs are cliques, and each unused representative gives a singleton. -/
theorem cover_of_matching [DecidableEq V] (S : Finset V) (mate : {v // v ∉ S} → V)
    (inj : Function.Injective mate) (hm : ∀ x, mate x ∈ S ∧ G.Adj x.val (mate x)) :
    Gᶜ.Colorable S.card := by
  classical
  let owner (v : V) : ↥S := if h : v ∈ S then ⟨v,h⟩ else ⟨mate ⟨v,h⟩,(hm _).1⟩
  have proper {v w : V} (e : Gᶜ.Adj v w) : owner v ≠ owner w := by
    intro eq
    obtain ⟨ne,nonedge⟩ := (G.compl_adj _ _).mp e
    have valEq := congrArg Subtype.val eq
    by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
    · exact ne (by simpa [owner,hv,hw] using valEq)
    · have h : v = mate ⟨w,hw⟩ := by simpa [owner,hv,hw] using valEq
      exact nonedge (h ▸ (hm ⟨w,hw⟩).2.symm)
    · have h : mate ⟨v,hv⟩ = w := by simpa [owner,hv,hw] using valEq
      exact nonedge (h ▸ (hm ⟨v,hv⟩).2)
    · have h : mate ⟨v,hv⟩ = mate ⟨w,hw⟩ := by simpa [owner,hv,hw] using valEq
      exact ne (congrArg Subtype.val (inj h))
  let col : Gᶜ.Coloring ↥S := Coloring.mk owner proper
  simpa using col.colorable

/-- For every positive palette size, a feasible labeling yields a clique
partition with at most its weight whenever maximum degree is at most k. -/
theorem cover_of_rainbow [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k)
    (degree : ∀ u, G.degree u ≤ k) {f : V → Fin (k+1)} (hf : Rainbow G f) :
    Gᶜ.Colorable (weight f) := by
  classical
  let S := univ.filter fun v => f v ≠ 0
  have demand (v : V) (hv : v ∉ S) : k ≤ (S.filter (G.Adj v)).card := by
    have zero : f v = 0 := by simpa [S] using hv
    have witness (i : Fin k) := hf v zero i.succ (Fin.succ_ne_zero i)
    choose pick edge color using witness
    have inj : Function.Injective pick := by
      intro i j eq
      exact Fin.succ_injective _ ((color i).symm.trans ((congrArg f eq).trans (color j)))
    rw [← Fintype.card_fin k, ← card_univ]
    apply card_le_card_of_injOn pick ?_ inj.injOn
    intro i _
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(color i).symm ▸ Fin.succ_ne_zero i⟩,edge i⟩
  have capacity (u : V) (_ : u ∈ S) : ((G.neighborFinset u) \ S).card ≤ k :=
    (card_le_card sdiff_subset).trans (degree u)
  obtain ⟨mate,inj,hm⟩ := match_outside G S hk demand capacity
  exact cover_of_matching G S mate inj hm

theorem rainbow_bound [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k)
    (degree : ∀ u, G.degree u ≤ k) : vertexCliqueCover G ≤ rainbowNumber G k := by
  let sizes := {n | ∃ f : V → Fin (k+1), weight f = n ∧ Rainbow G f}
  let label : Fin (k+1) := ⟨1,Nat.succ_lt_succ hk⟩
  have nz : label ≠ 0 := fun h => Nat.one_ne_zero (congrArg Fin.val h)
  have feasible : sizes.Nonempty :=
    ⟨_,fun _ => label,rfl,fun _ hv => False.elim (nz hv)⟩
  obtain ⟨f,cost,hf⟩ := Nat.sInf_mem feasible
  apply Nat.sInf_le
  change weight f = rainbowNumber G k at cost
  rw [← cost]
  exact cover_of_rainbow G hk degree hf

/-- The catalogue adds an order-at-least-two hypothesis. -/
theorem row1121 [DecidableRel G.Adj] (_ : 2 ≤ Fintype.card V)
    (subcubic : ∀ u, G.degree u ≤ 3) :
    vertexCliqueCover G ≤ rainbowNumber G 3 := rainbow_bound G (by decide) subcubic

#print axioms match_outside
#print axioms cover_of_matching
#print axioms cover_of_rainbow
#print axioms rainbow_bound
#print axioms row1121
end HallRainbow1121
