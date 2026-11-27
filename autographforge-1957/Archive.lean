import Factor
import Mathlib.Combinatorics.SimpleGraph.Circulant

namespace RegularCliques1957.Archive
open SimpleGraph Finset Graffiti326 AutoGraphForge378 TriangleMatching1078 HallRainbow1121
abbrev C := cycleGraph 24

/-- Pair 3i with 3i+1 for each i. -/
def endpoint (i : Fin 8) (b : Bool) : Fin 24 :=
  ⟨3*i.val + (if b then 1 else 0), by have := i.isLt; cases b <;> simp <;> omega⟩

theorem maximal : HasMaximalMatching C 8 := by
  have distinct : ∀ i j b c, endpoint i b = endpoint j c → i=j ∧ b=c := by decide
  let f : Fin 8 × Bool ↪ Fin 24 := ⟨fun z => endpoint z.1 z.2, by
    rintro ⟨i,b⟩ ⟨j,c⟩ e
    exact Prod.ext (distinct i j b c e).1 (distinct i j b c e).2⟩
  have edge : ∀ i, C.Adj (endpoint i false) (endpoint i true) := by decide
  have hit : ∀ x y, C.Adj x y → (∃ i b, endpoint i b = x) ∨ (∃ i b, endpoint i b = y) := by decide
  refine ⟨f,edge,?_⟩
  intro x hx y hy xy
  rcases hit x y xy with h|h
  · exact hx ((Graffiti326.mem_support f).mpr h)
  · exact hy ((Graffiti326.mem_support f).mpr h)

/-- The eight selected edges form an induced matching, so an edge cannot
dominate two of them. This is the packing argument used for row 659. -/
theorem edge_exact : lineDomination C = 8 := by
  classical
  apply le_antisymm (lineDomination_le_of_maximal C maximal)
  obtain ⟨D,sz,dom⟩ := Nat.sInf_mem (s:={k | ∃ D : Finset C.edgeSet, D.card=k ∧ Dominates C.lineGraph D})
    ⟨_,univ,rfl,fun e => Or.inl (mem_univ e)⟩
  change D.card = lineDomination C at sz
  have edge : ∀ i, C.Adj (endpoint i false) (endpoint i true) := by decide
  have witness (i : Fin 8) : ∃ e : ↥D, ∃ b, endpoint i b ∈ e.val.val := by
    obtain ⟨e,he,z,ze,zi⟩ := (dominates_iff C D).mp dom ⟨s(endpoint i false,endpoint i true),edge i⟩
    rcases Sym2.mem_iff.mp zi with rfl|rfl
    · exact ⟨⟨e,he⟩,false,ze⟩
    · exact ⟨⟨e,he⟩,true,ze⟩
  choose pick bit hits using witness
  have apart : ∀ i j b c, endpoint i b = endpoint j c ∨ C.Adj (endpoint i b) (endpoint j c) → i=j := by decide
  have inj : Function.Injective pick := by
    intro i j eq
    by_cases same : endpoint i (bit i) = endpoint j (bit j)
    · exact apart _ _ _ _ (Or.inl same)
    have repr := (Sym2.mem_and_mem_iff same).mp ⟨hits i,eq ▸ hits j⟩
    have adj := (pick i).val.property
    rw [repr] at adj
    exact apart _ _ _ _ (Or.inr adj)
  simpa only [Fintype.card_fin,Fintype.card_coe,sz] using Fintype.card_le_of_injective pick inj

def palette (v : Fin 24) : Fin 12 := ⟨v.val/2,by have := v.isLt; omega⟩
def evenVertex (i : Fin 12) : Fin 24 := ⟨2*i.val,by have := i.isLt; omega⟩

theorem cover_exact : vertexCliqueCover C = 12 := by
  have proper : ∀ v w, Cᶜ.Adj v w → palette v ≠ palette w := by decide
  have feasible : Cᶜ.Colorable 12 := ⟨Coloring.mk palette (fun h => proper _ _ h)⟩
  apply le_antisymm (Nat.sInf_le feasible)
  obtain ⟨opt⟩ := Nat.sInf_mem (s:={k | Cᶜ.Colorable k}) ⟨12,feasible⟩
  have distinct : ∀ i j, i ≠ j → Cᶜ.Adj (evenVertex i) (evenVertex j) := by decide
  have inj : Function.Injective (fun i => opt (evenVertex i)) :=
    fun i j h => Classical.byContradiction (fun ne => opt.valid (distinct i j ne) h)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ inj

theorem released_witness : 2 ≤ Fintype.card (Fin 24) ∧ C.Connected ∧ C.IsRegularOfDegree 2 ∧
    ¬ (vertexCliqueCover C : ℚ) ≤ (4/3 : ℚ)*lineDomination C+1 := by
  exact ⟨by decide,cycleGraph_connected (n:=23),fun _ => cycleGraph_degree_three_le (n:=21),
    by rw [cover_exact,edge_exact]; norm_num⟩

end RegularCliques1957.Archive
