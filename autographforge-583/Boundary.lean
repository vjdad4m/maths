import Sharp
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace SlaterEdges583
open Finset SimpleGraph TriangleMatching1078

private abbrev P := pathGraph 4
local instance : DecidableRel P.Adj := fun _ _ => decidable_of_iff' _ pathGraph_adj

/-- On P₄, the middle edge dominates the line graph but a Slater
prefix of length one has capacity three. -/
theorem path_four : P.Connected ∧ P.minDegree = 1 ∧ slater P = 2 ∧ lineDomination P = 1 := by
  have low := slater_mass P 2 (by decide)
  have capacities := capacity_bound P ({1,2} : Finset (Fin 4)) 2 (by decide)
  have val : (∑ u ∈ ({1,2} : Finset (Fin 4)), (P.degree u + 1)) = 6 := by decide
  rw [val] at capacities
  have hiSlater : slater P ≤ 2 := Nat.sInf_le
    (s := {k : ℕ | Fintype.card (Fin 4) ≤ k + ((degreesDesc P).take k).sum})
    (show 4 ≤ 2 + ((degreesDesc P).take 2).sum from by omega)
  rw [Fintype.card_fin] at low
  have two : slater P = 2 := by omega
  let mid : P.edgeSet := ⟨s(1,2),by apply pathGraph_adj.mpr; decide⟩
  have covers : Dominates P.lineGraph {mid} := by
    rw [dominates_iff]
    intro e
    have hit : ∀ a b : Fin 4, P.Adj a b → a=1 ∨ b=1 ∨ a=2 ∨ b=2 := by decide
    obtain ⟨q,hq⟩ := e
    induction q using Sym2.ind with
    | h a b =>
      refine ⟨mid,mem_singleton_self _,?_⟩
      rcases hit a b hq with rfl|rfl|rfl|rfl
      · exact ⟨1,Sym2.mem_mk_left _ _,Sym2.mem_mk_left _ _⟩
      · exact ⟨1,Sym2.mem_mk_left _ _,Sym2.mem_mk_right _ _⟩
      · exact ⟨2,Sym2.mem_mk_right _ _,Sym2.mem_mk_left _ _⟩
      · exact ⟨2,Sym2.mem_mk_right _ _,Sym2.mem_mk_right _ _⟩
  have hi : lineDomination P ≤ 1 := Nat.sInf_le ⟨{mid},card_singleton _,covers⟩
  have gt : 0 < lineDomination P := by
    obtain ⟨D,sz,dom⟩ := EulerDom574.line_attained P
    obtain ⟨e,he,_⟩ := (dominates_iff P D).mp dom mid
    rw [← sz]
    exact card_pos.mpr ⟨e,he⟩
  exact ⟨pathGraph_connected 3,by decide,two,by omega⟩

private abbrev K := (⊤ : SimpleGraph (Fin 3))

/-- The triangle supplies the remaining positive equality value k = 1. -/
theorem triangle : 2 ≤ Fintype.card (Fin 3) ∧ K.CliqueFree 4 ∧ K.Connected ∧
    (∀ v, Even (K.degree v)) ∧ slater K = 1 ∧ lineDomination K = 1 ∧
    AutoGraphForge378.minMaximalMatching K = 1 := by
  have order : 2 ≤ Fintype.card (Fin 3) := by decide
  have conn : K.Connected := by
    refine ⟨fun u v => ?_⟩
    by_cases eq : u=v
    · subst v; exact Reachable.rfl
    · exact (show K.Adj u v from eq).reachable
  have even (v : Fin 3) : Even (K.degree v) := ⟨1,by simp [K]⟩
  have noFour : K.CliqueFree 4 := by
    intro s hs
    have h := s.card_le_univ
    rw [hs.card_eq] at h
    exact (by decide : ¬ 4 ≤ Fintype.card (Fin 3)) h
  let f : Fin 1 × Bool ↪ Fin 3 :=
    ⟨fun p => if p.2 then 1 else 0, by
      have h : ∀ p q : Fin 1 × Bool,
          (if p.2 then 1 else 0 : Fin 3) = (if q.2 then 1 else 0) → p=q := by decide
      exact fun p q => h p q⟩
  have mat : AutoGraphForge378.HasMaximalMatching K 1 := by
    refine ⟨f,fun _ => (by decide : (0 : Fin 3) ≠ 1),?_⟩
    have missed (v : Fin 3) (hv : v ∉ Graffiti326.support f) : v = 2 := by
      have hs (b : Bool) := (Graffiti326.mem_support f).mpr (show ∃ i c, f (i,c) = f (0,b) from ⟨0,b,rfl⟩)
      have h0 : v ≠ 0 := fun eq => hv (eq.symm ▸ hs false)
      have h1 : v ≠ 1 := fun eq => hv (eq.symm ▸ hs true)
      exact (by decide : ∀ j : Fin 3, j ≠ 0 → j ≠ 1 → j=2) v h0 h1
    intro u hu v hv h
    exact h.ne ((missed u hu).trans (missed v hv).symm)
  have hm : AutoGraphForge378.minMaximalMatching K ≤ 1 := Nat.sInf_le mat
  have src := row583 K order noFour conn even
  have pos := slater_mass K 2 (by decide)
  rw [Fintype.card_fin] at pos
  have compare := lineDomination_le_matching K
  exact ⟨order,noFour,conn,even,by omega,by omega,by omega⟩

#print axioms triangle
#print axioms path_four
end SlaterEdges583
