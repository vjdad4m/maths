import Cover

namespace BullCover1125
open SimpleGraph Finset TriangleMatching1078

abbrev triangle := listed (n:=3) [(0,1),(1,2),(0,2)]

/-- Use bounded enumeration only on the fixed three-, four- and five-vertex
graphs. All optimizers in the general statement are defined independently. -/
private def EdgeDominates {V : Type*} (G : SimpleGraph V) (D : Finset G.edgeSet) :=
  ∀ e : G.edgeSet, ∃ f ∈ D, ∃ v : V, v ∈ f.val ∧ v ∈ e.val

instance {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : Finset G.edgeSet) : Decidable (Covers G D) := by
  unfold Covers
  infer_instance

private instance {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : Finset G.edgeSet) : Decidable (EdgeDominates G D) := by
  unfold EdgeDominates
  infer_instance

private theorem cover_check {V : Type*} (G : SimpleGraph V) (r : ℕ)
    (exists_min : ∃ P : Finset G.edgeSet, P.card=r ∧ Covers G P)
    (lower : ∀ P : Finset G.edgeSet, Covers G P → r ≤ P.card) : edgeCoverNumber G = r := by
  obtain ⟨P,sz,h⟩ := Nat.sInf_mem (s:={n | ∃ P : Finset G.edgeSet, P.card=n ∧ Covers G P})
    ⟨r,exists_min⟩
  exact le_antisymm (Nat.sInf_le exists_min) ((lower P h).trans_eq sz)

private theorem dom_check {V : Type*} (G : SimpleGraph V)
    (exists_one : ∃ D : Finset G.edgeSet, D.card=1 ∧ EdgeDominates G D)
    (positive : ∀ D : Finset G.edgeSet, EdgeDominates G D → 1 ≤ D.card) : lineDomination G = 1 := by
  obtain ⟨D,one,dom⟩ := exists_one
  have feasible : ∃ P : Finset G.edgeSet, P.card=1 ∧ Dominates G.lineGraph P :=
    ⟨D,one,(dominates_iff G D).mpr dom⟩
  obtain ⟨P,sz,h⟩ := Nat.sInf_mem (s:={k | ∃ P : Finset G.edgeSet, P.card=k ∧ Dominates G.lineGraph P})
    ⟨1,feasible⟩
  exact le_antisymm (Nat.sInf_le feasible) ((positive P ((dominates_iff G P).mp h)).trans_eq sz)

theorem claw_values : IsolateFree claw ∧ edgeCoverNumber claw = 3 ∧ lineDomination claw = 1 :=
  ⟨by unfold IsolateFree; decide,cover_check _ _ (by decide) (by decide),
    dom_check _ (by decide) (by decide)⟩

theorem bull_values : IsolateFree bull ∧ edgeCoverNumber bull = 3 ∧ lineDomination bull = 1 :=
  ⟨by unfold IsolateFree; decide,cover_check _ _ (by decide) (by decide),
    dom_check _ (by decide) (by decide)⟩

theorem triangle_values : IsolateFree triangle ∧ edgeCoverNumber triangle = 2 ∧ lineDomination triangle = 1 :=
  ⟨by unfold IsolateFree; decide,cover_check _ _ (by decide) (by decide),
    dom_check _ (by decide) (by decide)⟩

/-- Quantifying over all finite induced copies (using Fin labels) is the
hereditary version of the numeric inequality, restricted to its domain. -/
def Hereditary {V : Type*} (G : SimpleGraph V) :=
  ∀ (n : ℕ) (H : SimpleGraph (Fin n)), Nonempty (H ↪g G) → IsolateFree H →
    edgeCoverNumber H ≤ 2*lineDomination H

theorem hereditary_iff {V : Type*} (G : SimpleGraph V) :
    Hereditary G ↔ Free G claw ∧ Free G bull := by
  constructor
  · intro h
    constructor
    · intro e
      obtain ⟨dom,ec,ld⟩ := claw_values
      have invalid := h 4 claw e dom
      omega
    · intro e
      obtain ⟨dom,ec,ld⟩ := bull_values
      have invalid := h 5 bull e dom
      omega
  · rintro ⟨hc,hb⟩ n J ⟨emb⟩ noIso
    exact bound J noIso (free_subgraph hc emb) (free_subgraph hb emb)

theorem row_sharp : 2 ≤ Fintype.card (Fin 3) ∧ Free triangle claw ∧
    ¬ Graffiti137.InducedPath triangle 4 ∧ edgeCoverValue triangle = some 2 ∧
    lineDomination triangle = 1 := by
  classical
  obtain ⟨iso,c,d⟩ := triangle_values
  refine ⟨by decide,?_,?_,by simp [edgeCoverValue,iso,c],d⟩
  · rintro ⟨f⟩
    have small := Fintype.card_le_of_injective _ f.injective
    norm_num at small
  · rintro ⟨f,_⟩
    have small := Fintype.card_le_of_injective _ f.injective
    norm_num at small

#print axioms coverable_iff
#print axioms cover_from_domination
#print axioms bound
#print axioms row1125
#print axioms claw_values
#print axioms bull_values
#print axioms hereditary_iff
#print axioms row_sharp
end BullCover1125
