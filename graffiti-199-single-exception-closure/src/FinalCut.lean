import CatalogueSingleClosed
import TwoMissMatching

namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A port of a cut in this minimum-order branch misses at least two ordinary
vertices. If its misses are exactly an adjacent pair, the pair has no matching
into the other two ports. All assertions hold for every ordering of every
separating three-set. -/
theorem catalogue_minimum_misses_and_matching
    (minimum : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W), Fintype.card W < Fintype.card V →
      H.Connected → 2 ≤ Fintype.card W → treeNumber H ≤ vertexConnectivity H + 2 → Traceable H)
    (k : vertexConnectivity G = 3) (bound : treeNumber G ≤ vertexConnectivity G + 2)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ u v, G.degree u = 3 → G.degree v = 3 → ¬ G.Adj u v) :
    (∃ D : Finset V, D.card = 3 ∧ ¬ (DeletionGraph G D).Preconnected) ∧
    ∀ D : Finset V, D.card = 3 → ¬ (DeletionGraph G D).Preconnected →
      ∃ z : V, ∃ X : Set V, ∃ P : PathOn G {v | v ≠ z},
      ∀ r a b : V, r ≠ a → r ≠ b → a ≠ b → D = {r,a,b} →
        SingletonCut G X z r a b ∧ SaturatedPort G X r a b ∧
        (P.terminalQuartet.card = 4 ∧ (∀ v ∈ P.terminalQuartet, v ∈ X) ∧
          (∀ v ∈ P.terminalQuartet, ∀ w ∈ P.terminalQuartet, ¬ G.Adj v w) ∧
          ∀ s ∈ D, ∃ v ∈ P.terminalQuartet, ¬ G.Adj s v) ∧ MissesTwo G X r ∧
        ∀ x ∈ X, ∀ y ∈ X, G.Adj x y → ¬ G.Adj r x → ¬ G.Adj r y →
          (∀ t ∈ X \ {x,y}, G.Adj r t) →
          ¬ ((G.Adj x a ∧ G.Adj y b) ∨ (G.Adj y a ∧ G.Adj x b)) := by
  obtain ⟨existsCut,every⟩ := catalogue_minimum_all_ports_miss_two minimum k bound order no ind
  refine ⟨existsCut,?_⟩
  intro D size cut
  obtain ⟨z,X,P,all⟩ := every D size cut
  refine ⟨z,X,P,?_⟩
  intro r a b ra rb ab eq
  obtain ⟨F,sat,quart,miss⟩ := all r a b ra rb ab eq
  refine ⟨F,sat,quart,miss,?_⟩
  rintro x xX y yX xy rx ry on (⟨xa,yb⟩|⟨ya,xb⟩)
  · exact no (F.traceable_of_matched_two_misses xX yX xy rx ry on xa yb)
  · exact no (F.traceable_of_matched_two_misses yX xX xy.symm ry rx ((Set.pair_comm x y) ▸ on) ya xb)

#print axioms catalogue_minimum_misses_and_matching
end Graffiti199Depleted.Catalogue.Incomplete
