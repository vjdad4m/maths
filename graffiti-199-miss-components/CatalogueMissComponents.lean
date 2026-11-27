import SplitEdgeClosed
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- All missed vertices are isolated in the induced graph, except possibly
the members of a single connected component. The remaining fields describe
the attachments and internal structure of that possible component. -/
structure MissComponentProfile (G : SimpleGraph V) (X : Set V) (r : V) : Prop where
  unique : ∀ i j : RootComponent G X r, 2 ≤ Nat.card (MissPart G X r i) →
    2 ≤ Nat.card (MissPart G X r j) → i = j
  uniformPair : ∀ i : RootComponent G X r, 2 ≤ Nat.card (MissPart G X r i) →
    UniformMissPart G X r i → Nat.card (MissPart G X r i) = 2 ∧ CubicContactPair G X r i
  noncliqueDisjoint : ∀ i : RootComponent G X r, ¬ (MissPart G X r i).Pairwise G.Adj →
    ∀ j k : RootComponent G X r, j ≠ k →
      Disjoint (rootedBlockContacts G X r j) (rootedBlockContacts G X r k)
  cubicContact : ∀ i : RootComponent G X r, CubicContactPair G X r i →
    ∀ j : RootComponent G X r, i ≠ j → rootedBlockContacts G X r j ⊆ rootedBlockContacts G X r i
  nestedUniform : ∀ (i : RootComponent G X r) (p : V), p ∈ rootedBlockContacts G X r i →
    ∀ j : RootComponent G (MissPart G X r i) p, UniformMissPart G (MissPart G X r i) p j

/-- Exact minimum-order catalogue assumptions, specialized to connectivity
three and independent cubic vertices. The previous three-miss and path
certificates and the new component profile hold for the same shore. -/
theorem catalogue_minimum_miss_component_profile
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
          ∀ s ∈ D, ∃ v ∈ P.terminalQuartet, ¬ G.Adj s v) ∧
        (∃ T : Finset V, T.card = 3 ∧ ∀ v ∈ T, v ∈ Noncontacts G X r) ∧
        MissComponentProfile G X r := by
  obtain ⟨sep,every⟩ := catalogue_minimum_all_ports_miss_three minimum k bound order no ind
  refine ⟨sep,?_⟩
  intro D size cut
  obtain ⟨z,X,P,all⟩ := every D size cut
  refine ⟨z,X,P,?_⟩
  intro r a b ra rb ab eq
  obtain ⟨F,sat,quart,three⟩ := all r a b ra rb ab eq
  have cross := catalogue_minimum_crossing minimum F.conn F.budget order no ind
  have smaller := smallerAtThree_of_catalogue_minimum minimum
  exact ⟨F,sat,quart,three,
    ⟨fun _ _ => F.nonsingleton_unique smaller order cross no ind,
      fun _ large good => F.uniform_nonsingleton_has_cubic_contact smaller order cross no ind three good large,
      fun _ nc _ _ ne => F.contacts_disjoint_of_nonclique nc ne,
      fun _ hub _ ne _ => F.cubic_contact_absorbs hub ne,
      fun _ _ pi => (F.nested_cliques pi).1⟩⟩

#print axioms catalogue_minimum_miss_component_profile
end Graffiti199Depleted.Catalogue.Incomplete
