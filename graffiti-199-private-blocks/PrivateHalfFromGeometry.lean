import RootedBlocks
import ExceptionalHalf

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] {X : Set V} {r : V}

/-- In the exceptional configuration, derive every edge needed for the
half-path from the actual private contact and rooted-tree obstruction. -/
theorem NoRootedFour.private_component_half
    (none : NoRootedFour G X r) (rOff : r ∉ X)
    (c : (G.induce (Noncontacts G X r)).ConnectedComponent)
    {P : Set V} {x t : V}
    (privateContact : x ∈ rootedBlockContacts G X r c)
    (unique : ∀ q ∈ rootedBlockContacts G X r c, q = x)
    (cliqueResidual : P.Pairwise G.Adj) (residual : P.Nonempty)
    (residualContacts : P ⊆ shoreContacts G X r) (xOff : x ∉ P)
    (tC : t ∈ noncontactComponent G X r c) :
    ∃ z ∈ P, G.Adj r z ∧ Traverses G ((P ∪ {x}) ∪ noncontactComponent G X r c) z t := by
  obtain ⟨xX,rx,u,uC,xu⟩ := privateContact
  have comp (v : V) (hv : v ∈ noncontactComponent G X r c) :
      v ∈ Noncontacts G X r := by
    obtain ⟨v,_,rfl⟩ := hv
    exact v.property
  have apart : Disjoint P (noncontactComponent G X r c) :=
    Set.disjoint_left.mpr (by
      intro v hv hc
      exact (comp v hc).2 (residualContacts hv).2)
  have xC : x ∉ noncontactComponent G X r c := fun h => (comp _ h).2 rx
  have xToP (q : V) (hq : q ∈ P) : G.Adj x q := by
    have ⟨qX,rq⟩ := residualContacts hq
    have miss : ¬ G.Adj q u :=
      fun edge => xOff ((unique _ ⟨qX,rq,u,uC,edge⟩) ▸ hq)
    exact none.cross_contacts_complete rOff xX qX (comp _ uC) rx rq xu miss
  have xToC (v : V) (hv : v ∈ noncontactComponent G X r c) : G.Adj x v :=
    none.contact_common_on_component rOff c xX rx uC hv xu
  obtain ⟨z,hz,route⟩ := private_clique_half_traversal cliqueResidual
    (none.clique_of_contact rOff c xX rx uC xu) residual tC apart xOff xC xToP xToC
  exact ⟨z,hz,(residualContacts hz).2,route⟩

/-- Two independent contacts on one side leave room for at most two
independent vertices on a side complete to that same port. -/
theorem card_independent_other_shore_le_two_of_complete_port [DecidableEq V]
    {D : Finset V} {Y : Set V} {a : V} (ha : a ∈ D)
    (budget : treeNumber G ≤ 5) (offX : ∀ v ∈ D, v ∉ X) (offY : ∀ v ∈ D, v ∉ Y)
    (boundX : ShoreBoundary G D X) (apart : Disjoint X Y)
    (complete : ∀ v ∈ Y, G.Adj a v)
    (U T : Finset V) (two : 2 ≤ U.card)
    (contacts : ∀ u ∈ U, u ∈ shoreContacts G X a) (side : ∀ t ∈ T, t ∈ Y)
    (indU : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v)
    (indT : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) : T.card ≤ 2 := by
  have cap := card_independent_shore_contacts_le_four budget offX offY boundX apart ha U T ∅
    contacts (fun t ht => ⟨side _ ht,complete _ (side _ ht)⟩)
      indU indT (by simp)
  omega

#print axioms NoRootedFour.private_component_half
#print axioms card_independent_other_shore_le_two_of_complete_port

end Graffiti199Depleted.Catalogue
