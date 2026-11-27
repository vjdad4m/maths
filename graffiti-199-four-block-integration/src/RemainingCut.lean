import MainGraphBridges

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The crossing law used in the archived minimum-counterexample proof.
The two witnesses are entire surviving edges on opposite sides of a vertex set. -/
def CrossingBetweenSurvivingEdges (G : SimpleGraph V) : Prop :=
  ∀ (D : Finset V), D.card ≤ 3 → ∀ U : Set V,
    (∃ a ∈ U, ∃ b ∈ U, a ∉ D ∧ b ∉ D ∧ G.Adj a b) →
    (∃ c ∉ U, ∃ d ∉ U, c ∉ D ∧ d ∉ D ∧ G.Adj c d) →
    ∃ x ∈ U, ∃ y ∉ U, x ∉ D ∧ y ∉ D ∧ G.Adj x y

/-- The archived crossing law is precisely the edge-to-edge reachability
needed by the standalone splice. Choose a reachable shore for the reverse
implication. -/
theorem edgeReach_iff_crossing_between_surviving_edges :
    EdgeReachAfterSmallDeletion G ↔ CrossingBetweenSurvivingEdges G := by
  constructor
  · intro reach D size U
    rintro ⟨a,aU,b,_,aD,bD,ab⟩ ⟨c,cU,d,_,cD,dD,cd⟩
    exact crossingAfterSmallDeletion reach size aU cU aD bD cD dD ab cd
  · intro cross D size a b c d ab cd
    by_contra no
    let H := G.induce {v | v ∉ D}
    let U : Set V := {v | ∃ keep : v ∉ D, H.Reachable a ⟨v,keep⟩}
    have cOff : c.val ∉ U := fun ⟨_,h⟩ => no h
    have dOff : d.val ∉ U := fun ⟨_,h⟩ =>
      no (h.trans (show H.Adj d c from G.symm cd).reachable)
    obtain ⟨x,⟨xD,ax⟩,y,yOff,_,yD,xy⟩ := cross D size U
      ⟨a.val,⟨a.property,.rfl⟩,b.val,⟨b.property,(show H.Adj a b from ab).reachable⟩,
        a.property,b.property,ab⟩
      ⟨c.val,cOff,d.val,dOff,c.property,d.property,cd⟩
    exact yOff ⟨yD,ax.trans (show H.Adj ⟨x,xD⟩ ⟨y,yD⟩ from xy).reachable⟩

#print axioms edgeReach_iff_crossing_between_surviving_edges

end Graffiti199Depleted
