import FlankEndpoint
import CubicMatePositions

namespace Graffiti199Depleted.ContractedEdge

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} (E : ContractedEdge G)
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

/-- The omission obtained from a cubic edge in a minimum-order
counterexample admits the flank restrictions in both orientations,
and in fact on every path with that same omission. -/
theorem minimum_cubic_edge_flank_profile
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card V)
    (da : G.degree E.a = 3) (db : G.degree E.b = 3)
    (noTrace : ¬ Catalogue.Traceable G) :
    ∃ z : V, (z = E.a ∨ z = E.b) ∧ Nonempty (PathOn G {v | v ≠ z}) ∧
      ∀ p : PathOn G {v | v ≠ z},
        ((insert z p.terminalFlanks).card = 5 ∧
          ∀ x ∈ insert z p.terminalFlanks, ∀ y ∈ insert z p.terminalFlanks, ¬ G.Adj x y) ∧
        (∀ A : Finset V, A ⊆ G.neighborFinset z →
          (∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) → A.card + (p.uniqueAttachments A).card ≤ 4) ∧
        (NoIndependentSix G →
          ∃ x ∈ p.predecessors, x ∉ p.rev.predecessors ∧ (x = p.first ∨ G.Adj p.first x)) := by
  obtain ⟨z,endAt,p,_⟩ :=
    E.minimum_cubic_edge_constrained_omission smaller conn cross budget order da db noTrace
  have degree : G.degree z = 3 := endAt.elim (fun eq => eq.symm ▸ da) (fun eq => eq.symm ▸ db)
  refine ⟨z,endAt,⟨p⟩,fun q => ⟨?_,q.unique_attachment_bound noTrace budget,?_⟩⟩
  · simpa only [degree] using q.omitted_and_terminalFlanks_independent noTrace
  · intro noSix
    exact q.initial_reaches_exclusive_predecessor noTrace noSix degree

#print axioms minimum_cubic_edge_flank_profile

end Graffiti199Depleted.ContractedEdge
