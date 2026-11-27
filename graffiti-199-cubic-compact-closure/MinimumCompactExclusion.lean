import CompactClosure

open private three_names_exhaust_neighbors from DepletedFootprint

namespace Graffiti199Depleted

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

namespace CompactOmission

omit [DecidableEq V] in
private theorem cubic_contact_is_slot (f : Fin 8 ↪ V)
    (dz : G.degree (f 7) = 3)
    (z1 : G.Adj (f 7) (f 1)) (z3 : G.Adj (f 7) (f 3)) (z5 : G.Adj (f 7) (f 5))
    {w : V} (zw : G.Adj (f 7) w) (dw : G.degree w = 3) :
    G.degree (f 1) = 3 ∨ G.degree (f 3) = 3 ∨ G.degree (f 5) = 3 := by
  obtain ⟨i,hi,eq⟩ := three_names_exhaust_neighbors f (by decide) (by decide) (by decide) dz
    z1 z3 z5 w zw
  rcases (show i = 1 ∨ i = 3 ∨ i = 5 from by simpa using hi) with rfl|rfl|rfl
  · exact Or.inl (eq.symm ▸ dw)
  · exact Or.inr (Or.inl (eq.symm ▸ dw))
  · exact Or.inr (Or.inr (eq.symm ▸ dw))

/-- An omitted cubic vertex with a cubic neighbor cannot have its three
independent neighbors at alternate positions in a seven-vertex block
of any spanning path of the vertex deletion, in a nontraceable graph
with induced-tree number at most five. -/
theorem no_compact_placement (budget : Catalogue.treeNumber G ≤ 5)
    (noTrace : ¬ Catalogue.Traceable G) {z w : V}
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w)
    (p : PathOn G {v | v ≠ z}) (f : Fin 8 ↪ V) (fZ : f 7 = z)
    (L R : List V) (split : p.vertices = L ++ middle f ++ R)
    (z1 : G.Adj z (f 1)) (z3 : G.Adj z (f 3)) (z5 : G.Adj z (f 5))
    (off13 : ¬ G.Adj (f 1) (f 3)) (off15 : ¬ G.Adj (f 1) (f 5))
    (off35 : ¬ G.Adj (f 3) (f 5)) : False := by
  subst z
  exact noTrace (traceable_of_compact_cubic_omission budget f p L R split z1 z3 z5
    off13 off15 off35 dz (cubic_contact_is_slot f dz z1 z3 z5 zw dw))

end CompactOmission

namespace ContractedEdge

/-- The omission forced by a cubic edge in the minimum-order reduction
also rules out the compact placement on every one-omission path with
the given omitted vertex. -/
theorem minimum_cubic_edge_noncompact_omission (E : ContractedEdge G)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G) (budget : Catalogue.treeNumber G ≤ 5)
    (order : 10 ≤ Fintype.card V) (da : G.degree E.a = 3) (db : G.degree E.b = 3)
    (noTrace : ¬ Catalogue.Traceable G) :
    ∃ z, (z = E.a ∨ z = E.b) ∧ (∃ p : PathOn G {v | v ≠ z}, ConstrainedOmission z p) ∧
      ∀ (q : PathOn G {v | v ≠ z}) (f : Fin 8 ↪ V), f 7 = z →
        ∀ L R : List V, q.vertices = L ++ CompactOmission.middle f ++ R →
          G.Adj z (f 1) → G.Adj z (f 3) → G.Adj z (f 5) →
          ¬ G.Adj (f 1) (f 3) → ¬ G.Adj (f 1) (f 5) → ¬ G.Adj (f 3) (f 5) → False := by
  obtain ⟨z,atEnd,p,constrained⟩ :=
    E.minimum_cubic_edge_constrained_omission smaller conn cross budget order da db noTrace
  refine ⟨z,atEnd,⟨p,constrained⟩,?_⟩
  rcases atEnd with h|h
  · subst z
    exact CompactOmission.no_compact_placement budget noTrace da db E.edge
  · subst z
    exact CompactOmission.no_compact_placement budget noTrace db da E.edge.symm

end ContractedEdge

#print axioms CompactOmission.no_compact_placement
#print axioms ContractedEdge.minimum_cubic_edge_noncompact_omission

end Graffiti199Depleted
