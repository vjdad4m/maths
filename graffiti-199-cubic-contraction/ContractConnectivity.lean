import ContractEdge

namespace Graffiti199Depleted

open SimpleGraph

variable {X Y : Type*} {A : SimpleGraph X} {B : SimpleGraph Y}

private theorem reachable_map_or_eq (f : X → Y)
    (edge : ∀ ⦃x y⦄, A.Adj x y → B.Adj (f x) (f y) ∨ f x = f y)
    {x y : X} (reach : A.Reachable x y) : B.Reachable (f x) (f y) := by
  obtain ⟨w⟩ := reach
  induction w with
  | nil => exact .rfl
  | cons adj _ ih =>
    rcases edge adj with e|e
    · exact e.reachable.trans ih
    · exact e.symm ▸ ih

namespace ContractedEdge

variable {V : Type*} {G : SimpleGraph V} (E : ContractedEdge G)
variable [DecidableEq V]

private def deletion (D : Finset E.Vertex) : Finset V :=
  if none ∈ D then insert E.b (D.map E.representative) else D.map E.representative

private theorem mem_deletion (D : Finset E.Vertex) (x : V) :
    x ∈ E.deletion D ↔ E.project x ∈ D := by
  by_cases xb : x = E.b
  · subst x
    have bOff : E.b ∉ D.map E.representative := by
      rintro h
      obtain ⟨y,_,eq⟩ := Finset.mem_map.mp h
      exact E.rep_ne_b y eq
    by_cases dn : none ∈ D <;> simp [deletion,dn,bOff]
  · have exactMap : x ∈ D.map E.representative ↔ E.project x ∈ D := by
      constructor
      · rintro h
        obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp h
        simpa using hz
      · intro h
        exact Finset.mem_map.mpr ⟨_,h,E.rep_project _ xb⟩
    by_cases dn : none ∈ D
    · simpa [deletion,dn,xb] using exactMap
    · simpa [deletion,dn] using exactMap

private theorem deletion_le (D : Finset E.Vertex) : (E.deletion D).card ≤ D.card + 1 := by
  unfold deletion
  split
  · exact (Finset.card_insert_le _ _).trans_eq (by rw [Finset.card_map])
  · rw [Finset.card_map]
    omega

variable [Fintype V] [DecidableRel G.Adj]

/-- Contracting an edge outside every triangle preserves
three-connectivity in the archived cut case. A three-deletion
lifted from a smaller deletion necessarily removes both ends, so
any isolated survivor would give a common neighbor of the ends. -/
theorem connectivityAtLeast_three
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G)
    (order : 5 ≤ Fintype.card V)
    (noCommon : ∀ x, ¬ (G.Adj x E.a ∧ G.Adj x E.b)) :
    Catalogue.ConnectivityAtLeast E.graph 3 := by
  have size := E.card_vertex
  have more : 3 < Fintype.card E.Vertex := by omega
  refine ⟨more,?_⟩
  intro D small
  let R := E.deletion D
  have rsmall : R.card ≤ 3 := (E.deletion_le D).trans (by omega)
  let S : Set V := {x | x ∉ R}
  let T : Set E.Vertex := {x | x ∉ D}
  let f : S → T := fun x =>
    ⟨E.project x.val,fun h => x.property ((E.mem_deletion D _).mpr h)⟩
  let g : T → S := fun x =>
    ⟨E.representative x.val,fun h => x.property (by
      simpa using (E.mem_deletion D _).mp h)⟩
  have right (x : T) : f (g x) = x := Subtype.ext (E.project_rep _)
  have reach : (G.induce S).Preconnected := by
    by_cases fewer : R.card < 3
    · exact (conn.2 R fewer).preconnected
    · have exactSize : R.card = 3 := by omega
      have dn : none ∈ D := by
        by_contra h
        have count : R.card = D.card := by simp [R,deletion,h]
        omega
      have aR : E.a ∈ R := (E.mem_deletion D _).mpr (by simpa using dn)
      have bR : E.b ∈ R := (E.mem_deletion D _).mpr (by simpa using dn)
      have neighbor (x : S) : ∃ y : S, G.Adj x.val y.val := by
        by_contra! absent
        have sub : G.neighborFinset x.val ⊆ R := by
          intro y hy
          by_contra keep
          exact absent ⟨y,keep⟩ ((G.mem_neighborFinset _ _).mp hy)
        have min := degree_of_small_deletion_preconnected (G := G) (by omega)
          (fun L lt => (conn.2 L lt).preconnected) x.val
        have eq := Finset.eq_of_subset_of_card_le sub (by
          rw [G.card_neighborFinset_eq_degree, exactSize]
          exact min)
        exact noCommon x.val ⟨(G.mem_neighborFinset _ _).mp (eq.symm ▸ aR),
          (G.mem_neighborFinset _ _).mp (eq.symm ▸ bR)⟩
      intro x y
      obtain ⟨a,xa⟩ := neighbor x
      obtain ⟨b,yb⟩ := neighbor y
      exact edgeReach_iff_crossing_between_surviving_edges.mpr cross R rsmall x a y b xa yb
  have pc : (E.graph.induce T).Preconnected := by
    intro x y
    have edges {v w : S} (h : (G.induce S).Adj v w) :
        (E.graph.induce T).Adj (f v) (f w) ∨ f v = f w :=
      (E.project_adj_or_eq h).imp id Subtype.ext
    simpa only [right] using reachable_map_or_eq (A := G.induce S) (B := E.graph.induce T) f
      (fun {v w} h => edges (v := v) (w := w) h) (reach (g x) (g y))
  have proper : D.card < (Finset.univ : Finset E.Vertex).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨x,_,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card proper
  exact @SimpleGraph.Connected.mk _ (E.graph.induce T) pc ⟨⟨x,off⟩⟩

#print axioms connectivityAtLeast_three

end ContractedEdge

end Graffiti199Depleted
