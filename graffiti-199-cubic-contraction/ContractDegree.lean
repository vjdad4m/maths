import MinimumContraction

namespace Graffiti199Depleted.ContractedEdge

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} (E : ContractedEdge G)

variable [DecidableRel G.Adj] in
instance graphAdjDecidable : DecidableRel E.graph.Adj := by
  intro x y
  rcases x with (_|x) <;> rcases y with (_|y)
  · change Decidable False
    infer_instance
  · change Decidable (G.Adj E.a y.val ∨ G.Adj E.b y.val)
    infer_instance
  · change Decidable (G.Adj E.a x.val ∨ G.Adj E.b x.val)
    infer_instance
  · exact ‹DecidableRel G.Adj› x.val y.val

variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/-- No outside vertex loses degree when an edge with no common
neighbor is contracted. -/
theorem degree_other (w : E.Other)
    (noCommon : ∀ x, ¬ (G.Adj x E.a ∧ G.Adj x E.b)) :
    E.graph.degree (some w) = G.degree w.val := by
  classical
  let A := G.neighborSet w.val
  let B := E.graph.neighborSet (some w)
  have maps (z : (↑A : Set V)) : E.graph.Adj (some w) (E.project z.val) := by
    have edge : G.Adj w.val z.val := z.property
    by_cases za : z.val = E.a
    · rw [za,E.project_a]
      exact Or.inl (Eq.mp (congrArg (fun t : V => G.Adj t w.val) za) edge.symm)
    · by_cases zb : z.val = E.b
      · rw [zb,E.project_b]
        exact Or.inr (Eq.mp (congrArg (fun t : V => G.Adj t w.val) zb) edge.symm)
      · rw [E.project_of_other _ ⟨za,zb⟩]
        exact edge
  let f : (↑A : Set V) → (↑B : Set E.Vertex) := fun z => ⟨E.project z.val,maps z⟩
  have injective : Function.Injective f := by
    intro x y e
    have h : E.project x.val = E.project y.val := congrArg Subtype.val e
    by_cases xb : x.val = E.b
    · have yn : E.project y.val = none := by simpa [xb] using h.symm
      rcases (E.project_none_iff _).mp yn with ya|yb
      · have ex : G.Adj w.val E.b := Eq.mp (congrArg (G.Adj w.val) xb) x.property
        have ey : G.Adj w.val E.a := Eq.mp (congrArg (G.Adj w.val) ya) y.property
        exact (noCommon w.val ⟨ey,ex⟩).elim
      · exact Subtype.ext (xb.trans yb.symm)
    · by_cases yb : y.val = E.b
      · have xn : E.project x.val = none := by simpa [yb] using h
        rcases (E.project_none_iff _).mp xn with xa|xb'
        · have ex : G.Adj w.val E.a := Eq.mp (congrArg (G.Adj w.val) xa) x.property
          have ey : G.Adj w.val E.b := Eq.mp (congrArg (G.Adj w.val) yb) y.property
          exact (noCommon w.val ⟨ex,ey⟩).elim
        · exact (xb xb').elim
      · apply Subtype.ext
        simpa only [E.rep_project _ xb,E.rep_project _ yb] using congrArg E.representative h
  have surj : Function.Surjective f := by
    rintro ⟨z,hz⟩
    cases z with
    | none =>
      rcases (show G.Adj E.a w.val ∨ G.Adj E.b w.val from hz) with ha|hb
      · exact ⟨⟨E.a,ha.symm⟩,Subtype.ext E.project_a⟩
      · exact ⟨⟨E.b,hb.symm⟩,Subtype.ext E.project_b⟩
    | some z => exact ⟨⟨z.val,hz⟩,Subtype.ext (E.project_of_other _ z.property)⟩
  have equal := Fintype.card_congr (Equiv.ofBijective f ⟨injective,surj⟩)
  change Fintype.card (G.neighborSet w.val) = Fintype.card (E.graph.neighborSet (some w)) at equal
  rw [G.card_neighborSet_eq_degree,E.graph.card_neighborSet_eq_degree] at equal
  exact equal.symm

/-- A surviving cubic vertex keeps the contraction in the exact
connectivity-three class. -/
theorem contraction_connectivity_eq_three
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G) (order : 5 ≤ Fintype.card V)
    (noCommon : ∀ x, ¬ (G.Adj x E.a ∧ G.Adj x E.b))
    (w : E.Other) (cubic : G.degree w.val = 3) :
    Catalogue.vertexConnectivity E.graph = 3 := by
  classical
  have k3 := E.connectivityAtLeast_three conn cross order noCommon
  apply Nat.le_antisymm
  · by_contra! large
    let K := E.graph
    change 3 < Catalogue.vertexConnectivity K at large
    let t : E.Vertex := some w
    let D := K.neighborFinset t
    have card : D.card = 3 := (K.card_neighborFinset_eq_degree _).trans ((E.degree_other w noCommon).trans cubic)
    letI : Nonempty E.Vertex := ⟨none⟩
    have all := Catalogue.connectivityAtLeast_vertexConnectivity (G := K)
    have keep : t ∉ D := K.not_mem_neighborFinset_self t
    have room : (insert t D).card < (Finset.univ : Finset E.Vertex).card := by
      rw [Finset.card_insert_of_not_mem keep,card,Finset.card_univ]
      have size := all.1
      omega
    obtain ⟨y,_,yOff⟩ := Finset.exists_mem_not_mem_of_card_lt_card room
    let S : Set E.Vertex := {v | v ∉ D}
    let x : S := ⟨t,keep⟩
    let z : S := ⟨y,fun h => yOff (Finset.mem_insert_of_mem h)⟩
    have iso (p : S) : ¬ (K.induce S).Adj x p := fun e =>
      p.property ((K.mem_neighborFinset _ _).mpr e)
    have reach : (K.induce S).Reachable x z := (all.2 D (by omega)).preconnected x z
    obtain ⟨p⟩ := reach
    have same {q : S} (w : (K.induce S).Walk x q) : x = q := by
      cases w with
      | nil => rfl
      | cons h _ => exact (iso _ h).elim
    have eq : t = y := congrArg Subtype.val (same p)
    exact yOff (eq ▸ Finset.mem_insert_self _ _)
  · unfold Catalogue.vertexConnectivity
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k3.1,k3⟩)

/-- A minimum taken only among the exact-connectivity-three graphs
also supplies a spanning path for the contraction if a cubic vertex
survives outside the edge. -/
theorem contraction_traceable_of_exact_three_minimum
    (smaller : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      Fintype.card W < Fintype.card V → Catalogue.vertexConnectivity H = 3 →
      Catalogue.treeNumber H ≤ 5 → Catalogue.Traceable H)
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G) (order : 5 ≤ Fintype.card V)
    (budget : Catalogue.treeNumber G ≤ 5)
    (noCommon : ∀ x, ¬ (G.Adj x E.a ∧ G.Adj x E.b))
    (w : E.Other) (cubic : G.degree w.val = 3) :
    Catalogue.Traceable E.graph := by
  have size := E.card_vertex
  exact smaller E.Vertex E.graph (by omega)
    (E.contraction_connectivity_eq_three conn cross order noCommon w cubic)
    ((E.treeNumber_le noCommon).trans budget)

#print axioms degree_other
#print axioms contraction_connectivity_eq_three
#print axioms contraction_traceable_of_exact_three_minimum

end Graffiti199Depleted.ContractedEdge
