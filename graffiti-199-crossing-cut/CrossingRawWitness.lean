import CutTorsoBudget

open private triangle_absurd from CutTorsoBudget

namespace Graffiti199Depleted.Catalogue.CrossingRawWitness

open SimpleGraph

private def block (x : Fin 8) : ℕ :=
  if x.val < 3 then 0 else if x.val < 5 then 1 else if x.val < 7 then 2 else 3

/-- A triangle of ports joined to two disjoint edges and a singleton. -/
def graph : SimpleGraph (Fin 8) where
  Adj x y := x ≠ y ∧ (block x = 0 ∨ block y = 0 ∨ block x = block y)
  symm := by
    rintro x y ⟨ne,edge|edge|edge⟩
    · exact ⟨ne.symm,Or.inr (Or.inl edge)⟩
    · exact ⟨ne.symm,Or.inl edge⟩
    · exact ⟨ne.symm,Or.inr (Or.inr edge.symm)⟩
  loopless := by intro x h; exact h.1 rfl

instance graphAdjDecidable : DecidableRel graph.Adj := by
  intro x y
  change Decidable (x ≠ y ∧ (block x = 0 ∨ block y = 0 ∨ block x = block y))
  infer_instance

private def ports : Finset (Fin 8) := {0,1,2}

theorem connectivity : ConnectivityAtLeast graph 3 := by
  refine ⟨by decide,?_⟩
  intro D small
  obtain ⟨p,hp,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (show D.card < ports.card from (show ports.card = 3 by decide).symm ▸ small)
  let P : {v : Fin 8 // v ∉ D} := ⟨p,off⟩
  have hub : block p = 0 := (show ∀ x ∈ ports, block x = 0 from by decide) p hp
  refine @SimpleGraph.Connected.mk _ (graph.induce {v : Fin 8 | v ∉ D}) ?_ ⟨P⟩
  intro x y
  have attach (x : {v : Fin 8 // v ∉ D}) :
      (graph.induce {v : Fin 8 | v ∉ D}).Reachable x P := by
    by_cases eq : x.val = p
    · exact (show x = P from Subtype.ext eq) ▸ .rfl
    · exact (show (graph.induce {v : Fin 8 | v ∉ D}).Adj x P from ⟨eq,Or.inr (Or.inl hub)⟩).reachable
  exact (attach x).trans (attach y).symm

theorem no_crossing : ¬ CrossingBetweenSurvivingEdges graph := by
  intro cross
  let U : Set (Fin 8) := {3,4}
  have banned : ∀ x y : Fin 8, x ∈ U → y ∉ U → y ∉ ports → ¬ graph.Adj x y := by
    decide
  obtain ⟨x,xU,y,yU,_,yD,xy⟩ := cross ports (by decide) U
    ⟨3,by simp [U],4,by simp [U],by decide,by decide,by decide⟩
    ⟨5,by decide,6,by decide,by decide,by decide,by decide⟩
  exact banned x y xU yU yD xy

theorem exact_connectivity : vertexConnectivity graph = 3 := by
  classical
  have ge : 3 ≤ vertexConnectivity graph := by
    unfold vertexConnectivity
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by decide),connectivity⟩)
  have le : vertexConnectivity graph ≤ 3 := by
    by_contra! h
    apply no_crossing
    apply edgeReach_iff_crossing_between_surviving_edges.mp
    intro D small a _ c _ _ _
    exact ((connectivityAtLeast_vertexConnectivity (G := graph)).2 D (by omega)).preconnected a c
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4500000 in
private theorem large_triangle :
    ∀ S : Finset (Fin 8), 6 ≤ S.card →
      ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, graph.Adj a b ∧ graph.Adj a c ∧ graph.Adj c b := by
  decide +kernel

theorem budget : treeNumber graph ≤ 5 := by
  classical
  unfold treeNumber
  apply Finset.sup_le
  intro S h
  change S.card ≤ 5
  by_cases high : 6 ≤ S.card
  · obtain ⟨a,aS,b,bS,c,cS,ab,ac,cb⟩ := large_triangle S high
    let H := graph.induce (↑S : Set (Fin 8))
    have tree : H.IsTree := (Finset.mem_filter.mp h).2
    exact (triangle_absurd tree
      (show H.Adj ⟨a,aS⟩ ⟨b,bS⟩ from ab) (show H.Adj ⟨a,aS⟩ ⟨c,cS⟩ from ac)
      (show H.Adj ⟨c,cS⟩ ⟨b,bS⟩ from cb)).elim
  · omega

theorem sole_cubic : ∀ x : Fin 8, graph.degree x = 3 ↔ x = 7 := by
  decide +kernel

theorem independent_cubics : ∀ a b, graph.degree a = 3 → graph.degree b = 3 → ¬ graph.Adj a b := by
  intro a b ha hb
  have ea := (sole_cubic a).mp ha
  have eb := (sole_cubic b).mp hb
  intro e
  rw [ea,eb] at e
  exact graph.loopless 7 e

theorem traceable : Traceable graph := by
  apply traceable_iff_hamiltonian_walk.mpr
  apply pathOn_univ_iff_hamiltonian_walk.mp
  refine ⟨⟨[7,0,3,4,1,5,6,2],by simp,by decide,by decide,?_⟩⟩
  intro v
  change v ∈ ([7,0,3,4,1,5,6,2] : List (Fin 8)) ↔ True
  fin_cases v <;> decide

#print axioms exact_connectivity
#print axioms no_crossing
#print axioms budget
#print axioms independent_cubics
#print axioms traceable

end Graffiti199Depleted.Catalogue.CrossingRawWitness
