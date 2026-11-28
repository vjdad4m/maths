import DegreeFiveEightActual189
import RootedOreTwoCandidates189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private left_boundary from AdjacentCut189
open private not_common from DegreeFiveFourPort189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

/-- A short shore with two or more specified cut-a contacts has a spanning
route from one of those contacts. Closing high pairs is local to the induced
shore and is transferred back before gluing. -/
theorem free_route_small_far_shore (far : 3≤G.dist a b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (sz : S.L.card≤8) (roots : 2≤S.localA.card) :
    ∃ u v,G.Adj a u ∧ RouteOn G S.L u v := by
  classical
  let U := ↑(↑S.L : Set V)
  let J := G.induce (↑S.L : Set V)
  let T := (univ : Finset U).filter (fun v=>G.Adj a v.val)
  have mapped : T.map (Function.Embedding.subtype (fun v : V=>v∈(↑S.L : Set V)))=S.localA := by
    ext v
    simp only [T,mem_map,mem_filter,mem_univ,true_and,Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨w,aw,rfl⟩
      exact mem_filter.mpr ⟨w.property,aw⟩
    intro h
    obtain ⟨vL,av⟩ := mem_filter.mp h
    exact ⟨⟨v,vL⟩,av,rfl⟩
  have root2 : 2≤T.card := by
    have h : (T.map (Function.Embedding.subtype (fun v : V=>v∈(↑S.L : Set V)))).card=S.localA.card := congrArg Finset.card mapped
    rw [card_map] at h
    omega
  have deg (u : U) (hi : 5≤G.degree u.val) : 4≤J.degree u := by
    have step (c : V) (sub : G.neighborFinset u.val⊆insert c (inside G S.L u.val)) :
        4≤(inside G S.L u.val).card := by
      have x := (card_le_card sub).trans (card_insert_le c (inside G S.L u.val))
      rw [card_neighborFinset_eq_degree] at x
      omega
    have high : 4≤(inside G S.L u.val).card := by
      by_cases bu : G.Adj b u.val
      · apply step b
        intro w wN
        have uw := (mem_neighborFinset G u.val w).mp wN
        rcases left_boundary S u.val u.property w uw with wa|wb|wL
        · exact (not_common far (wa ▸ uw.symm) bu).elim
        · exact mem_insert.mpr (.inl wb)
        exact mem_insert_of_mem (mem_filter.mpr ⟨wL,uw⟩)
      apply step a
      intro w wN
      have uw := (mem_neighborFinset G u.val w).mp wN
      rcases left_boundary S u.val u.property w uw with wa|wb|wL
      · exact mem_insert.mpr (.inl wa)
      · exact (bu (wb ▸ uw.symm)).elim
      exact mem_insert_of_mem (mem_filter.mpr ⟨wL,uw⟩)
    rwa [inside_card_eq_degree_induce (G:=G) S.L u] at high
  have low (x y : U) (ne : x≠y) : 5≤G.degree x.val ∨ 5≤G.degree y.val :=
    degree x.val y.val (fun e=>ne (Subtype.ext e))
  have ok (x y : U) (hx : 5≤G.degree x.val) (hy : 5≤G.degree y.val)
      (_ : x≠y) (_ : ¬J.Adj x y) : Fintype.card U≤J.degree x+J.degree y := by
    have n : Fintype.card U=S.L.card := Fintype.card_coe S.L
    have x4 := deg x hx
    have y4 := deg y hy
    omega
  obtain ⟨r,rT,t,p,hp,hs⟩ := rooted_Ore_from_two_candidates S.leftConnected T root2
    (fun v=>5≤G.degree v.val) low ok
  exact ⟨r.val,t.val,(mem_filter.mp rT).2,lift_side_path S.L p hp hs⟩

#print axioms free_route_small_far_shore
end Graffiti189LongestPath.CrossSaturation.Split.Five
