import SixWeightedSideRoute189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair Graffiti189Ore
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Rooted Ore with the order rather than order-plus-one degree-sum threshold;
the other endpoint is unrestricted. -/
theorem rooted_side_route (S : Finset V) {r : V} (rs : r∈S)
    (ore : ∀ u∈S,∀ v∈S,u≠v → ¬G.Adj u v →
      S.card≤(inside G S u).card+(inside G S v).card) :
    ∃ t∈S,RouteOn G S t r := by
  classical
  let T := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let K : SimpleGraph T := ⊤
  let r' : T := ⟨r,rs⟩
  have cl : CompleteOn K (univ : Finset T) := by
    intro u _ v _ ne
    exact ne
  obtain ⟨t,p,pp,ps⟩ := rooted_path_in_clique (univ : Finset T) cl (mem_univ r')
  have rK : Rooted K r' := ⟨t,p,pp,fun u=>(ps u).mpr (mem_univ u)⟩
  obtain ⟨z,q,qp,qs⟩ := rooted_closure (show J≤K from le_top) r' (fun u v uv no=>by
    have ne : u.val≠v.val := fun e=>uv (Subtype.ext e)
    have h := ore u.val u.property v.val v.property ne no
    rw [←Fintype.card_coe S,inside_card_eq_degree_induce,inside_card_eq_degree_induce] at h
    exact h) rK
  exact ⟨z.val,z.property,(show RouteOn G S r z.val from lift_side_path S q qp qs).reverse⟩

#print axioms rooted_side_route
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
