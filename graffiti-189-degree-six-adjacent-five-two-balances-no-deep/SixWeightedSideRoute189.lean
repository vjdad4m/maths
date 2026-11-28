import SixTenOre189
import AdjacentCutFiveFourteenDarkLift189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private lift_side_path from DegreeFiveSmallSides189

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Terminal Ore on a prescribed support, with one unit of slack at the
specified last vertex, transferred through the induced graph. -/
theorem weighted_side_route (S : Finset V) {x y : V} (xs : x∈S) (ys : y∈S) (xy : x≠y)
    (ore : ∀ u∈S,∀ v∈S,u≠v → ¬G.Adj u v →
      S.card+1≤(inside G S u).card+(inside G S v).card+(if u=y ∨ v=y then 1 else 0)) :
    RouteOn G S x y := by
  classical
  let T := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let K : SimpleGraph T := ⊤
  let x' : T := ⟨x,xs⟩
  let y' : T := ⟨y,ys⟩
  have xy' : x'≠y' := fun e=>xy (congrArg Subtype.val e)
  have need (u v : T) (uv : K.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card T+1≤J.degree u+J.degree v+(if u=y' ∨ v=y' then 1 else 0) := by
    have uz : u.val≠v.val := fun h=>uv (Subtype.ext h)
    have rel : (u.val=y ∨ v.val=y) ↔ (u=y' ∨ v=y') := by
      constructor
      · exact fun h=>h.elim (fun j=>.inl (Subtype.ext j)) (fun j=>.inr (Subtype.ext j))
      · exact fun h=>h.elim (fun j=>.inl (congrArg Subtype.val j)) (fun j=>.inr (congrArg Subtype.val j))
    have h := ore u.val u.property v.val v.property uz no
    rw [←Fintype.card_coe S,inside_card_eq_degree_induce,inside_card_eq_degree_induce] at h
    simpa only [rel] using h
  obtain ⟨p,pp,ps⟩ := hamilton_connected_of_ore (G:=K)
    (fun u v ne notEdge=>False.elim (notEdge (show K.Adj u v from ne))) xy'
  obtain ⟨q,qp,qs⟩ := weighted_terminal_ore_closure (show J≤K from le_top) need p pp ps
  exact lift_side_path S q qp qs

#print axioms weighted_side_route
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
