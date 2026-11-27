import PairedOn189
import MultiPinRotation189

namespace Graffiti189LongestPath.OneSlack
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The paired double-porter configuration at d=4 is impossible if the
third vertex of its closed-star boundary is also on the longest path. -/
theorem paired_on_impossible (hc : G.Connected)
    (bound : ∀ v, (EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (a4 : 4≤G.degree a) (b4 : 4≤G.degree b) {x : V} (hx : x∉p.support)
    {i : ℕ} (hi : i∈Pins p x) (hj : i+2∈Pins p x)
    (size : (Pins p x).card=2)
    {u : V} (hu : u∉p.support) (xu : G.Adj x u)
    {t : V} (ts : t∈p.support) (tb : t∈External G (OmittedStar p x))
    (nt : t∉PinVertices p x) : False := by
  obtain ⟨upper,bx,y,yo,xy,j,jy,eq,jc,by'⟩ :=
    PairedOn.paired_on_data hc bound conn hp hx hi hj size hu xu ts tb nt
  have gap {m : ℕ} (hm : m∈Pins p x) : m+3≤j ∨ j+3≤m := by
    have ne : m≠j := by
      intro e
      subst m
      exact nt (mem_image.mpr ⟨j,hm,eq⟩)
    rcases lt_or_gt_of_ne ne with lo|lo
    · exact Or.inl (gap_three_of_linked_pins hp hm jy lo xy.toWalk (IsPath.of_adj xy)
        (by simp) (by simp [hx,yo]))
    · exact Or.inr (gap_three_of_linked_pins hp jy hm lo xy.symm.toWalk (IsPath.of_adj xy.symm)
        (by simp) (by simp [hx,yo]))
  have lower := MultiRotation.path_order_ge_twelve hc hp a4 b4 hx hi hj size
    (distanceTwo_le_of_even 4 x (bound x)) bx yo jy jc (distanceTwo_le_of_even 4 y (bound y)) by'
    (gap hi) (gap hj)
  omega

#print axioms paired_on_impossible
end Graffiti189LongestPath.OneSlack
