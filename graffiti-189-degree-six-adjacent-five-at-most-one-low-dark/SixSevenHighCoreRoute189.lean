import SixWeightedSideRoute189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private lift_side_path from DegreeFiveSmallSides189
open private starClose star_mono star_degree_of_marked star_degree_of_unmarked from SixTenOre189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- An order-seven dark block of internal minimum degree three with a
five-vertex degree-five core is Hamilton-connected. Use ordinary Ore
sums to fill every missing edge incident to the high core. -/
theorem seven_high_core_route (D C : Finset V) (cd : C⊆D)
    (d7 : D.card=7) (c5 : 5≤C.card)
    (deg : ∀ z∈D,3≤(inside G D z).card)
    (high : ∀ z∈C,5≤(inside G D z).card)
    {a b : V} (ad : a∈D) (bd : b∈D) (ab : a≠b) :
    RouteOn G D a b := by
  classical
  let U := ↑(↑D : Set V)
  let J := G.induce (↑D : Set V)
  let M := univ.filter (fun u : U=>u.val∈C)
  let H := starClose J M
  have n7 : Fintype.card U=7 := (Fintype.card_coe D).trans d7
  have exactC : M.card=C.card := by
    apply card_bij (fun (j : U) _=>j.val)
    · intro j m
      exact (mem_filter.mp m).2
    · intro j _ k _ e
      exact Subtype.ext e
    · intro z zm
      exact ⟨⟨z,cd zm⟩,mem_filter.mpr ⟨mem_univ _,zm⟩,rfl⟩
  have c (u : U) : 3≤J.degree u := by
    rw [←inside_card_eq_degree_induce]
    exact deg _ u.property
  have C5 {u : U} (um : u∈M) : 5≤J.degree u := by
    rw [←inside_card_eq_degree_induce]
    exact high _ (mem_filter.mp um).2
  have H5 (u : U) : 5≤H.degree u := by
    change 5≤(starClose J M).degree u
    by_cases m : u∈M
    · have w := star_degree_of_marked (G:=J) M m
      rw [n7] at w
      omega
    have w := star_degree_of_unmarked (G:=J) M m
    omega
  let a' : U := ⟨a,ad⟩
  let b' : U := ⟨b,bd⟩
  have ne : a'≠b' := fun h=>ab (congrArg Subtype.val h)
  obtain ⟨p,pp,ps⟩ := hamilton_connected_of_ore (G:=H)
    (fun u v _ _=>by rw [n7]; have x := H5 u; have y := H5 v; omega) ne
  have ore (u v : U) (yes : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card U+1 ≤ J.degree u+J.degree v+(if u=b' ∨ v=b' then 1 else 0) := by
    rcases yes with yes|⟨_,mu|mv⟩
    · exact (no yes).elim
    · have i := C5 mu
      have j := c v
      omega
    · have i := c u
      have j := C5 mv
      omega
  obtain ⟨q,qp,qs⟩ := weighted_terminal_ore_closure (star_mono J M) ore p pp ps
  exact lift_side_path D q qp qs

#print axioms seven_high_core_route
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
