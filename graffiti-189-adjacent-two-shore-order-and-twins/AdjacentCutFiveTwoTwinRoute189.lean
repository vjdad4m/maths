import AdjacentCutFiveTwoTwinGeometry189
import UniversalRouteSingletons189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_hit_a from AdjacentCutFiveActual189
open private d2 from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 40000

theorem adj_twin_route_of_balanced_saturated (hc : G.Connected) (ab : a ≠ b)
    (even : ∀ x, (EvenFrom G x).card ≤ 6) (twin : (∀ z, z ≠ a → z ≠ b → (G.Adj a z ↔ G.Adj b z)))
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    {C D : (CutGraph (G:=G) a b).ConnectedComponent} (cd : C≠D)
    (five : (AdjTwinOdd D).card = 5) (fiveC : (AdjTwinOdd C).card = 5)
    (bound : (AdjTwinEven C).card ≤ 5) :
    ∃ s t, G.Adj a s ∧ RouteOn G (Shore C) s t := by
  classical
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
  have one x (ax : G.Adj a x) : G.dist a x = 1 := dist_eq_one_iff_adj.mpr ax
  have oddport {z : V} (zc : z∈Shore C) : z∈AdjTwinOdd C ↔ G.Adj a z := by
    simp only [AdjTwinOdd,mem_filter,zc,true_and]
    constructor
    · intro oz
      rcases adj_twin_port_universal_of_odd_five hc even twin cd five xc ax z zc with rfl|xz
      · exact ax
      by_contra az
      have za : z≠a := fun e => (shore_off C).1 (e ▸ zc)
      have dz := d2 hc za.symm az ax xz
      exact oz (by simp [(mem_filter.mp dz).2])
    · intro az
      rw [one z az]
      decide
  have apart : Disjoint (AdjTwinOdd C) (AdjTwinEven C) :=
    disjoint_left.mpr (fun _ ho he => (mem_filter.mp ho).2 (mem_filter.mp he).2)
  have union : AdjTwinOdd C ∪ AdjTwinEven C = Shore C := by
    ext z
    simp only [AdjTwinOdd,AdjTwinEven,mem_union,mem_filter]
    constructor
    · exact fun h=>h.elim And.left And.left
    intro hz
    by_cases e : Even (G.dist a z)
    · exact .inr ⟨hz,e⟩
    · exact .inl ⟨hz,e⟩
  have xk : x∈AdjTwinOdd C := (oddport xc).mpr ax
  obtain ⟨t,p,_⟩ := universal_route_from_singletons (AdjTwinOdd C) (AdjTwinEven C) xk
    apart (by
      intro u hu w hw ne
      have uc := (mem_filter.mp hu).1
      rw [union] at hw
      have uw := adj_twin_port_universal_of_odd_five hc even twin cd five uc
        ((oddport uc).mp hu) w hw
      exact uw.resolve_left ne.symm) (by rwa [fiveC])
  rw [union] at p
  exact ⟨x,t,ax,p⟩

#print axioms adj_twin_route_of_balanced_saturated
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
