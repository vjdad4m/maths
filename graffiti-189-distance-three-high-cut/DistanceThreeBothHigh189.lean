import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore shore_off shore_disjoint shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private secondShore charge_at_high_port from DegreeFiveDistanceTwoThreeClose189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- On a distance-at-least-three two-shore cut under the degree-five
hypotheses, neither distinguished cut vertex can be the unique low vertex. -/
theorem both_cut_degrees_at_least_five_of_far_cut {a b : V}
    (hc : G.Connected) (far : 3≤G.dist a b) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : (CutGraph (G:=G) a b).ConnectedComponent} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D) :
    5≤G.degree a ∧ 5≤G.degree b := by
  classical
  have ab : a≠b := by intro eq; rw [eq,dist_self] at far; omega
  have nab : ¬G.Adj a b := by
    intro e; have h := dist_eq_one_iff_adj.mpr e; omega
  have noncommon (v : V) (av : G.Adj a v) (bv : G.Adj b v) : False := by
    have w := G.dist_le (SimpleGraph.Walk.cons av bv.symm.toWalk)
    change G.dist a b≤2 at w
    omega
  have main (c d : V) (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) :
      5≤G.degree c := by
    by_contra! low
    have ch (F : (CutGraph (G:=G) a b).ConnectedComponent) :
        5≤((Shore F).filter (G.Adj c)).card + (secondShore F c).card := by
      have hit : ∃ u∈Shore F,G.Adj c u := by
        rcases perm with ⟨rfl,h⟩|⟨rfl,h⟩
        · exact shore_hit_a ab conn F
        · exact shore_hit_b ab conn F
      obtain ⟨u,uf,cu⟩ := hit
      have uc : u≠c := cu.ne.symm
      have high := (degree u c uc).resolve_right (by omega)
      have no : ¬G.Adj d u := by
        intro du
        rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact noncommon u cu du
        · exact noncommon u du cu
      simpa only [if_neg no] using charge_at_high_port perm hc uf cu high
    have deg : G.degree c=((Shore C).filter (G.Adj c)).card+((Shore D).filter (G.Adj c)).card := by
      let A := (Shore C).filter (G.Adj c)
      let B := (Shore D).filter (G.Adj c)
      have eq : G.neighborFinset c=A∪B := by
        ext v
        constructor
        · intro vm
          have cv := (G.mem_neighborFinset ..).mp vm
          rcases cover v with rfl|rfl|vc|vd
          · rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
            · exact (cv.ne rfl).elim
            · exact (nab cv.symm).elim
          · rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
            · exact (nab cv).elim
            · exact (cv.ne rfl).elim
          · exact mem_union_left _ (mem_filter.mpr ⟨vc,cv⟩)
          · exact mem_union_right _ (mem_filter.mpr ⟨vd,cv⟩)
        · intro vm
          exact (G.mem_neighborFinset ..).mpr
            ((mem_union.mp vm).elim (fun h=>(mem_filter.mp h).2) (fun h=>(mem_filter.mp h).2))
      have dis : Disjoint A B := (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)
      have e := congrArg Finset.card eq
      rwa [G.card_neighborFinset_eq_degree,card_union_of_disjoint dis] at e
    have cap : (secondShore C c).card+(secondShore D c).card≤5 := by
      have soc : secondShore C c⊆DistanceTwo G c := inter_subset_right
      have sod : secondShore D c⊆DistanceTwo G c := inter_subset_right
      have dis := (shore_disjoint cd).mono
        (show secondShore C c⊆Shore C from inter_subset_left)
        (show secondShore D c⊆Shore D from inter_subset_left)
      have le := card_le_card (union_subset soc sod)
      rw [card_union_of_disjoint dis] at le
      exact le.trans (distanceTwo_le_of_even 5 c (even c))
    have pc := ch C
    have pd := ch D
    omega
  exact ⟨main a b (.inl ⟨rfl,rfl⟩),main b a (.inr ⟨rfl,rfl⟩)⟩

#print axioms both_cut_degrees_at_least_five_of_far_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
