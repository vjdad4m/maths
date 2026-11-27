import P5DominatingCycleCenter133
import C7BranchResidualP5Core133
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Graffiti133P5Radius
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133MultiWeighted
  Graffiti133Camby Graffiti133FiveResidual
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem close_two_dist_le (hc : G.Connected) {x y : V} (h : CloseTwo G x y) : G.dist x y≤2 := by
  rcases h with rfl|ed|⟨z,a,b⟩
  · rw [dist_self]
    decide
  · rw [dist_eq_one_iff_adj.mpr ed]
    decide
  · have bound : G.dist x y≤G.dist x z+G.dist z y := hc.dist_triangle
    rw [dist_eq_one_iff_adj.mpr a,dist_eq_one_iff_adj.mpr b] at bound
    exact bound

theorem radius_at_most_four_of_nested_p5_free (hc : G.Connected) (h4 : FourCycleFree G)
    (D : Finset V) (Ddom : CD G D) (E : Finset (D : Set V)) (Edom : CD (G.induce (D : Set V)) E)
    (e5 : NoPath ((G.induce (D : Set V)).induce (E : Set (D : Set V))) 5) :
    radius G≤4 := by
  classical
  let J := G.induce (D : Set V)
  let L := J.induce (E : Set (D : Set V))
  obtain ⟨c,cc⟩ := p5free_has_two_step_center Edom.1 (restricted_c4 (restricted_c4 h4 D) E) e5
  let a : V := c.val.val
  have close (x : (E : Set (D : Set V))) : G.dist a x.val.val≤2 :=
    close_two_dist_le hc (by
      rcases cc x with h|e|⟨z,p,q⟩
      · exact Or.inl (congrArg (fun v : (E : Set (D : Set V))=>v.val.val) h)
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr ⟨z.val.val,p,q⟩))
  have d3 (x : (D : Set V)) : G.dist a x.val≤3 := by
    rcases Edom.2 x with xe|⟨y,ye,xy⟩
    · exact (close ⟨x,xe⟩).trans (by decide)
    · have t : G.dist a x.val≤G.dist a y.val+G.dist y.val x.val := hc.dist_triangle
      rw [dist_eq_one_iff_adj.mpr (show G.Adj y.val x.val from xy.symm)] at t
      have z : G.dist a y.val≤2 := close ⟨y,ye⟩
      omega
  have all (x : V) : G.dist a x≤4 := by
    rcases Ddom.2 x with xd|⟨y,yd,xy⟩
    · exact (d3 ⟨x,xd⟩).trans (by decide)
    · have t : G.dist a x≤G.dist a y+G.dist y x := hc.dist_triangle
      rw [dist_eq_one_iff_adj.mpr xy.symm] at t
      have z : G.dist a y≤3 := d3 ⟨y,yd⟩
      omega
  unfold radius
  have hm : Finset.univ.sup (G.dist a) ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hl := Finset.min_le hm
  cases e : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d =>
    have hu : d≤Finset.univ.sup (G.dist a) := by simpa [e] using hl
    exact hu.trans (Finset.sup_le_iff.mpr (fun w _=>all w))

theorem radius_five_mean_at_most_four (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : NoPath G 9) (hr : 5≤radius G) :
    (∑ x : V,localIndependence G x)≤4*Fintype.card V := by
  by_contra! high
  have r4 : 4≤radius G := (by decide : 4≤5).trans hr
  obtain ⟨D,dm,_,E,em,e5⟩ := if_radius_four_and_high_mean_nested_p5_free_core hc h4 h9 r4 high
  have r := radius_at_most_four_of_nested_p5_free hc h4 D dm.1 E em.1 e5
  omega

#print axioms radius_at_most_four_of_nested_p5_free
#print axioms radius_five_mean_at_most_four
end Graffiti133P5Radius
