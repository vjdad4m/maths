import OddHole183
import Profiles183
import MetricCycle183
import Run4Shift183

namespace Graffiti183.Exceptional
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Written on the Wall II conjecture 183, in its exact catalogue form. -/
theorem conjecture183 (hc : G.Connected) : Claim183 G := by
  classical
  by_contra hf
  have claw : ClawFree G := claw_free_of_failure G hc hf
  obtain ⟨⟨hR,v,w,hVW,hu⟩,_⟩ :=
    (Graffiti183.conjecture183_failure_iff hc (Graffiti185.Reuse.order_bound G hc)).mp hf
  obtain ⟨s⟩ := exists_six_pattern hc claw (by omega) hVW hu
  obtain ⟨S,Sv,Sw,Ssix,Scon,Sbip⟩ := six_pattern_bip_seed G s
  obtain ⟨m,hm,hodd,f,hmark,hcyc,hmax⟩ := large_odd_hole G hc hf claw Sv Sw Ssix Scon Sbip
  have hv : v ∈ indexSet f := hmark (by simp)
  have hw : w ∈ indexSet f := hmark (by simp)
  obtain ⟨vi,hvi⟩ := mem_indexSet.mp hv
  obtain ⟨wi,hwi⟩ := mem_indexSet.mp hw
  have Hfar : 2 < G.dist (f vi) (f wi) := by rw [hvi,hwi,hVW]; decide
  have Hunique : ∀ x, 2 < G.dist (f vi) x ↔ x = f wi := by simpa only [hvi,hwi] using hu
  have Hmax : NoLargeMarked G (f vi) (f wi) m := by
    rw [hvi,hwi]
    exact hmax
  have noedge : ¬G.Adj (f vi) (f wi) := by
    intro e
    rw [dist_eq_one_iff_adj.mpr e] at Hfar
    omega
  have C := cycle_contact_conditions hm hcyc hc claw Hmax noedge
  have core : NoSmallCore G m := hole_connected_dom_lower G hc hf hm f hcyc
  have Hprof : ExteriorProfiles G f := fun z hz =>
    outside_profile_of_conditions hm hcyc claw C hz
  have Hshort := short_run_only hm hcyc C core Hfar Hprof
  have eq : m = 7 := cycle_length_seven hc hm hodd hcyc Hunique Hshort
  subst m
  obtain ⟨a,z,hz,hr⟩ := seven_has_run_four hc hcyc Hunique Hshort
  exact no_run_four_seven f claw hcyc C core Hfar Hmax a ⟨z,hz,hr⟩

#print axioms conjecture183
end Graffiti183.Exceptional
