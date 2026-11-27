import CambyMinimumCycleDecomp133
import NestedCoreDominatingC7Branch133
import C9Main133

namespace Graffiti133FiveResidual
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby
  Graffiti133CambyMinimum Graffiti133C9 Graffiti133NestedThreeControls
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem if_radius_four_and_high_mean_nested_p5_free_core
    (hc : G.Connected) (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (r : 4≤radius G) (s : 4*Fintype.card V<∑ x : V,localIndependence G x) :
    ∃ D : Finset V,MinimalSize G D ∧
      NoPath (G.induce (D : Set V)) 7 ∧
      ∃ E : Finset (D : Set V),MinimalSize (G.induce (D : Set V)) E ∧
        NoPath ((G.induce (D : Set V)).induce (E : Set (D : Set V))) 5 := by
  classical
  rcases minimum_connected_domination_decomposition G hc 7 (by decide) h9 with
    ⟨D,dm,no7⟩|⟨H,dom⟩
  · let J := G.induce (D : Set V)
    have noIn : NoPath J 7 := by
      rintro ⟨p,hp⟩
      exact no7 ⟨Subtype.val ∘ p,⟨Subtype.val_injective.comp hp.1,hp.2⟩,fun i=>(p i).property⟩
    rcases minimum_connected_domination_decomposition J dm.1.1 5 (by decide) noIn with
      ⟨E,em,en⟩|⟨HJ,hd⟩
    · refine ⟨D,dm,noIn,E,em,?_⟩
      rintro ⟨p,hp⟩
      exact en ⟨Subtype.val ∘ p,⟨Subtype.val_injective.comp hp.1,hp.2⟩,fun i=>(p i).property⟩
    · let H : Hole G 7 := ⟨Subtype.val ∘ HJ.c,Subtype.val_injective.comp HJ.inj,HJ.adj⟩
      have dom (x : V) (xd : x∈D) (xo : Outside H.c x) : ∃ i,G.Adj x (H.c i) :=
        hd ⟨x,xd⟩ (fun i eq=>xo i (congrArg Subtype.val eq))
      have bd := radius_four_minimum_p7_free_core_with_dominating_C7_mean_four H hc h4 h9 r
        D dm (fun i=>(HJ.c i).property) noIn dom
      exact (not_lt_of_ge bd s).elim
  · have bd := dominating_nine_budget H h4 h9 dom
    exact (not_lt_of_ge bd s).elim

#print axioms if_radius_four_and_high_mean_nested_p5_free_core
end Graffiti133FiveResidual
