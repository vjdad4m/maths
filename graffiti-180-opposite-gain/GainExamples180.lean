import TwoWingGain180
import EightPorts180
import NineConflict180
import TightFlip180

set_option warningAsError true
set_option compiler.extract_closed false
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair

/-- The old eight-vertex recoloring obstruction meets the parity-contained
scope, as does the tight nine-vertex two-component marking. -/
theorem compatible_regressions :
    Protected Eight.G 2 false Eight.A ∧ allowance Tight.G 1 false Tight.A=2 ∧ Protected Tight.G 1 false Tight.A := by
  constructor
  · have marks := Eight.data.2.1
    apply solo_scope Eight.G Eight.data.1 (by decide) 2 0 5 (by decide) false Eight.A Eight.data.2.2.1
      (by decide) (Eight.lower_pair {0,5} (by decide))
    · rw [marks];decide
    · rw [marks];decide
    · exact Or.inl (by rw [marks];decide)
  · refine ⟨Tight.budget,?_⟩
    have marks := Tight.data.2.1
    apply solo_scope Tight.G Tight.data.1 (by decide) 1 0 7 (by decide) false Tight.A Tight.data.2.2.1
      (by decide) ((color_function ..).mpr ⟨Tight.paint,Tight.cp⟩)
    · rw [marks];decide
    · rw [marks];decide
    · exact Or.inl (by rw [marks];decide)

namespace ExampleNine
open PairRepair.Nine

/-- On the published incompatible example, the new scoped theorem gives
the lower bound directly from the disjoint masks. The previously
certified exact allowance attains this new bound. -/
theorem sharp_gain : (3≤allowance G 6 false A) ∧ allowance G 6 false A=3 := by
  let c (v : V) := decide (v∈({2,4,7}:Finset V))
  have cp : ProperOn G (univ\({0,1}:Finset V)) c := by unfold ProperOn;decide
  have parts : TwoRegions G 0 1 C D ∅ := ⟨by decide,by decide,by decide,by decide,by decide,by decide⟩
  have l : MixedAt G 0 C c := ⟨2,3,by decide,by decide,by decide,by decide,
    joined_step G C (joined_self G C (by decide : (2:V)∈C)) (by decide) (by decide)⟩
  have d : MixedAt G 0 D c := ⟨4,5,by decide,by decide,by decide,by decide,
    joined_step G D (joined_self G D (by decide : (4:V)∈D)) (by decide) (by decide)⟩
  have marks := data.2.1
  have deg : G.degree 0=4 := (card_neighborFinset_eq_degree G 0).symm.trans (by decide)
  have same (F H : Fintype (G.neighborSet 0)) : @SimpleGraph.degree V G 0 F=@SimpleGraph.degree V G 0 H := by
    rw [Subsingleton.elim F H]
  have degrees (F : Fintype (G.neighborSet 0)) : @SimpleGraph.degree V G 0 F=4 := (same F _).trans deg
  have rule (S : Finset V) (sr : S⊆univ\({0,1}:Finset V)) (t : Bool)
      (hit : DropCheck G 0 1 (A∩insert 6 (parity G 6 false)) S c t) : ∃ x∈S,TerminalColor G 0 1 (S.erase x) t := by
    obtain ⟨x,xs,_,chk⟩ := hit
    have sub := (erase_subset x S).trans sr
    exact ⟨x,xs,(terminal_iff_contacts G 0 1 (by decide) (by decide) _
      (fun m => (mem_sdiff.mp (sub m)).2 (by decide)) (fun m => (mem_sdiff.mp (sub m)).2 (by decide))
      c (fun i im j jm => cp i (sub im) j (sub jm)) t).mpr chk⟩
  have nod : ¬∃ t : Bool,DropCheck G 0 1 (A∩insert 6 (parity G 6 false)) C c t ∧
       DropCheck G 0 1 (A∩insert 6 (parity G 6 false)) D c t := by
    rintro ⟨t,lc,rc⟩
    have yes := (opposite_signatures t).1.mp (rule C (by decide) t lc)
    have no := (opposite_signatures t).2.mp (rule D (by decide) t rc)
    exact Bool.noConfusion (no.symm.trans yes)
  refine ⟨?_,budget⟩
  apply masks_force_three G data.1 6 0 1 (by decide) false A data.2.2.1 (by decide) (by decide)
    transversal (by rw [marks];decide) (by rw [marks];decide) (degrees _) C D ∅ parts c cp l d _ nod
  exact Or.inl (Or.inl (by rw [marks];decide))
end ExampleNine

#print axioms compatible_regressions
#print axioms ExampleNine.sharp_gain
end Minimal180.OppositeGain
