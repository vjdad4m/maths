import PaletteLift384b
import Palette9Entries384b

namespace Graffiti384b.SmallPalette.N9
open Graffiti384b.SmallPalette Finset SimpleGraph
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4500000

theorem quad_core (G : SimpleGraph (Fin 9)) (dh : DecidableRel G.Adj) :
    letI := dh
    6≤(graphPalette G).card → ∃ S, QuadOmit G S := by
  letI := dh
  intro div
  obtain ⟨x,y,xy,x5,y5⟩ := two_large_scores (by decide : 2≤9) G div
  by_cases large : 4≤(G.neighborFinset x∩G.neighborFinset y).card
  · exact common_quad G x y xy large
  obtain ⟨s,p,roots,edge01,contact⟩ := GraffitiSmallNorm9.normalize_two_anchors G x y xy
    (four_degree G x5) (four_degree G y5) (by omega)
  obtain ⟨b,fit⟩ := entries_of_shape G s p edge01 contact
  have scored := score_eq_triangles G p _ fit
  have r : Ranked (n:=9) (adj (forms9 s) b) := by
    refine ⟨?_,?_⟩
    · rwa [graphPalette_transfer G p _ scored]
    · intro i small
      rw [scored]
      have eq : i=0 ∨ i=1 := by
        have v : i.val=0 ∨ i.val=1 := by omega
        exact v.imp Fin.ext Fin.ext
      rcases eq with rfl|rfl
      · rcases roots with ⟨h,_⟩|⟨h,_⟩
        · rwa [h]
        · rwa [h]
      · rcases roots with ⟨_,h⟩|⟨_,h⟩
        · rwa [h]
        · rwa [h]
  obtain ⟨a,b',c,d,effective⟩ := check9 s b r
  exact ⟨_, effective_to_omit G p.toEmbedding _ fit effective⟩

#print axioms quad_core
end Graffiti384b.SmallPalette.N9
