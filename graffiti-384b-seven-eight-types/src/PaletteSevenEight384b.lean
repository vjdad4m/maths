import Palette6Core384b
import Palette7Core384b
import Palette8Core384b
import Palette9Core384b

namespace Graffiti384b.SmallPalette
open Finset SimpleGraph

theorem exact_of_seven_or_eight_types {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (low : 7≤(types G).card) (high : (types G).card≤8) :
    gamma G≤bound G := by
  have bo : bound G=Fintype.card V-4 := by unfold bound; omega
  rw [bo]
  by_cases many : 10≤(nonleaves G).card
  · have b := nonleaf_bound G
    omega
  have lo := nonleaf_at_least_six G low
  have hi : (nonleaves G).card≤9 := by omega
  have cases : (nonleaves G).card=6 ∨ (nonleaves G).card=7 ∨
      (nonleaves G).card=8 ∨ (nonleaves G).card=9 := by omega
  rcases cases with sz|sz|sz|sz
  · exact nonleaf_model G sz low N6.quad_core
  · exact nonleaf_model G sz low N7.quad_core
  · exact nonleaf_model G sz low N8.quad_core
  · exact nonleaf_model G sz low N9.quad_core

#print axioms exact_of_seven_or_eight_types
end Graffiti384b.SmallPalette
