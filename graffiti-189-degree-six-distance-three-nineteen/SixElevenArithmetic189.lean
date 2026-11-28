import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix

/-- Arithmetic of the two marked port classes and the four visibility
classes of nonports in the eleven-vertex shore. The eight e-coordinates
count the possible unique vertex below threshold. -/
theorem impossible_six_eleven_counts
    (p q a₀ a₁ b₀ b₁ x y w z ea₀ ea₁ eb₀ eb₁ ex ey ew ez : ℕ)
    (pn : 0<p) (qn : 0<q)
    (small : p+q≤6)
    (low : ea₀+ea₁+eb₀+eb₁+ex+ey+ew+ez+5≤p+q)
    (order : a₀+a₁+b₀+b₁+x+y+w+z=11)
    (aFive : a₀+a₁≤5) (bFive : b₀+b₁≤5)
    (aHigh : 6≤p+a₀+a₁) (bHigh : 6≤q+b₀+b₁)
    (aVis : b₁+x+w≤p) (bVis : a₁+y+w≤q)
    (noDark : z≤ez)
    (aPlain : ea₀<a₀ → p+b₀+b₁≤6+eb₀+eb₁)
    (bPlain : eb₀<b₀ → q+a₀+a₁≤6+ea₀+ea₁)
    (aSees : ea₁<a₁ → p+1+b₀≤6+eb₀)
    (bSees : eb₁<b₁ → q+1+a₀≤6+ea₀)
    (onlyA : ex<x → q+1+b₀+b₁≤6+eb₀+eb₁)
    (onlyB : ey<y → p+1+a₀+a₁≤6+ea₀+ea₁) :
    False := by
  omega

#print axioms impossible_six_eleven_counts
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
