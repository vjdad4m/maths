import SixElevenArithmetic189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix

/-- In a twelve-vertex opposite shore the hidden nonport supplies an
extra omitted slot if present. Otherwise only dark-versus-port
nonedges need be charged. -/
theorem impossible_six_twelve_counts
    (p q a₀ a₁ b₀ b₁ x y w z ea₀ ea₁ eb₀ eb₁ ex ey ew ez : ℕ)
    (_pn : 0<p) (_qn : 0<q)
    (small : p+q≤6)
    (low : ea₀+ea₁+eb₀+eb₁+ex+ey+ew+ez+5≤p+q)
    (order : a₀+a₁+b₀+b₁+x+y+w+z=12)
    (aFive : a₀+a₁+y≤5) (bFive : b₀+b₁+x≤5)
    (aHigh : 6≤p+a₀+a₁) (bHigh : 6≤q+b₀+b₁)
    (aVis : b₁+x+w≤p) (bVis : a₁+y+w≤q)
    (noDark : z≤ez) (someHidden : 0<z)
    (aPlain : ea₀<a₀ → p+y+z+(if z=0 then 0 else b₀+b₁)≤
      6+ey+ez+(if z=0 then 0 else eb₀+eb₁))
    (bPlain : eb₀<b₀ → q+x+z+(if z=0 then 0 else a₀+a₁)≤
      6+ex+ez+(if z=0 then 0 else ea₀+ea₁))
    (aSees : ea₁<a₁ → p+1+y+z+(if z=0 then 0 else b₀)≤6+ey+ez+(if z=0 then 0 else eb₀))
    (bSees : eb₁<b₁ → q+1+x+z+(if z=0 then 0 else a₀)≤6+ex+ez+(if z=0 then 0 else ea₀))
    (_onlyA : ex<x → q+1+b₀+b₁≤6+eb₀+eb₁)
    (_onlyB : ey<y → p+1+a₀+a₁≤6+ea₀+ea₁) :
    False := by
  have h : z≠0 := Nat.ne_of_gt someHidden
  simp only [if_neg h] at aPlain bPlain aSees bSees
  omega

#print axioms impossible_six_twelve_counts
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
