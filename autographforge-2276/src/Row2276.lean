import Row2055

namespace TraceableBurn
open SimpleGraph
open PathCycleSharpness (burning Eulerian Subcubic)

/-- GraphCalc's Eulerian predicate for simple undirected graphs uses
connectedness and even degree at every vertex. AutoGraphForge normalized
row 2276, cleared of the positive denominator. -/
theorem row2276 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2≤Fintype.card V) (he : Eulerian G) (subcubic : Subcubic G) : 3*burning G≤PathCycleSharpness.slater G+9 := by
  have hd (v : V) : G.degree v≤2 := by
    have hq := he.2 v
    have hv := subcubic v
    omega
  have size := (card_le_thrice_slater G hd).trans (cycle_budget _)
  have cv := cover_of_degree_two G he.1 hn hd size
  have hb : burning G≤slater G/3+3 := Nat.sInf_le (burns_of_cover he.1 cv)
  change 3*burning G≤TraceableBurn.slater G+9
  omega

theorem row2276_rat {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2≤Fintype.card V) (he : Eulerian G) (subcubic : Subcubic G) :
    (burning G : ℚ) ≤ (1/3 : ℚ)*PathCycleSharpness.slater G+3 := by
  have h : (3:ℚ)*(burning G : ℚ)≤(PathCycleSharpness.slater G : ℚ)+9 := by
    exact_mod_cast row2276 G hn he subcubic
  linarith

#print axioms row2276_rat
end TraceableBurn
