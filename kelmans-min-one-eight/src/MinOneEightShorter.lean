import MinOneEight

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.MinOneEightShorter
open MinOneEight (Core core a b q)
open RemoteSpacedPrismHandle (Port)

private def marked (x y : Core) : Prop :=
  ∃ i : Port,(x=a i∧y=b i)∨(x=b i∧y=a i)

private instance (x y : Core) : Decidable (marked x y) := by
  unfold marked
  infer_instance

/-- The contribution of a single matching edge to the number of marked omissions. -/
def w (x y : Core) : ℕ := if marked x y then 1 else 0

abbrev m := q false

set_option maxRecDepth 8000 in
/-- A genuine alternating square cannot exchange its two matched edges for
the other two edges without changing the marked-edge count. -/
theorem no_neutral_four : ∀ x y : Core,
    [x,m x,y,m y].Nodup → core.Adj (m x) y → core.Adj (m y) x →
    w x (m x)+w y (m y) ≠ w (m x) y+w (m y) x := by decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- A genuine alternating six-cycle cannot exchange its three matched edges for
the other three edges without changing the marked-edge count. -/
theorem no_neutral_six : ∀ x y z : Core,
    [x,m x,y,m y,z,m z].Nodup →
    core.Adj (m x) y → core.Adj (m y) z → core.Adj (m z) x →
    w x (m x)+w y (m y)+w z (m z) ≠ w (m x) y+w (m y) z+w (m z) x := by decide

#print axioms no_neutral_four
#print axioms no_neutral_six
end KelmansCactus.AtomicBridge.MinOneEightShorter
