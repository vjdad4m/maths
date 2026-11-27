import EarRelease

open SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaCrossEarGeometry
open PentagonProfile (Port)
open EarRelease (Released)

variable {V : Type*}

/-- The two replacement contacts cannot themselves be adjacent:
together with the absorbed edge this would close an actual square. -/
theorem replacements_nonadjacent {G : SimpleGraph V} {p : Port↪V}
    (L : Released G p)
    (noSquare : ∀ a b c d : V,G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a=c∨b=d)
    (ear : G.Adj (p 1) (p 4)) :
    ¬G.Adj L.next1.val L.next4.val := by
  intro bad
  have b : G.Adj (p 4) L.next4.val := (L.end4 L.next4).mpr rfl
  have a : G.Adj (p 1) L.next1.val := (L.end1 L.next1).mpr rfl
  rcases noSquare (p 1) (p 4) L.next4.val L.next1.val ear b bad.symm a.symm with e|e
  · exact L.next4.property.1 e.symm
  · exact L.next1.property.2 e.symm

#print axioms replacements_nonadjacent
end KelmansCactus.AtomicBridge.ThetaCrossEarGeometry
