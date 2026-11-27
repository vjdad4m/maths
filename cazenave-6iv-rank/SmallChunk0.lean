import SmallNumerics
namespace CazenaveRank
set_option maxRecDepth 10000
set_option maxHeartbeats 15000000
theorem case3 : intClaim 3 0 := by decide
theorem case4 : ∀ p : Fin 3, intClaim 4 p.val := by decide
theorem case5 : ∀ p : Fin 3, intClaim 5 p.val := by decide
theorem case6 : ∀ p : Fin 4, intClaim 6 p.val := by decide
theorem case7 : ∀ p : Fin 4, intClaim 7 p.val := by decide
theorem case8 : ∀ p : Fin 5, intClaim 8 p.val := by decide
theorem case9 : ∀ p : Fin 5, intClaim 9 p.val := by decide
theorem case10 : ∀ p : Fin 6, intClaim 10 p.val := by decide
theorem case11 : ∀ p : Fin 6, intClaim 11 p.val := by decide
theorem case12 : ∀ p : Fin 7, intClaim 12 p.val := by decide
end CazenaveRank
