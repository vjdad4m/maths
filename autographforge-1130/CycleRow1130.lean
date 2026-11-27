import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row1130 : 2 ≤ Fintype.card (Fin 160) ∧ ClawFree (cycleGraph 160) ∧
    (∃ d, (cycleGraph 160).IsRegularOfDegree d) ∧
    ¬ ((1/7 : ℚ) * rainbow2 (cycleGraph 160) + 12/7 ≤ burning (cycleGraph 160)) := by
  let G := cycleGraph 160
  have reg (v : Fin 160) : G.degree v = 2 := cycleGraph_degree_three_le
  have claw : ClawFree G := by
    intro v a b c va vb vc ab ac bc
    have neighbors {x : Fin 160} (h : G.Adj v x) : x = v-1 ∨ x = v+1 := by
      simpa [G,cycleGraph_neighborFinset] using (G.mem_neighborFinset v x).mpr h
    rcases neighbors va with h|h <;> rcases neighbors vb with h'|h' <;>
      rcases neighbors vc with h''|h'' <;> simp_all
  have lb := rainbow_half G (fun v => (reg v).le)
  rw [Fintype.card_fin] at lb
  have lower : (80 : ℚ) ≤ rainbow2 G := by exact_mod_cast (show 80 ≤ rainbow2 G by omega)
  have upper : (burning G : ℚ) ≤ 13 := by exact_mod_cast burning160
  refine ⟨by rw [Fintype.card_fin]; decide,claw,⟨2,reg⟩,?_⟩
  change ¬ ((1/7 : ℚ) * rainbow2 G + 12/7 ≤ burning G)
  linarith

#print axioms row1130
end CycleBatch
