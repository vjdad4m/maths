import ClawRainbow

namespace TriangleFreeRainbow242
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem weights_full (hc : ClawRainbow720.ClawFree G) (ht : G.CliqueFree 3)
    (f : V → Fin 4) (sol : ClawRainbow720.Rainbow G f) :
    ClawRainbow720.weight f = Fintype.card V := by
  classical
  have nz (v : V) : f v ≠ 0 := by
    intro hv
    have demand := ClawRainbow720.rainbow_demand G f sol v hv
    let I := G.neighborFinset v
    have ind : G.IsIndepSet I := by
      rw [show (↑I : Set V) = G.neighborSet v by
        ext u
        exact G.mem_neighborFinset v u]
      exact G.isIndepSet_neighborSet_of_triangleFree ht v
    have cap := ClawRainbow720.local_cap G hc I ind v
    have hin : ((univ.filter (fun u => f u ≠ 0)).filter (G.Adj v)) ⊆
        I.filter (G.Adj v) := by
      intro u hu
      have va : G.Adj v u := (mem_filter.mp hu).2
      exact mem_filter.mpr ⟨(G.mem_neighborFinset v u).mpr va, va⟩
    have bound := (card_le_card hin).trans cap
    omega
  simp [ClawRainbow720.weight,nz]

theorem row242 (hc : ClawRainbow720.ClawFree G) (ht : G.CliqueFree 3) :
    ClawRainbow720.rainbowNumber G = Fintype.card V := by
  classical
  let sizes := {k | ∃ f : V → Fin 4, ClawRainbow720.weight f = k ∧ ClawRainbow720.Rainbow G f}
  have feasible : sizes.Nonempty := ⟨_, fun _ => 1, rfl,
    fun _ hv => False.elim ((by decide : (1 : Fin 4) ≠ 0) hv)⟩
  obtain ⟨f,cost,sol⟩ := Nat.sInf_mem feasible
  change ClawRainbow720.weight f = ClawRainbow720.rainbowNumber G at cost
  exact cost.symm.trans (weights_full G hc ht f sol)

#print axioms weights_full
#print axioms row242
end TriangleFreeRainbow242
