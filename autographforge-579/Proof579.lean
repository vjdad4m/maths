import ClawRainbow
import HallRainbow

namespace RainbowIndependent579
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem independent_le_weight (hf : ClawRainbow720.ClawFree G) (I : Finset V)
    (ind : G.IsIndepSet I) (f : V → Fin 3) (sol : HallRainbow1121.Rainbow G f) :
    I.card ≤ HallRainbow1121.weight f := by
  classical
  let B : Finset V := univ.filter fun v => f v ≠ 0
  have incident (u : V) (hu : u ∈ I \ B) :
      2 ≤ ((B \ I).bipartiteAbove G.Adj u).card := by
    obtain ⟨ui, ub⟩ := mem_sdiff.mp hu
    have zero : f u = 0 := by simpa [B] using ub
    obtain ⟨a, ua, ha⟩ := sol u zero 1 (by decide)
    obtain ⟨b, ub', hb⟩ := sol u zero 2 (by decide)
    have ne : a ≠ b := by
      intro e
      have e' : (1 : Fin 3) = 2 := ha.symm.trans ((congrArg f e).trans hb)
      exact (by decide : (1 : Fin 3) ≠ 2) e'
    have mem (v : V) (uv : G.Adj u v) (nz : f v ≠ 0) :
        v ∈ (B \ I).bipartiteAbove G.Adj u :=
      (mem_bipartiteAbove _).mpr
        ⟨mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, nz⟩, fun vi => ind ui vi uv.ne uv⟩, uv⟩
    have ma := mem a ua (ha.symm ▸ (by decide : (1 : Fin 3) ≠ 0))
    have mb := mem b ub' (hb.symm ▸ (by decide : (2 : Fin 3) ≠ 0))
    have sub : ({a,b} : Finset V) ⊆ (B \ I).bipartiteAbove G.Adj u := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact ma
      · rw [mem_singleton] at hv
        exact hv ▸ mb
    simpa [ne] using card_le_card sub
  have supply (v : V) (_ : v ∈ B \ I) :
      ((I \ B).bipartiteBelow G.Adj v).card ≤ 2 := by
    apply le_trans (card_le_card ?_) (ClawRainbow720.local_cap G hf I ind v)
    intro u hu
    obtain ⟨mem, uv⟩ := (mem_bipartiteBelow _).mp hu
    exact mem_filter.mpr ⟨(mem_sdiff.mp mem).1, uv.symm⟩
  have count := card_mul_le_card_mul G.Adj incident supply
  have diff : (I \ B).card ≤ (B \ I).card :=
    Nat.le_of_mul_le_mul_right count (by decide)
  have hi := card_sdiff_add_card I B
  have hb := card_sdiff_add_card B I
  rw [union_comm B I] at hb
  change I.card ≤ B.card
  omega

theorem row579 (hf : ClawRainbow720.ClawFree G) :
    G.indepNum ≤ HallRainbow1121.rainbowNumber G 2 := by
  classical
  obtain ⟨I,hi⟩ := G.exists_isNIndepSet_indepNum
  let sizes := {k | ∃ f : V → Fin 3, HallRainbow1121.weight f = k ∧ HallRainbow1121.Rainbow G f}
  have feasible : sizes.Nonempty := ⟨_, fun _ => 1, rfl,
    fun _ hv => False.elim ((by decide : (1 : Fin 3) ≠ 0) hv)⟩
  obtain ⟨f,cost,hf'⟩ := Nat.sInf_mem feasible
  change HallRainbow1121.weight f = HallRainbow1121.rainbowNumber G 2 at cost
  simpa [hi.card_eq,cost] using independent_le_weight G hf I hi.isIndepSet f hf'

#print axioms independent_le_weight
#print axioms row579
end RainbowIndependent579
