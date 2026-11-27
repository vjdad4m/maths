import Mathlib.SetTheory.Cardinal.Finite
import PowerBasis
import CographJoin

namespace Hereditary105
open Finset SimpleGraph AutoGraphPowerBurning
variable {V : Type*} (G : SimpleGraph V)

def Dominates {U : Type*} (H : SimpleGraph U) (S : Finset U) :=
  ∀ v, v ∈ S ∨ ∃ u ∈ S, H.Adj v u

noncomputable def domination := sInf {k | ∃ S : Finset V, S.card=k ∧ Dominates G S}

theorem dom_attained [Fintype V] : ∃ S : Finset V, S.card=domination G ∧ Dominates G S := by
  exact Nat.sInf_mem (s:={k | ∃ S : Finset V, S.card=k ∧ Dominates G S})
    ⟨_,univ,rfl,fun v => Or.inl (mem_univ v)⟩

theorem power_le_card {S : Finset V} (h : ∀ v, Observed G S v) : power G ≤ S.card :=
  Nat.sInf_le (s:={r | ∃ T : Finset V, r = T.card ∧ ∀ v, Observed G T v}) ⟨S,rfl,h⟩

theorem power_le_dom [Fintype V] : power G ≤ domination G := by
  obtain ⟨S,size,dom⟩ := dom_attained G
  rw [← size]
  apply power_le_card
  intro v
  obtain h|⟨u,hu,e⟩ := dom v
  · exact .root h
  · exact .neighbor hu e

/-- The number of connected components, including isolated vertices. -/
noncomputable def components := Nat.card G.ConnectedComponent

theorem components_le_power [Fintype V] : components G ≤ power G := by
  classical
  letI := Fintype.ofSurjective G.connectedComponentMk (fun c => c.exists_rep)
  obtain ⟨S,cost,allSeen⟩ := Nat.sInf_mem
    (s:={r | ∃ T : Finset V, r = T.card ∧ ∀ v, Observed G T v})
    ⟨_,univ,rfl,fun v => .root (mem_univ v)⟩
  have localSeed {v : V} (h : Observed G S v) : ∃ u ∈ S, G.connectedComponentMk u = G.connectedComponentMk v := by
    induction h with
    | root h => exact ⟨_,h,rfl⟩
    | neighbor h edge => exact ⟨_,h,ConnectedComponent.connectedComponentMk_eq_of_adj edge.symm⟩
    | force e _ _ ih _ =>
      obtain ⟨u,hu,eq⟩ := ih
      exact ⟨u,hu,eq.trans (ConnectedComponent.connectedComponentMk_eq_of_adj e.symm)⟩
  have onto : S.image G.connectedComponentMk = univ := by
    apply eq_univ_of_forall
    intro c
    obtain ⟨v,rfl⟩ := c.exists_rep
    exact mem_image.mpr (localSeed (allSeen v))
  change power G = S.card at cost
  rw [components,Nat.card_eq_fintype_card,cost,← card_univ,← onto]
  exact card_image_le

/-- A universal vertex of each component gives optimum seeds for both processes. -/
theorem exact_of_centers [Fintype V]
    (centers : ∀ c : G.ConnectedComponent, ∃ u ∈ c.supp, ∀ v ∈ c.supp, v ≠ u → G.Adj v u) :
    domination G = components G ∧ power G = components G := by
  classical
  letI := Fintype.ofSurjective G.connectedComponentMk (fun c => c.exists_rep)
  choose f member covers using centers
  let S := univ.image f
  have dominates : Dominates G S := by
    intro v
    let c := G.connectedComponentMk v
    have hf : f c ∈ S := mem_image.mpr ⟨c,mem_univ _,rfl⟩
    by_cases e : v = f c
    · exact Or.inl (e ▸ hf)
    · exact Or.inr ⟨f c,hf,covers c v rfl e⟩
  have cap : S.card ≤ components G := by
    rw [components,Nat.card_eq_fintype_card,← card_univ]
    exact card_image_le
  have hi : domination G ≤ S.card := Nat.sInf_le (s:={r | ∃ T : Finset V, T.card = r ∧ Dominates G T})
    ⟨S,rfl,dominates⟩
  have lo := components_le_power G
  have mid := power_le_dom G
  omega

end Hereditary105
