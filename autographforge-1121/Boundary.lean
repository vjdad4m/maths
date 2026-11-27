import HallRainbow
import Mathlib.Data.Fintype.Sum

namespace HallRainbow1121
open SimpleGraph Finset
abbrev biclique (k m : ℕ) := completeBipartiteGraph (Fin k) (Fin m)

/-- The clique partition has one slot per vertex of the larger part. -/
theorem biclique_cover {k m : ℕ} (h : k ≤ m) : vertexCliqueCover (biclique k m) = m := by
  classical
  let slot : Fin k ⊕ Fin m → Fin m := Sum.elim (Fin.castLE h) id
  have proper {u v} (adj : (biclique k m)ᶜ.Adj u v) : slot u ≠ slot v := by
    obtain ⟨ne,no⟩ := ((biclique k m).compl_adj _ _).mp adj
    cases u with
    | inl a =>
      cases v with
      | inl b => exact fun e => ne (congrArg Sum.inl (Fin.ext (congrArg (fun j : Fin m => j.val) e)))
      | inr b => exact (no (by simp [biclique,completeBipartiteGraph])).elim
    | inr a =>
      cases v with
      | inl b => exact (no (by simp [biclique,completeBipartiteGraph])).elim
      | inr b => exact fun e => ne (congrArg Sum.inr e)
  have upper : (biclique k m)ᶜ.Colorable m := ⟨Coloring.mk slot proper⟩
  have att : (biclique k m)ᶜ.Colorable (vertexCliqueCover (biclique k m)) :=
    Nat.sInf_mem (s := {n | (biclique k m)ᶜ.Colorable n}) ⟨m,upper⟩
  obtain ⟨col⟩ := att
  have inj : Function.Injective (fun j : Fin m => col (Sum.inr j)) := by
    intro a b eq
    by_contra ne
    apply col.valid (_root_.SimpleGraph.compl_adj _ _ _ |>.mpr ⟨fun e => ne (Sum.inr.inj e),
      by simp [biclique,completeBipartiteGraph]⟩) eq
  exact le_antisymm (Nat.sInf_le upper) (by simpa using Fintype.card_le_of_injective _ inj)

/-- All k colors on the k-side suffice, and any labeling uses at least k
vertices: either the whole k-side is colored or a zero there sees all k colors. -/
theorem biclique_rainbow (k m : ℕ) : rainbowNumber (biclique k m) k = k := by
  classical
  let f : Fin k ⊕ Fin m → Fin (k+1) := Sum.elim Fin.succ (fun _ => 0)
  have rf : Rainbow (biclique k m) f := by
    rintro (v|v) hv c hc
    · exact (Fin.succ_ne_zero v hv).elim
    · obtain ⟨i,rfl⟩ := Fin.exists_succ_eq.mpr hc
      exact ⟨Sum.inl i,by simp [biclique,completeBipartiteGraph],rfl⟩
  have marked : univ.filter (fun v => f v ≠ 0) =
      (univ : Finset (Fin k)).image (Sum.inl : Fin k → Fin k ⊕ Fin m) := by
    ext v
    cases v <;> simp [f]
  have cost : weight f = k := by
    simp only [weight,marked,card_image_of_injective _ Sum.inl_injective,card_univ,Fintype.card_fin]
  let sizes := {n | ∃ f : Fin k ⊕ Fin m → Fin (k+1), weight f = n ∧ Rainbow (biclique k m) f}
  have good : k ∈ sizes := ⟨f,cost,rf⟩
  obtain ⟨g,eq,hg⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨k,good⟩)
  change weight g = rainbowNumber (biclique k m) k at eq
  apply le_antisymm (Nat.sInf_le good)
  change k ≤ rainbowNumber (biclique k m) k
  rw [← eq]
  suffices lower : (univ : Finset (Fin k)).card ≤ weight g by simpa using lower
  by_cases all : ∀ i : Fin k, g (Sum.inl i) ≠ 0
  · apply card_le_card_of_injOn Sum.inl ?_ Sum.inl_injective.injOn
    exact fun i _ => mem_filter.mpr ⟨mem_univ _,all i⟩
  · push_neg at all
    obtain ⟨i,hi⟩ := all
    have sees (j : Fin k) := hg (Sum.inl i) hi j.succ (Fin.succ_ne_zero j)
    choose pick _ color using sees
    have inj : Function.Injective pick := fun a b e =>
      Fin.succ_injective _ ((color a).symm.trans ((congrArg g e).trans (color b)))
    apply card_le_card_of_injOn pick ?_ inj.injOn
    exact fun j _ => mem_filter.mpr ⟨mem_univ _,(color j).symm ▸ Fin.succ_ne_zero j⟩

local instance (k m : ℕ) : DecidableRel (biclique k m).Adj := fun a b => by
  change Decidable (a.isLeft ∧ b.isRight ∨ a.isRight ∧ b.isLeft)
  infer_instance

/-- The degree threshold can already fail when the larger part has size k+1. -/
theorem biclique_degrees (k m : ℕ) :
    (∀ a : Fin k, (biclique k m).degree (Sum.inl a) = m) ∧
    (∀ b : Fin m, (biclique k m).degree (Sum.inr b) = k) := by
  classical
  constructor
  · intro a
    have neighbors : (biclique k m).neighborFinset (Sum.inl a) =
        (univ : Finset (Fin m)).image Sum.inr := by
      ext x
      cases x <;> simp [biclique,completeBipartiteGraph]
    rw [← SimpleGraph.card_neighborFinset_eq_degree,neighbors,
      card_image_of_injective _ Sum.inr_injective,card_univ,Fintype.card_fin]
  · intro b
    have neighbors : (biclique k m).neighborFinset (Sum.inr b) =
        (univ : Finset (Fin k)).image Sum.inl := by
      ext x
      cases x <;> simp [biclique,completeBipartiteGraph]
    rw [← SimpleGraph.card_neighborFinset_eq_degree,neighbors,
      card_image_of_injective _ Sum.inl_injective,card_univ,Fintype.card_fin]

/-- K(k,m) shows equality at m=k and arbitrary additive failure for m>k
when the maximum-degree hypothesis is removed. -/
theorem biclique_boundary {k m : ℕ} (h : k ≤ m) :
    vertexCliqueCover (biclique k m) = m ∧ rainbowNumber (biclique k m) k = k :=
  ⟨biclique_cover h,biclique_rainbow k m⟩

#print axioms biclique_degrees
#print axioms biclique_boundary
end HallRainbow1121
