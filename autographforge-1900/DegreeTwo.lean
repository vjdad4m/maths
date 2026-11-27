import OuterForest
import Lean.Elab.Tactic.Omega

/-! The degree-two complement bound from the public C43 certificate. -/
namespace OuterStar1900
open Finset SimpleGraph AutoGraphForge370
private theorem near_of_walk {U : Type*} {G : SimpleGraph U}
    (one : ∀ z x y, G.Adj z x → G.Adj z y → x=y)
    {u v : U} (p : G.Walk u v) : u=v ∨ G.Adj u v := by
  induction p with
  | nil => exact Or.inl rfl
  | cons e _ ih =>
    rcases ih with h|h
    · exact Or.inr (h ▸ e)
    · exact Or.inl (one _ _ _ e.symm h)

/-- In maximum degree two, a proper outer-connected dominating set leaves at
most two vertices: every vertex outside has at most one neighbor outside. -/
theorem outer_budget {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj]
    (degree : ∀ u, G.degree u ≤ 2) (D : Finset U) (hd : OuterDominating G D) : Fintype.card U ≤ D.card+2 := by
  classical
  let T := G.induce (D : Set U)ᶜ
  have one (z x y : ↥((D : Set U)ᶜ)) (zx : T.Adj z x) (zy : T.Adj z y) : x=y := by
    by_contra ne
    obtain ⟨w,hw,zw⟩ := hd.1 z.val z.property
    have cap := degree z.val
    have many : 2 < (G.neighborFinset z.val).card := two_lt_card_iff.mpr
      ⟨x.val,y.val,w,(G.mem_neighborFinset _ _).mpr zx,(G.mem_neighborFinset _ _).mpr zy,
       (G.mem_neighborFinset _ _).mpr zw,fun h => ne (Subtype.ext h),
       fun h => x.property (h ▸ hw), fun h => y.property (h ▸ hw)⟩
    exact (Nat.not_lt_of_ge cap) many
  have near (x y : ↥((D : Set U)ᶜ)) : x=y ∨ T.Adj x y := by
    obtain ⟨p⟩ := hd.2 x y
    exact near_of_walk one p
  have small : (univ \ D).card ≤ 2 := by
    by_contra! bad
    obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp bad
    let A : ↥((D : Set U)ᶜ) := ⟨a,(mem_sdiff.mp ha).2⟩
    let B : ↥((D : Set U)ᶜ) := ⟨b,(mem_sdiff.mp hb).2⟩
    let E : ↥((D : Set U)ᶜ) := ⟨c,(mem_sdiff.mp hc).2⟩
    have eq := one A B E ((near A B).resolve_left (fun h => ab (congrArg Subtype.val h)))
      ((near A E).resolve_left (fun h => ac (congrArg Subtype.val h)))
    exact bc (congrArg Subtype.val eq)
  have h := card_sdiff_add_card_eq_card (s:=D) (t:=univ) (subset_univ D)
  rw [card_univ] at h
  omega

end OuterStar1900
