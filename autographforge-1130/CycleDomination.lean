import CycleCore

namespace CycleBatch
open SimpleGraph Finset PathCycleSharpness

def Total {U : Type*} (G : SimpleGraph U) (S : Finset U) := ∀ v, ∃ u ∈ S, G.Adj u v
noncomputable def totalNumber {U : Type*} [Fintype U] (G : SimpleGraph U) :=
  sInf {k | ∃ S : Finset U, S.card = k ∧ Total G S}

theorem total43 : totalNumber C = 22 := by
  let S := univ.filter (fun v : V => v.val % 4 = 1 ∨ v.val % 4 = 2)
  let sizes := {k | ∃ S : Finset V, S.card = k ∧ Total C S}
  have good : 22 ∈ sizes := ⟨S,by decide,by unfold Total; decide⟩
  obtain ⟨B,cost,hB⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨_,good⟩)
  have covers : univ ⊆ B.biUnion (fun v => C.neighborFinset v) := by
    intro v _
    obtain ⟨u,hu,uv⟩ := hB v
    exact mem_biUnion.mpr ⟨u,hu,(C.mem_neighborFinset u v).mpr uv⟩
  have cap := (card_le_card covers).trans card_biUnion_le
  change Fintype.card V ≤ ∑ u ∈ B, C.degree u at cap
  simp only [Fintype.card_fin,deg,sum_const,smul_eq_mul] at cap
  change B.card = totalNumber C at cost
  exact le_antisymm (Nat.sInf_le good) (by omega)

def Rainbow2 {U : Type*} (G : SimpleGraph U) (f : U → Fin 3) :=
  ∀ v, f v = 0 → ∀ c : Fin 3, c ≠ 0 → ∃ u, G.Adj v u ∧ f u = c

def weight {U : Type*} [Fintype U] (f : U → Fin 3) := (univ.filter fun v => f v ≠ 0).card

noncomputable def rainbow2 {U : Type*} [Fintype U] (G : SimpleGraph U) :=
  sInf {n | ∃ f : U → Fin 3, weight f = n ∧ Rainbow2 G f}

/-- A 2-rainbow labeling on a graph of maximum degree two has at least as
many colored as uncolored vertices, by counting their incidences. -/
theorem rainbow_half {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj]
    (degree : ∀ u, G.degree u ≤ 2) : Fintype.card U ≤ 2 * rainbow2 G := by
  classical
  let sizes := {n | ∃ f : U → Fin 3, weight f = n ∧ Rainbow2 G f}
  have feasible : sizes.Nonempty :=
    ⟨_,fun _ => 1,rfl,fun _ hv => False.elim ((by decide : (1 : Fin 3) ≠ 0) hv)⟩
  obtain ⟨f,cost,hf⟩ := Nat.sInf_mem feasible
  let B := univ.filter (fun u => f u ≠ 0)
  have dem (x : U) (hx : x ∈ univ \ B) : 2 ≤ (B.bipartiteAbove G.Adj x).card := by
    have zero : f x = 0 := by simpa [B] using (mem_sdiff.mp hx).2
    obtain ⟨u,xu,hu⟩ := hf x zero 1 (by decide)
    obtain ⟨v,xv,hv⟩ := hf x zero 2 (by decide)
    apply one_lt_card.mpr
    exact ⟨u, (mem_bipartiteAbove _).mpr ⟨by simp [B,hu],xu⟩,
      v, (mem_bipartiteAbove _).mpr ⟨by simp [B,hv],xv⟩,fun e => by
        subst v; rw [hu] at hv; exact (by decide : (1 : Fin 3) ≠ 2) hv⟩
  have supply (y : U) (_ : y ∈ B) : ((univ \ B).bipartiteBelow G.Adj y).card ≤ 2 := by
    apply le_trans (card_le_card ?_) (degree y)
    intro x hx
    exact (G.mem_neighborFinset y x).mpr ((mem_bipartiteBelow _).mp hx).2.symm
  have h := Finset.card_mul_le_card_mul G.Adj dem supply
  have sz := Finset.card_sdiff_add_card_eq_card (s:=B) (t:=univ) (subset_univ B)
  rw [card_univ] at sz
  change B.card = rainbow2 G at cost
  omega

theorem rainbow43 : rainbow2 C = 22 := by
  let f (v : V) : Fin 3 := if v.val % 2 = 1 then 0 else if v.val / 2 % 2 = 0 then 1 else 2
  have good : Rainbow2 C f := by unfold Rainbow2; decide
  have upper : rainbow2 C ≤ 22 := Nat.sInf_le ⟨f,by decide,good⟩
  have lower := rainbow_half C (fun v => (deg v).le)
  rw [Fintype.card_fin] at lower
  omega

/-- The same nonempty-complement convention as row 370 and GraphCalc. -/
def Outer {U : Type*} (G : SimpleGraph U) (D : Finset U) :=
  (∀ x ∉ D, ∃ y ∈ D, G.Adj x y) ∧ (G.induce (D : Set U)ᶜ).Connected

noncomputable def outerNumber {U : Type*} [Fintype U] (G : SimpleGraph U) : Option ℕ := by
  classical
  exact if h : ∃ k, ∃ D : Finset U, Outer G D ∧ D.card = k then some (Nat.find h) else none

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
    (degree : ∀ u, G.degree u ≤ 2) (D : Finset U) (hd : Outer G D) : Fintype.card U ≤ D.card+2 := by
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

theorem outer43 : outerNumber C = some 41 := by
  classical
  let D : Finset V := univ \ {0,1}
  have valid : Outer C D := by
    constructor
    · change ∀ x : V, x ∉ univ \ {0,1} → ∃ y ∈ univ \ ({0,1} : Finset V), C.Adj x y
      decide
    · let T := C.induce (D : Set V)ᶜ
      have choices (x : ↥((D : Set V)ᶜ)) : x.val=0 ∨ x.val=1 := by
        by_cases h : x.val=0
        · exact Or.inl h
        · exact Or.inr (by simpa [D,h] using x.property)
      have nonempty : Nonempty ↥((D : Set V)ᶜ) := ⟨⟨0,by simp [D]⟩⟩
      refine ⟨fun x y => ?_⟩
      by_cases h : x=y
      · subst y; exact Reachable.rfl
      · apply Adj.reachable
        change C.Adj x.val y.val
        rcases choices x with hx|hx <;> rcases choices y with hy|hy
        all_goals first | exact (h (Subtype.ext (hx.trans hy.symm))).elim | rw [hx,hy]; decide
  have card : D.card=41 := by decide
  have feasible : ∃ k, ∃ D : Finset V, Outer C D ∧ D.card = k := ⟨41,D,valid,card⟩
  simp only [outerNumber, dif_pos feasible,Option.some.injEq]
  apply le_antisymm (Nat.find_min' feasible ⟨D,valid,card⟩)
  obtain ⟨D,hD,eq⟩ := Nat.find_spec feasible
  have lb := outer_budget C (fun v => (deg v).le) D hD
  rw [Fintype.card_fin,eq] at lb
  omega

theorem burning160 : burning (cycleGraph 160) ≤ 13 := by
  let G := cycleGraph 160
  have hc : G.Connected := cycleGraph_connected (n:=159)
  apply Nat.sInf_le
  apply TraceableBurn.burns_of_cover hc
  apply TraceableBurn.cover_of_enumeration hc (n:=160) (by decide) (by decide) (Equiv.refl _)
  intro i j hij
  change G.Adj i j
  apply cycleGraph_adj'.mpr
  right
  have hle : i ≤ j := by change i.val ≤ j.val; omega
  rw [Fin.sub_val_of_le hle]
  omega
end CycleBatch
