import GadgetTools180

set_option warningAsError true
namespace Converse180
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

abbrev Deco (D : Finset V) := V ⊕ ↥D
noncomputable def decorate (D : Finset V) : SimpleGraph (Deco D) where
  Adj := Sum.elim (fun a => Sum.elim (G.Adj a) (fun b => a = b.val))
    (fun a => Sum.elim (fun b => a.val = b) (fun _ => False))
  symm := by rintro (a|a) (b|b) e <;> first | exact e.symm | exact e.elim
  loopless := by rintro (a|a) e; exact G.loopless a e; exact e

noncomputable def project (D : Finset V) : Deco D → V := Sum.elim id Subtype.val

omit [Fintype V] [DecidableEq V] in
theorem deco_layers (hc : G.Connected) (r : V) (D : Finset V) :
    let H := decorate G D
    H.Connected ∧ ∀ v, H.dist v (.inl r) =
      Sum.elim (fun a => G.dist a r) (fun a : ↥D => G.dist a.val r + 1) v := by
  dsimp only
  apply layers
  · exact G.dist_self
  · rintro (a|a) (b|b) e
    · have h := hc.dist_triangle (u:=a) (v:=b) (w:=r)
      rw [dist_eq_one_iff_adj.mpr (show G.Adj a b from e)] at h
      change G.dist a r ≤ G.dist b r + 1
      omega
    · change a = b.val at e
      change G.dist a r ≤ G.dist b.val r + 1 + 1
      rw [e]; omega
    · change a.val = b at e
      change G.dist a.val r + 1 ≤ G.dist b r + 1
      rw [e]
    · exact e.elim
  · rintro (v|v) ne
    · obtain ⟨w,e,d⟩ := Graffiti169.exists_predecessor G hc r v (fun h => ne (congrArg Sum.inl h))
      exact ⟨.inl w,e,d⟩
    · exact ⟨.inl v.val,rfl,rfl⟩

theorem deco_bip (D : Finset V) : bipartiteNum (decorate G D) ≤ bipartiteNum G + D.card := by
  classical
  apply Finset.sup_le
  intro S h
  have col := restrict_color G (decorate G D) Sum.inl Sum.inl_injective
    (fun {_ _} e => e) (mem_filter.mp h).2
  have small := le_sup (f := card) (s := univ.filter (TwoColor G)) (mem_filter.mpr ⟨mem_univ _,col⟩)
  have rest := card_le_univ (pull (Sum.inr : ↥D → Deco D) S)
  rw [Fintype.card_coe] at rest
  rw [split_card S]
  change _ ≤ bipartiteNum G + D.card
  exact Nat.add_le_add small rest

omit [Fintype V] [DecidableEq V] in
theorem deco_indep (D A : Finset V) (ai : Indep G A) (dis : Disjoint A D) :
    Indep (decorate G D) (A.disjSum univ) := by
  classical
  rintro (a|a) ha (b|b) hb ne e
  · exact ai a (inl_mem_disjSum.mp ha) b (inl_mem_disjSum.mp hb)
      (fun h => ne (congrArg Sum.inl h)) e
  · exact Finset.disjoint_left.mp dis (inl_mem_disjSum.mp ha)
      ((show a=b.val from e).symm ▸ b.property)
  · exact Finset.disjoint_left.mp dis (inl_mem_disjSum.mp hb) ((show a.val=b from e) ▸ a.property)
  · exact e.elim

theorem deco_leaves (hn : 1 < Fintype.card V) (D B : Finset V) :
    weightedLeaves (decorate G D) (B.disjSum univ) ≤ weightedLeaves G (B \ D) + D.card := by
  classical
  apply Finset.sup_le
  intro T ht
  obtain ⟨st,tr⟩ := (mem_filter.mp ht).2
  have step {a b : Deco D} (e : T.Adj a b) :
      project D a = project D b ∨ T.Adj (.inl (project D a)) (.inl (project D b)) := by
    have h := st e
    cases a <;> cases b
    · exact Or.inr e
    · exact Or.inl h
    · exact Or.inl h
    · exact h.elim
  obtain ⟨K,ks,kt,map⟩ := tree_inside G T tr.isConnected Sum.inl (project D)
    (fun _ => rfl) (fun e => step e) (fun {_ _} e => st e)
  have ex (v : V) (bv : v ∈ B) (out : v ∉ B \ D) :
      ∃ w, T.Adj (.inl v) w ∧ ∀ u : V, w ≠ Sum.inl u := by
    have vd : v ∈ D := by by_contra no; exact out (mem_sdiff.mpr ⟨bv,no⟩)
    let t : ↥D := ⟨v,vd⟩
    have eg : T.Adj (.inr t) (.inl v) := by
      obtain ⟨w,e⟩ := exists_adj T tr.isConnected (by
        rw [Fintype.card_sum,Fintype.card_coe]; omega) (.inr t)
      have g := st e
      cases w with
      | inl w => exact (show v=w from g) ▸ e
      | inr w => exact g.elim
    exact ⟨.inr t,eg.symm,fun _ => Sum.noConfusion⟩
  have bound := piece_leaves G hn T Sum.inl Sum.inl_injective ks kt map (B \ D) B ex
  let S := (B.disjSum (univ : Finset ↥D)) ∩ leaves T
  have eq : pull Sum.inl S = B ∩ pull Sum.inl (leaves T) := by ext x; simp [S]
  have count := split_card S
  rw [eq] at count
  have rest := card_le_univ (pull Sum.inr S)
  rw [Fintype.card_coe] at rest
  change S.card ≤ weightedLeaves G (B \ D) + D.card
  omega

#print axioms deco_layers
#print axioms deco_bip
#print axioms deco_indep
#print axioms deco_leaves
end Converse180
