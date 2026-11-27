import CoreSplit180
set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem second_scores (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) :
    let G := J⊔SimpleGraph.edge x y
    weightedLeaves G U=weightedLeaves J U+1 ∧
      (¬FirstForm J U x y w ↔ weightedLeaves G (U\{x,y})=weightedLeaves J U) := by
  classical
  let G := J⊔SimpleGraph.edge x y
  let S := univ\C
  let W := U\{x,y}
  have wc : w∈C := by by_contra nw; exact tip.2.2.2.1 ⟨w,by simp [nw],xw⟩
  have gain := (triangle_gain_iff_core J hc hn x y w xy old xw wy U).mpr
    ⟨C,cu,wc,count,Or.inr (Or.inl tip)⟩
  change weightedLeaves J U<weightedLeaves G U at gain
  obtain ⟨T,sub,tr,opt⟩ := tree_opt G (hc.mono le_sup_left) U
  obtain ⟨_,_,_,_,_,best,absent,eq,_⟩ := common_neighbor_rotation J T (by omega) x y w xy old xw wy U sub tr (opt ▸ gain)
  have one := congrArg card eq
  rw [card_insert_of_not_mem absent,best,opt] at one
  have sg : Con G S := tip.2.2.1.mono (fun _ _ e => Or.inl e)
  have edge : G.Adj x y := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,xy⟩)
  have cover (q:V) (out:q∉S) : Dominates G S q := by
    by_cases qx : q=x
    · subst q; exact ⟨y,tip.2.1,edge⟩
    obtain ⟨t,ts,e⟩ := tip.2.2.2.2 q (by simpa [S] using out) qx
    exact ⟨t,ts,Or.inl e⟩
  have subC : C.erase x⊆W\S := by
    intro q h
    obtain ⟨qx,qc⟩ := mem_erase.mp h
    have qy : q≠y := fun e => (mem_sdiff.mp tip.2.1).2 (e ▸ qc)
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨cu qc,by simp [qx,qy]⟩,by simp [S,qc]⟩
  have base := (card_le_card subC).trans (weightedCore G S W sg cover)
  have cut := card_erase_add_one tip.1
  refine ⟨one,?_⟩
  rw [first_iff_erased_gain J hc hn x y w xy old xw wy]
  change (¬weightedLeaves J U<weightedLeaves G W) ↔ weightedLeaves G W=weightedLeaves J U
  omega

#print axioms second_scores
end Minimal180
