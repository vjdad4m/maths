import DegreeFiveAlternatingBlock189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem route_clique_join_end_leaf_with_extra_block {H P : Finset V} {x y : V}
    (dis : Disjoint H P) (cl : CompleteOn G H)
    (cross : ∀ h∈H,∀ p∈P,G.Adj h p)
    (cap : P.card≤H.card+1) (xh : x∈H) (yp : y∈P)
    (pair : H.card<P.card → ∃ s∈P,∃ t∈P,G.Adj s t) :
    ∃ p∈H,RouteOn G (H∪P) p y := by
  classical
  have xy' := cross x xh y yp
  by_cases small : P.card≤H.card
  · exact route_clique_join_end_leaf dis cl
      (fun h hh p pp=>cross h hh p (mem_erase.mp pp).2) small xh yp xy'
  obtain ⟨s,sp,t,tp,st⟩ := pair (by omega)
  have block (s t : V) (sp : s∈P) (tp : t∈P) (st : G.Adj s t) :
      ∃ p∈H,RouteOn G (H∪P) p y := by
    let B := ({s,t} : Finset V)
    let L := P\B
    have sub : B⊆P := insert_subset_iff.mpr ⟨sp,singleton_subset_iff.mpr tp⟩
    have lsub : L⊆P := sdiff_subset
    have b2 : B.card=2 := by simp [B,st.ne]
    have lsize : L.card=P.card-2 := by
      change (P\B).card=P.card-2
      rw [card_sdiff sub,b2]
    have llt : L.card<H.card := by have bLe := card_le_card sub; omega
    have lplus : L.card+1≤H.card := by omega
    have sOff : s∉H∪L := by
      intro h
      exact (mem_union.mp h).elim (fun a=>disjoint_left.mp dis a sp)
        (fun l=>(mem_sdiff.mp l).2 (by simp [B]))
    have tOff : t∉H∪L := by
      intro h
      exact (mem_union.mp h).elim (fun a=>disjoint_left.mp dis a tp)
        (fun l=>(mem_sdiff.mp l).2 (by simp [B]))
    have cover : (H∪L)∪B=H∪P := by
      have e : L∪B=P := sdiff_union_of_subset sub
      rw [union_assoc,e]
    by_cases ty : t=y
    · subst t
      have no (h : V) (hh : h∈H) (l : V) (ll : l∈L) : G.Adj h l :=
        cross h hh l (lsub ll)
      obtain ⟨p,pp,route⟩ := route_clique_join_end_block (dis.mono (Subset.refl _) lsub)
        cl no sOff tOff llt xh (cross x xh s sp) st
      exact ⟨p,pp,cover ▸ route⟩
    by_cases sy : s=y
    · subst s
      have no (h : V) (hh : h∈H) (l : V) (ll : l∈L) : G.Adj h l :=
        cross h hh l (lsub ll)
      obtain ⟨p,pp,route⟩ := route_clique_join_end_block (dis.mono (Subset.refl _) lsub)
        cl no tOff sOff llt xh (cross x xh t tp) st.symm
      have eq : (H∪L)∪({t,y} : Finset V)=(H∪L)∪B := by ext w; simp [B,or_comm,or_left_comm,or_assoc]
      exact ⟨p,pp,eq.trans cover ▸ route⟩
    have yy : y∈L := mem_sdiff.mpr ⟨yp,by simp [B,show y≠s from fun e=>sy e.symm,show y≠t from fun e=>ty e.symm]⟩
    obtain ⟨p,pp,route⟩ := route_clique_join_block_before_leaf
      (dis.mono (Subset.refl _) lsub) cl
      (fun h hh u uu=>cross h hh u (lsub (mem_erase.mp uu).2))
      (fun h hh=>cross h hh s sp) (fun h hh=>(cross h hh t tp).symm)
      sOff tOff st lplus xh yy xy'
    exact ⟨p,pp,cover ▸ route⟩
  exact block s t sp tp st

#print axioms route_clique_join_end_leaf_with_extra_block
end Graffiti189LongestPath.CrossSaturation
