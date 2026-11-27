import Join180

set_option warningAsError true
namespace Assembly180
open Finset SimpleGraph Graffiti177 Converse180 Rooted180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem tree_opt (H : SimpleGraph V) (hc : H.Connected) (U : Finset V) :
    ∃ K ≤ H, K.IsTree ∧ (U ∩ leaves K).card = weightedLeaves H U := by
  classical
  obtain ⟨T,st,tr⟩ := hc.exists_isTree_le
  obtain ⟨K,h,e⟩ := exists_mem_eq_sup (s:=univ.filter (fun J : SimpleGraph V => J ≤ H ∧ J.IsTree))
    (f:=fun J => (U ∩ leaves J).card) ⟨T,mem_filter.mpr ⟨mem_univ _,st,tr⟩⟩
  exact ⟨K,(mem_filter.mp h).2.1,(mem_filter.mp h).2.2,e.symm⟩

noncomputable abbrev emb (S : Finset V) : ↥S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩

/-- A leaf distinct from the seam has all its neighbors in its original side. -/
private theorem preserve {c : V} {S T : Finset V} (s : Split G c S T)
    (K : SimpleGraph ↥S) (J : SimpleGraph ↥T) (H : SimpleGraph V) (ht : H.IsTree)
    (sub : H ≤ K.map (emb S) ⊔ J.map (emb T)) (v : ↥S) (ne : v.val≠c) (leaf : v∈leaves K) :
    v.val∈leaves H := by
  classical
  have hn := s.largeL
  have small := s.smallL
  rw [Fintype.card_coe] at hn
  apply leaf_of_unique H ht.isConnected (by omega)
  have inside {w} (e : H.Adj v.val w) : ∃ b : ↥S, K.Adj v b ∧ b.val=w := by
    rcases sub e with p|p
    · obtain ⟨a,b,ab,av,bw⟩ := p
      exact ⟨b,(Subtype.ext av : a=v) ▸ ab,bw⟩
    · obtain ⟨a,b,_,av,_⟩ := p
      exact (ne (s.common v.property ((show a.val=v.val from av) ▸ a.property))).elim
  intro a b e f
  obtain ⟨i,vi,rfl⟩ := inside e
  obtain ⟨j,vj,rfl⟩ := inside f
  exact congrArg Subtype.val (leaf_unique K leaf vi vj)

namespace Split
variable {c : V} {S T : Finset V} (s : Split G c S T)
include s
/-- The two weighted optima away from the common vertex can be realized
simultaneously in the ambient graph. -/
theorem leaf_join (hc : G.Connected) (U : Finset V) :
    weightedLeaves (side G S) (pull (fun v : ↥S => v.val) (U.erase c)) +
    weightedLeaves (side G T) (pull (fun v : ↥T => v.val) (U.erase c)) ≤ weightedLeaves G U := by
  classical
  let L := pull (fun v : ↥S => v.val) (U.erase c)
  let R := pull (fun v : ↥T => v.val) (U.erase c)
  obtain ⟨K,ks,kt,ke⟩ := tree_opt _ (s.connectedL hc) L
  obtain ⟨J,js,jt,je⟩ := tree_opt _ (s.flip.connectedL hc) R
  let H := K.map (emb S) ⊔ J.map (emb T)
  let f : K →g H := ⟨Subtype.val,fun {a b} e => Or.inl ⟨a,b,e,rfl,rfl⟩⟩
  let g : J →g H := ⟨Subtype.val,fun {a b} e => Or.inr ⟨a,b,e,rfl,rfl⟩⟩
  have ch : H.Connected := by
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨c,fun v => ?_⟩
    rcases s.either v with h|h
    · exact (kt.isConnected (⟨c,s.both.1⟩ : ↥S) ⟨v,h⟩).map f
    · exact (jt.isConnected (⟨c,s.both.2⟩ : ↥T) ⟨v,h⟩).map g
  obtain ⟨M,ms,mt⟩ := ch.exists_isTree_le
  have mg : M ≤ G := by
    intro v w e
    rcases ms e with ⟨a,b,ab,rfl,rfl⟩|⟨a,b,ab,rfl,rfl⟩
    · exact ks ab
    · exact js ab
  let A := L ∩ leaves K
  let B := R ∩ leaves J
  have propL {v : ↥S} (h : v ∈ A) : v.val≠c ∧ v.val∈U := mem_erase.mp (mem_pull.mp (mem_inter.mp h).1)
  have propR {v : ↥T} (h : v ∈ B) : v.val≠c ∧ v.val∈U := mem_erase.mp (mem_pull.mp (mem_inter.mp h).1)
  have dis : Disjoint (push A) (push B) := by
    apply disjoint_left.mpr
    intro v a b
    obtain ⟨i,hi,rfl⟩ := mem_map.mp a
    exact (propL hi).1 (s.common i.property (push_sub _ b))
  have lower : push A ∪ push B ⊆ U ∩ leaves M := by
    intro v h
    rcases mem_union.mp h with a|b
    · obtain ⟨i,hi,rfl⟩ := mem_map.mp a
      exact mem_inter.mpr ⟨(propL hi).2,preserve s K J M mt ms i (propL hi).1 (mem_inter.mp hi).2⟩
    · obtain ⟨i,hi,rfl⟩ := mem_map.mp b
      have rev : M ≤ J.map (emb T) ⊔ K.map (emb S) := by rw [sup_comm]; exact ms
      exact mem_inter.mpr ⟨(propR hi).2,preserve s.flip J K M mt rev i (propR hi).1 (mem_inter.mp hi).2⟩
  have size := (card_le_card lower).trans (le_sup (s:=univ.filter (fun Q : SimpleGraph V => Q≤G ∧ Q.IsTree))
    (f:=fun Q => (U ∩ leaves Q).card) (mem_filter.mpr ⟨mem_univ _,mg,mt⟩))
  rw [card_union_of_disjoint dis,card_push,card_push] at size
  change A.card+B.card ≤ weightedLeaves G U at size
  exact (ke ▸ je ▸ size)

end Split
#print axioms Split.leaf_join
end Assembly180
