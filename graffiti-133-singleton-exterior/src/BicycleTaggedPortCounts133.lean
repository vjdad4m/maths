import BicycleTaggedFamily133

namespace Graffiti133Bicycle
open SimpleGraph Finset
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {B : Finset V}

noncomputable def TaggedFamily.siteNeighbors [DecidableRel G.Adj] (F : TaggedFamily G B) (z : V)
    (S : {S // S∈F.sets}) : Finset V :=
  S.val.filter (fun w=>G.Adj z w)

theorem TaggedFamily.site_neighbor_count [DecidableRel G.Adj] (F : TaggedFamily G B)
    (z : V) (zB : z∈B) (S : {S // S∈F.sets}) :
    (F.siteNeighbors z S).card =
      (if z=F.head S then 1 else 0)+(if z=(F.channel S).b then 1 else 0) := by
  letI : DecidableEq V := Classical.decEq _
  let P := F.channel S
  let a : Fin P.n := ⟨0,P.pos⟩
  let b : Fin P.n := ⟨P.n-1,by have h:=P.pos; omega⟩
  have mem (w : V) : w∈F.siteNeighbors z S ↔
      (z=F.head S ∧ w=(P.f a).val) ∨ (z=P.b ∧ w=(P.f b).val) := by
    constructor
    · intro wS
      obtain ⟨ws,wa⟩ := Finset.mem_filter.mp wS
      obtain ⟨i,q⟩ := P.spans (⟨w,ws⟩ : (S.val : Set V))
      have eq : (P.f i).val=w := congrArg Subtype.val q
      have ed : G.Adj z (P.f i).val := eq.symm ▸ wa
      rcases (P.attached i z zB).mp ed with ⟨v,e⟩|⟨v,e⟩
      · have ii : i=a := Fin.ext v
        exact Or.inl ⟨e,by rw [←ii,eq]⟩
      · have ii : i=b := Fin.ext (by change i.val=P.n-1; omega)
        exact Or.inr ⟨e,by rw [←ii,eq]⟩
    · rintro (⟨e,rfl⟩|⟨e,rfl⟩)
      · exact Finset.mem_filter.mpr ⟨(P.f a).property,
          (P.attached a z zB).mpr (Or.inl ⟨rfl,e⟩)⟩
      · exact Finset.mem_filter.mpr ⟨(P.f b).property,
          (P.attached b z zB).mpr (Or.inr ⟨by change P.n-1+1=P.n; have h:=P.pos; omega,e⟩)⟩
  change (F.siteNeighbors z S).card = (if z=F.head S then 1 else 0)+(if z=P.b then 1 else 0)
  by_cases za : z=F.head S <;> by_cases zb : z=P.b
  · have ne : (P.f a).val≠(P.f b).val := by
      intro eq
      have r := congrArg Fin.val (P.path.1 (Subtype.ext eq))
      change 0=P.n-1 at r
      have one : P.n=1 := by have hp:=P.pos; omega
      exact P.singletonNe one (zb.symm.trans za)
    have e : F.siteNeighbors z S = {(P.f a).val,(P.f b).val} := by ext w; rw [mem]; simp only [iff_true_intro za,iff_true_intro zb,true_and, Finset.mem_insert,Finset.mem_singleton]
    rw [e,if_pos za,if_pos zb]
    rw [Finset.card_insert_of_not_mem (by simp [ne]),Finset.card_singleton]
  · have e : F.siteNeighbors z S = {(P.f a).val} := by ext w; rw [mem]; simp only [iff_true_intro za,iff_false_intro zb,true_and,false_and,or_false,Finset.mem_singleton]
    rw [e,if_pos za,if_neg zb]
    simp
  · have e : F.siteNeighbors z S = {(P.f b).val} := by ext w; rw [mem]; simp only [iff_false_intro za,iff_true_intro zb,true_and,false_and,false_or,Finset.mem_singleton]
    rw [e,if_neg za,if_pos zb]
    simp
  · have e : F.siteNeighbors z S = ∅ := by ext w; rw [mem]; simp only [iff_false_intro za,iff_false_intro zb,false_and,or_false,Finset.not_mem_empty]
    rw [e,if_neg za,if_neg zb]
    simp

theorem TaggedFamily.outside_neighbor_count [DecidableRel G.Adj] (F : TaggedFamily G B)
    (z : V) (zB : z∈B) :
    ((G.neighborFinset z)\B).card = ∑ S∈F.sets.attach,
      ((if z=F.head S then 1 else 0)+(if z=(F.channel S).b then 1 else 0)) := by
  letI : DecidableEq V := Classical.decEq _
  have E : (G.neighborFinset z)\B = F.sets.attach.biUnion (F.siteNeighbors z) := by
    ext x
    constructor
    · intro h
      obtain ⟨a,b⟩ := Finset.mem_sdiff.mp h
      obtain ⟨S,sF,hs⟩ := F.cover _ b
      exact Finset.mem_biUnion.mpr
        ⟨⟨S,sF⟩,Finset.mem_attach _ _,Finset.mem_filter.mpr ⟨hs,(G.mem_neighborFinset z x).mp a⟩⟩
    · intro h
      obtain ⟨S,_,m⟩ := Finset.mem_biUnion.mp h
      obtain ⟨xs,ed⟩ := Finset.mem_filter.mp m
      exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset z x).mpr ed,
        fun b=>Finset.disjoint_left.mp (F.avoid _ S.property) xs b⟩
  have dis : (↑F.sets.attach : Set {S // S∈F.sets}).PairwiseDisjoint (F.siteNeighbors z) := by
    intro S hs T ht dst
    have ne : S.val≠T.val := fun e => dst (Subtype.ext e)
    apply Finset.disjoint_left.mpr
    intro x a b
    exact Finset.disjoint_left.mp (F.separate _ S.property _ T.property ne)
      (Finset.mem_filter.mp a).1 (Finset.mem_filter.mp b).1
  rw [E,Finset.card_biUnion dis]
  exact Finset.sum_congr rfl (fun _ _=>F.site_neighbor_count z zB _)

#print axioms TaggedFamily.site_neighbor_count
#print axioms TaggedFamily.outside_neighbor_count
end Graffiti133Bicycle
