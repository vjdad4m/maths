import PrivateAnchor180

set_option warningAsError true
namespace Minimal180.PrivateCore
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Private leaves at different core vertices are disjoint. -/
theorem private_disjoint (J : SimpleGraph V) (C : Finset V) (x : V)
    {z t : V} (ts : t∈univ\C) (ne : z≠t) :
    Disjoint (privateLeaves J C x z) (privateLeaves J C x t) := by
  apply disjoint_left.mpr
  intro q qz qt
  exact ne (((private_iff ..).mp qz).2.2 t ts ((private_iff ..).mp qt).2.1).symm

/-- An injective charging bound for any family of failed non-cut releases.
A leaf may be counted twice only if it is outside the closed old radius-two
ball of x. P and D may be any upper bounds on the two pools. -/
theorem private_packing (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (U C F P D : Finset V) (x y : V) (xy : x≠y) (cu : C⊆U) (ct : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (free : F⊆(U\C).erase y)
    (safe : ∀ z∈F, Con J ((univ\C).erase z))
    (fail : ∀ z∈F, ¬SingleWorks J C x y z)
    (pool : ∀ z∈F, privateLeaves J C x z⊆P)
    (dark : ∀ q∈P, ¬NearTwo J x q → q∈D) :
    2*F.card ≤ P.card+D.card := by
  classical
  let g := privateLeaves J C x
  let h (z : V) := g z ∩ D
  have dis : (F:Set V).PairwiseDisjoint g := by
    intro z _ t ht ne
    apply private_disjoint J C x _ ne
    exact mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp (mem_of_mem_erase (free ht))).2⟩
  have dis' : (F:Set V).PairwiseDisjoint h := by
    intro z hz t ht ne
    exact (dis hz ht ne).mono (inter_subset_left (s₂:=D)) inter_subset_left
  have two (z : V) (hz : z∈F) : 2 ≤ (g z).card+(h z).card := by
    have pos : (g z).Nonempty := by
      obtain k|⟨q,qc,_,qz,unique⟩ := (single_failure_iff J C x y z xy tip
        (mem_sdiff.mp (mem_of_mem_erase (free hz))).2 (mem_erase.mp (free hz)).1).mp (fail z hz)
      · exact (k (safe z hz)).elim
      exact ⟨q,(private_iff ..).mpr ⟨qc,qz,unique⟩⟩
    by_cases big : 2≤(g z).card
    · omega
    have one : (g z).card=1 := by have := card_pos.mpr pos; omega
    obtain ⟨q,eq⟩ := card_eq_one.mp one
    have qz : q∈g z := eq ▸ mem_singleton_self q
    have far := singleton_far J hc hn U C x y z q xy cu ct tip (free hz) (safe z hz) (fail z hz) eq
    have hpos : (h z).Nonempty := ⟨q,mem_inter.mpr ⟨qz,dark q (pool z hz qz) far⟩⟩
    have := card_pos.mpr hpos
    omega
  have unionP : F.biUnion g⊆P := by
    intro q hq
    obtain ⟨z,hz,hqz⟩ := mem_biUnion.mp hq
    exact pool z hz hqz
  have unionD : F.biUnion h⊆D := by
    intro q hq
    obtain ⟨z,_,hm⟩ := mem_biUnion.mp hq
    exact (mem_inter.mp hm).2
  calc
    2*F.card = ∑ _z ∈ F, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ z ∈ F, ((g z).card+(h z).card) := sum_le_sum two
    _ = (F.biUnion g).card+(F.biUnion h).card := by rw [sum_add_distrib,card_biUnion dis,card_biUnion dis']
    _ ≤ P.card+D.card := Nat.add_le_add (card_le_card unionP) (card_le_card unionD)

/-- Winning single release and rooted first form under the strict packing
inequality. For a two-connected old core the deletion premise is automatic. -/
theorem first_of_private_packing (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (U C K P D : Finset V) (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (cu : C⊆U) (ct : C.card=weightedLeaves J U+1) (tip : NeedsTip J C (univ\C) x y)
    (free : K⊆(U\C).erase y) (safe : ∀ z∈K, Con J ((univ\C).erase z))
    (pool : ∀ z∈K, privateLeaves J C x z⊆P) (dark : ∀ q∈P, ¬NearTwo J x q → q∈D)
    (short : P.card+D.card<2*K.card) :
    (∃ z∈K, SingleWorks J C x y z) ∧ FirstForm J U x y w := by
  classical
  have win : ∃ z∈K, SingleWorks J C x y z := by
    by_contra none
    push_neg at none
    exact (Nat.not_le_of_lt short) (private_packing J hc hn U C K P D x y xy cu ct tip free safe none pool dark)
  obtain ⟨z,hz,works⟩ := win
  refine ⟨⟨z,hz,works⟩,(second_split_iff J hc hn x y w xy old xw wy U C cu ct tip).mpr ?_⟩
  refine ⟨∅,empty_subset _,{z},singleton_subset_iff.mpr (free hz),by simp,?_⟩
  have e : C.erase x ∪ {z} = insert z (C.erase x) := by ext a; simp [or_comm]
  simpa only [sdiff_empty,e,SingleWorks] using works

#print axioms private_packing
#print axioms first_of_private_packing
end Minimal180.PrivateCore
