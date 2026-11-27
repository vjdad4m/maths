import OddWing180
import WingRank180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a nonbipartite graph, deleting a compulsory vertex from a maximum
bipartite witness cannot bipartize the whole graph. -/
theorem odd_after_tip {J : SimpleGraph V} {a : V} (odd : ¬TwoColor J univ)
    (forced : ∀ B, MaxSet J B → a∈B) : ¬TwoColor J (univ.erase a) := by
  classical
  intro col
  have room : bipartiteNum J<Fintype.card V := by
    obtain ⟨B,b,top⟩ := optB J
    have h : B≠univ := fun e => odd (e ▸ b)
    rw [←top,←card_univ]
    exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,h⟩)
  have n := card_erase_add_one (mem_univ a)
  rw [card_univ] at n
  have b := size_bip J col
  have pin := forced (univ.erase a) ⟨col,by omega⟩
  exact (mem_erase.mp pin).1 rfl

/-- Both tips separately leave odd obstructions even when the whole lower
graph is already a block and no cut decomposition is available. -/
theorem lower_without_either_tip {J : SimpleGraph V} {x y : V} (xy : x≠y) (odd : ¬TwoColor J univ)
    (drop : bipartiteNum (J⊔edge x y)<bipartiteNum J) :
    ¬TwoColor J (univ.erase x) ∧ ¬TwoColor J (univ.erase y) := by
  have pins (B : Finset V) (top : MaxSet J B) : x∈B ∧ y∈B := by
    obtain ⟨c,pc⟩ := (color_function J B).mp top.1
    obtain ⟨xb,yb,_⟩ := rank_forces_route J x y xy drop B top c pc
    exact ⟨xb,yb⟩
  exact ⟨odd_after_tip odd (fun B h => (pins B h).1),odd_after_tip odd (fun B h => (pins B h).2)⟩

/-- The least numbers of bipartization deletions add exactly in the two
lower wings when the chord lowers the bipartite order. -/
theorem seam_deficit {J : SimpleGraph V} {x y w : V} {S T : Finset V} (s : Split J w S T)
    (xs : x∈S) (ys : y∉S) (xy : x≠y) (drop : bipartiteNum (J⊔edge x y)<bipartiteNum J) :
    (S.card-bipartiteNum (side J S))+(T.card-bipartiteNum (side J T))=Fintype.card V-bipartiteNum J := by
  classical
  obtain ⟨B,bip,size⟩ := optB J
  have wb := (locked_seam s xs ys xy drop ⟨bip,size⟩).2.1
  have ranks := (exact_wing_scores s ⟨bip,size⟩ wb).2.2
  have card := card_union_add_card_inter S T
  rw [s.cover,s.meet,card_univ,card_singleton] at card
  have upper (Q : Finset V) : bipartiteNum (side J Q)≤Q.card := by
    obtain ⟨L,_,h⟩ := optB (side J Q)
    have bound : L.card≤Fintype.card ↥Q := L.card_le_univ
    rw [Fintype.card_coe] at bound
    omega
  have l := upper S
  have r := upper T
  omega

/-- At lower bipartization deficit one, a proper separation can have
only one nontrivial wing. The other is a pendant triangle tip. -/
theorem one_defect_pendant {J : SimpleGraph V} {x y w : V} {S T : Finset V}
    (s : Split J w S T) (left : OddWing J S x w) (right : OddWing J T y w)
    (one : bipartiteNum J+1=Fintype.card V) : S={x,w} ∨ T={y,w} := by
  classical
  rcases left.2.2 with l|l
  · exact Or.inl l
  rcases right.2.2 with r|r
  · exact Or.inr r
  exfalso
  obtain ⟨B,bip,size⟩ := optB J
  obtain ⟨c,pc⟩ := (color_function J B).mp bip
  have miss (Q : Finset V) (odd : ¬TwoColor J Q) : ∃ i∈Q,i∉B := by
    apply Finset.not_subset.mp
    exact fun h => odd ((color_function J Q).mpr ⟨c,fun i hi j hj e => pc i (h hi) j (h hj) e⟩)
  obtain ⟨i,hi,ib⟩ := miss _ l.1
  obtain ⟨j,hj,jb⟩ := miss _ r.1
  have ne : i≠j := by
    rintro rfl
    exact (mem_erase.mp hi).1 (s.common (mem_of_mem_erase hi) (mem_of_mem_erase hj))
  have cap := card_le_card (show ({i,j}:Finset V)⊆univ\B from insert_subset
    (mem_sdiff.mpr ⟨mem_univ _,ib⟩) (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_univ _,jb⟩)))
  rw [card_pair ne] at cap
  have room := card_sdiff_add_card_eq_card (subset_univ B)
  rw [card_univ] at room
  omega

#print axioms odd_after_tip
#print axioms lower_without_either_tip
#print axioms seam_deficit
#print axioms one_defect_pendant
end Minimal180.OddBlock
