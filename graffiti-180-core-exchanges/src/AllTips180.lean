import AllTipsScore180
import AllTipsRank180
import SecondScores180

set_option warningAsError true
namespace Minimal180.Case14
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180

/-- Whichever orientation or second certificate is chosen, every single exchange
fails. The same two-replacement first witness works for both orientations. -/
theorem all_second_stuck :
    Fintype.card V=14 ∧ G.Connected ∧ NoCut G ∧ SparseAt G 11 ∧ J⊔SimpleGraph.edge 3 4=G ∧
    ¬J.Adj 3 4 ∧ J.Adj 3 5 ∧ J.Adj 5 4 ∧ G.dist 3 11=G.dist 4 11 ∧ Indep G A ∧
    P=parity G 11 true ∧ U=eligible A P 11 ∧ weightedLeaves J U=2 ∧
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card ∧ bipartiteNum J=bipartiteNum G+1 ∧
    C3⊆U ∧ C4⊆U ∧ C3.card=weightedLeaves J U+1 ∧ C4.card=weightedLeaves J U+1 ∧
    NeedsTip J C3 (univ\C3) 3 4 ∧ NeedsTip J C4 (univ\C4) 4 3 ∧
    (∀ K : Finset V,K.card=weightedLeaves J U+1 →
      (NeedsTip J K (univ\K) 3 4 → K=C3 ∧ ∀ z∈(U\K).erase 4,¬Con G (univ\insert z (K.erase 3))) ∧
      (NeedsTip J K (univ\K) 4 3 → K=C4 ∧ ∀ z∈(U\K).erase 3,¬Con G (univ\insert z (K.erase 4)))) ∧
    F⊆U\{3,4} ∧ F.card=weightedLeaves J U+1 ∧ Con G (univ\F) ∧ (∀ q∈F,Dominates G (univ\F) q) ∧
    (F\C3).card=2 ∧ (C3\F).card=2 ∧ (F\C4).card=2 ∧ (C4\F).card=2 ∧
    FirstForm J U 3 4 5 ∧ weightedLeaves G U=3 ∧ weightedLeaves G (U\{3,4})=3 ∧ ¬violates G := by
  obtain ⟨allow,num,conn,dom⟩ := winning
  have won := (score_iff_core G (dist_data 11).1 (by decide) (U\{3,4}) 3).mpr
    ⟨F,allow,num.ge,conn,dom⟩
  have first := (first_iff_erased_gain J jc (by decide) 3 4 5 (by decide) (by decide) (by decide) (by decide) U).mpr
    (by rw [add_eq,old_score]; exact won)
  have size3 : C3.card=weightedLeaves J U+1 := by rw [old_score]; decide
  have top := (second_scores J jc (by decide) 3 4 5 (by decide) (by decide) (by decide) (by decide) U C3 (by decide) size3 tip3).1
  rw [add_eq,old_score] at top
  have erase := eligible_mono G (sdiff_subset : U\{3,4}⊆U)
  refine ⟨by decide,(dist_data 11).1,block,sparse,add_eq,by decide,by decide,by decide,?_,?_,?_,?_,old_score,?_,?_,
    by decide,by decide,size3,?_,tip3,tip4,?_,allow,?_,conn,dom,
    by decide,by decide,by decide,by decide,first,top,by omega,ordinary⟩
  · rw [(dist_data 11).2,(dist_data 11).2]; decide
  · unfold Indep; decide
  · ext i; rw [mem_parity,(dist_data 11).2]; exact (show ∀ j : V,j∈P ↔ d j 11%2=true.toNat by decide) i
  · unfold eligible; decide
  · rw [old_score,ranks.1]; decide
  · rw [ranks.1,ranks.2]
  · rw [old_score]; decide
  · intro K size
    rw [old_score] at size
    constructor
    · intro tip
      have eq := forced3 K size tip
      subst K; exact ⟨rfl,stuck3⟩
    · intro tip
      have eq := forced4 K size tip
      subst K; exact ⟨rfl,stuck4⟩
  · rw [old_score]; exact num

#print axioms all_second_stuck
end Minimal180.Case14
