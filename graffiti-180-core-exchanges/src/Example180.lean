import ExampleScore180
import ExampleRank180
import SecondScores180

set_option warningAsError true
set_option compiler.extract_closed false
namespace Minimal180.Case12
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180

/-- The lower equality, rank change, full rooted sparsity and exact weighted
scores coexist with a specified second certificate requiring two replacements. -/
theorem exact_transition :
    Fintype.card V=12 ∧ G.Connected ∧ NoCut G ∧ SparseAt G 0 ∧ J⊔SimpleGraph.edge 7 8=G ∧
    ¬J.Adj 7 8 ∧ J.Adj 7 1 ∧ J.Adj 1 8 ∧ G.dist 7 0=G.dist 8 0 ∧ Indep G A ∧
    P=parity G 0 false ∧ U=eligible A P 0 ∧ weightedLeaves J U=4 ∧
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card ∧ bipartiteNum J=bipartiteNum G+1 ∧
    C⊆U ∧ C.card=weightedLeaves J U+1 ∧ NeedsTip J C (univ\C) 7 8 ∧
    (∀ z∈(U\C).erase 8,¬Con G (univ\single z)) ∧
    (L\C).card=2 ∧ (C\L).card=2 ∧ FirstForm J U 7 8 1 ∧
    weightedLeaves G U=5 ∧ weightedLeaves G (U\{7,8})=5 ∧ ¬violates G := by
  obtain ⟨tip,stuck,allowed,_,sizeZ,sizeB,connected,dom,_⟩ := specified_exchange
  have won := (score_iff_core G (dist_data 0).1 (by decide) (U\{7,8}) 5).mpr
    ⟨L,allowed,by decide,connected,dom⟩
  have first := (first_iff_erased_gain J jc (by decide) 7 8 1 (by decide) (by decide) (by decide) (by decide) U).mpr
    (by rw [add_eq,old_score]; exact won)
  have cardC : C.card=weightedLeaves J U+1 := by rw [old_score]; decide
  have top := (second_scores J jc (by decide) 7 8 1 (by decide) (by decide) (by decide) (by decide) U C (by decide) cardC tip).1
  rw [add_eq,old_score] at top
  have erase := eligible_mono G (sdiff_subset : U\{7,8}⊆U)
  refine ⟨by decide,(dist_data 0).1,block,sparse,add_eq,by decide,by decide,by decide,?_,?_,?_,?_,old_score,?_,?_,
    by decide,cardC,tip,stuck,sizeZ,sizeB,first,top,by omega,ordinary⟩
  · rw [(dist_data 0).2,(dist_data 0).2]; decide
  · unfold Indep; decide
  · ext i; rw [mem_parity,(dist_data 0).2]; exact (show ∀ j : V,j∈P ↔ d j 0%2=false.toNat by decide) i
  · unfold eligible; decide
  · rw [old_score,ranks.1]; decide
  · rw [ranks.1,ranks.2]

/-- At the same oriented chord, changing the old certificate by one entry
allows a single exchange into a first-form witness. -/
theorem neighboring_certificate :
    let C' : Finset V := {0,1,2,4,7}
    let F := insert 10 (C'.erase 7)
    C'⊆U ∧ C'.card=weightedLeaves J U+1 ∧
    (C\C').card=1 ∧ (C'\C).card=1 ∧ NeedsTip J C' (univ\C') 7 8 ∧
    F⊆U\{7,8} ∧ F.card=weightedLeaves J U+1 ∧ Con G (univ\F) ∧
    ∀ q∈F,Dominates G (univ\F) q := by
  let C' : Finset V := {0,1,2,4,7}
  let F := insert 10 (C'.erase 7)
  have tip : NeedsTip J C' (univ\C') 7 8 := by
    refine ⟨by decide,by decide,con 3 (fun i => [88,88,88,0,88,2,2,88,1,3,2,1][i.val]!) (by decide) (by decide),?_,?_⟩
    all_goals unfold Dominates; decide
  have conn : Con G (univ\F) :=
    con 3 (fun i => [88,88,88,0,88,2,2,2,1,3,88,1][i.val]!) (by decide) (by decide)
  dsimp only
  rw [old_score]
  refine ⟨by decide,by decide,by decide,by decide,tip,by decide,by decide,conn,?_⟩
  unfold Dominates
  decide

#print axioms neighboring_certificate
#print axioms exact_transition
end Minimal180.Case12
