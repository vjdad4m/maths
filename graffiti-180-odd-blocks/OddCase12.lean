import SeamFirst180
import Example180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Case12

/-- The published 12-vertex tight, rooted-sparse transition lies in the
nonbipartite, biconnected lower branch of the reduction. -/
theorem case12_lower_block :
    Fintype.card V=12 ∧ NoCut G ∧ SparseAt G 0 ∧ J⊔edge 7 8=G ∧
    J.Adj 7 1 ∧ J.Adj 1 8 ∧ G.dist 7 0=G.dist 8 0 ∧ Indep G A ∧
    P=parity G 0 false ∧ U=eligible A P 0 ∧
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card ∧ bipartiteNum J=bipartiteNum G+1 ∧
    NeedsTip J C (univ\C) 7 8 ∧ NoCut J ∧ ¬TwoColor J univ := by
  obtain ⟨hn,_,block,sp,add,old,xw,wy,hor,ind,hp,hu,_,tight,drop,_,_,tip,_⟩ := exact_transition
  have noc := second_nonpendant_block (add ▸ block) xw wy (show J.Adj 7 2 by decide) (by decide) tip
  have odd := (odd_block_alternative J jc (by decide) 7 8 1 0 (by decide) old xw wy (add ▸ block)
    (add ▸ sp) (add ▸ drop)).1
  exact ⟨hn,block,sp,add,xw,wy,hor,ind,hp,hu,tight,drop,tip,noc,odd⟩

#print axioms case12_lower_block
end Minimal180.OddBlock
