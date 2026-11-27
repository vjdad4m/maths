import OriginalClique28

namespace Graffiti384b.Port28.Board
open Finset SimpleGraph
open private ThreeChoice.pair_turan from ThreeGeometry33
open private Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (M : Board G)

theorem covered_score {w : V} (wm : w∈M.W)
    (cover : ∀ C,G.IsNClique 5 C → 3≤(C∩M.B).card) :
    let b := nbr G w M.W
    let h := nbr G w {M.c}+nbr G w M.U+nbr G w M.L
    trianglesAt G w≤(b+h).choose 2 ∧
      (h≤2 → b+h≤10 → trianglesAt G w≤RankTable.cap (b+h) 3) := by
  classical
  let N := G.neighborFinset w
  have wu : ¬G.Adj w M.u := fun e => ((M.outside w).mp wm).2.2 (mem_union_left _ ((G.mem_neighborFinset ..).mpr e.symm))
  have ws : ¬G.Adj w M.s := fun e => ((M.outside w).mp wm).2.2 (mem_union_right _ ((G.mem_neighborFinset ..).mpr e.symm))
  have wb : Disjoint M.W M.B := disjoint_left.mpr (fun z zm => ((M.outside z).mp zm).2.2)
  have eq : (M.W∪M.B).filter (G.Adj w)=N := by
    ext z; simp only [N,mem_filter,mem_neighborFinset]
    constructor
    · exact And.right
    · intro wz
      by_cases zb : z∈M.B
      · exact ⟨mem_union_right _ zb,wz⟩
      · exact ⟨mem_union_left _ ((M.outside z).mpr ⟨fun h => wu (h ▸ wz),fun h => ws (h ▸ wz),zb⟩),wz⟩
  have sum : nbr G w (M.W∪M.B)=G.degree w := (congrArg card eq).trans (card_neighborFinset_eq_degree ..)
  have cu : Disjoint {M.c} M.U := by simp [U]
  have cl : Disjoint {M.c} M.L := by simp [L]
  have bs : nbr G w M.B=nbr G w {M.c}+nbr G w M.U+nbr G w M.L := by
    rw [←M.parts,Repair.nbr_add G w (disjoint_union_left.mpr ⟨cl,M.dis⟩),Repair.nbr_add G w cu]
  rw [Repair.nbr_add G w wb,bs] at sum
  refine ⟨(sum.symm ▸ Repair.triangles_le_choose G w),?_⟩
  intro small dsmall
  have free (Q : Finset V) (sub : Q⊆N) (clique : G.IsNClique (3+1) Q) : False := by
    have five := clique.insert (fun z zm => (G.mem_neighborFinset ..).mp (sub zm))
    have many := cover _ five
    have inc : (insert w Q)∩M.B⊆M.B.filter (G.Adj w) := by
      intro z zm; obtain ⟨zq,zb⟩ := mem_inter.mp zm
      have ne : z≠w := fun h => ((M.outside w).mp wm).2.2 (h ▸ zb)
      exact mem_filter.mpr ⟨zb,(G.mem_neighborFinset ..).mp (sub ((mem_insert.mp zq).resolve_left ne))⟩
    have up : 3≤nbr G w M.B := many.trans (card_le_card inc)
    omega
  have hi := ThreeChoice.pair_turan G N (by decide : 0<3) free
  have ns : N.card=G.degree w := card_neighborFinset_eq_degree ..
  change trianglesAt G w≤_ at hi
  rw [ns,←sum] at hi
  exact hi.trans_eq (RankTable.cap_table ⟨_,by omega⟩ ⟨3,by decide⟩ (by decide))


end Graffiti384b.Port28.Board
#print axioms Graffiti384b.Port28.Board.covered_score
