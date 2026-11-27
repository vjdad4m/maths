import DetachedExample180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 1500000
namespace Minimal180.DetachedExample
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 PrivateCore

theorem not_sparse : ¬SparseAt G 11 := by
  intro sp
  have ab : ¬Arc G 11 0 4 := by
    intro h
    have e := h.2.1
    rw [root_data.2.2,root_data.2.2] at e
    exact (by decide : ¬(_ = _)) e
  have ba : ¬Arc G 11 4 0 := by
    intro h
    have e := h.2.2 9 (by decide) (by rw [root_data.2.2,root_data.2.2]; decide)
    exact (by decide : (9:V)≠4) e
  let H := G.deleteEdges {s((0:V),4)}
  have increase := sp 0 4 (by decide) ab ba
  obtain ⟨T,col,st⟩ := optB H
  have triangle := triangle_excluded H T col 3 0 13
    (by apply deleteEdges_adj.mpr; exact ⟨by decide,by decide⟩)
    (by apply deleteEdges_adj.mpr; exact ⟨by decide,by decide⟩)
    (by apply deleteEdges_adj.mpr; exact ⟨by decide,by decide⟩)
  obtain ⟨a,_,out⟩ := Finset.not_subset.mp triangle
  have sub : T ⊂ univ := Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,fun h => out (h ▸ mem_univ a)⟩
  have bound := card_lt_card sub
  rw [card_univ,Fintype.card_fin] at bound
  change bipartiteNum H=bipartiteNum G+1 at increase
  rw [ranks.2] at increase
  omega

theorem ordinary : ¬violates G := by
  have bound : 10≤maxLeaves G := by
    rw [← weighted_all]
    apply (score_iff_core G root_data.2.1 (by decide) univ 10).mpr
    let L : Finset V := univ\{0,1,2,9}
    refine ⟨L,subset_univ _,by decide,Case14.con 0 (fun v => ([0,2,2,88,88,88,88,88,88,1,88,88,88,88]:List ℕ)[v.val]!)
      (by decide) (by decide),?_⟩
    unfold Dominates; decide
  let label (i:V) : Fin 8 := ([0,1,2,3,0,1,4,4,2,5,6,5,7,3]:List (Fin 8))[i.val]!
  obtain ⟨I,ind,num⟩ := exists_max_indep G
  have cap : I.card≤(univ:Finset (Fin 8)).card := by
    apply card_le_card_of_injOn label (fun _ _ => mem_univ _)
    intro i hi j hj eq
    by_contra ne
    exact ind i hi j hj ne ((show ∀ a b,a≠b → label a=label b → G.Adj a b by dsimp only [label]; decide) i j ne eq)
  rw [card_univ,Fintype.card_fin] at cap
  have even : maxEven G≤14 := by
    apply Finset.sup_le
    intro r _
    rw [even_equiv]
    exact card_le_univ _
  unfold violates
  rw [ranks.2]
  omega

#print axioms not_sparse
#print axioms ordinary
end Minimal180.DetachedExample
