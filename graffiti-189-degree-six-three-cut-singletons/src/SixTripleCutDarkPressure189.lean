import SixTripleCutHighActual189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark from SixTripleCutSingleton189

def innerDegree (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (x : V) :=
  (G.neighborFinset x ∩ A).card

theorem Shore.degree_eq_inner_add_rank {S A : Finset V} (sh : Shore G S A)
    {x : V} (xa : x∈A) : G.degree x=innerDegree G A x+rank G S x := by
  classical
  let P := G.neighborFinset x ∩ A
  let Q := S.filter (G.Adj x)
  have e : P∪Q=G.neighborFinset x := by
    ext y
    constructor
    · intro h
      exact (mem_union.mp h).elim (fun h=>(mem_inter.mp h).1) (fun h=>(G.mem_neighborFinset ..).mpr (mem_filter.mp h).2)
    · intro h
      have a := (G.mem_neighborFinset ..).mp h
      rcases sh.closed x xa y a with ya|ys
      · exact mem_union_left _ (mem_inter.mpr ⟨h,ya⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨ys,a⟩)
  have d : Disjoint P Q := sh.disjoint.mono inter_subset_right (filter_subset _ _)
  have c := card_union_of_disjoint d
  rw [e,card_neighborFinset_eq_degree] at c
  exact c

theorem Shore.dark_neighbor_of_high_visible {S A : Finset V}
    (sh : Shore G S A) (s3 : S.card=3) (v3 : (visible G S A).card=3)
    {x : V} (xm : x∈visible G S A) (high : 6≤G.degree x) :
    ∃ y∈dark G S A,G.Adj x y := by
  classical
  by_contra! no
  have sub : G.neighborFinset x⊆(visible G S A).erase x∪S := by
    intro y ym
    have xy := (G.mem_neighborFinset ..).mp ym
    rcases sh.closed x (mem_filter.mp xm).1 y xy with ya|ys
    · by_cases yv : y∈visible G S A
      · exact mem_union_left _ (mem_erase.mpr ⟨xy.ne.symm,yv⟩)
      · exact (no y (mem_sdiff.mpr ⟨ya,yv⟩) xy).elim
    · exact mem_union_right _ ys
  have e := (card_le_card sub).trans (card_union_le _ _)
  rw [card_neighborFinset_eq_degree,card_erase_of_mem xm,v3,s3] at e
  omega

/-- High degree of a dark neighbor forces local degree or local
distance-two mass at the given vertex. -/
theorem Shore.dark_neighbor_degree_bound (hc : G.Connected) {S A : Finset V}
    (sh : Shore G S A) {x y : V} (ya : y∈dark G S A) (xy : G.Adj x y) :
    G.degree y ≤ innerDegree G A x+(localTwo G A x).card := by
  classical
  let T := G.neighborFinset x∩A
  let U := localTwo G A x
  have yt : y∈T := mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr xy,(mem_sdiff.mp ya).1⟩
  have sub : G.neighborFinset y⊆insert x (T.erase y∪U) := by
    intro z zm
    have yz := (G.mem_neighborFinset ..).mp zm
    have za := (sh.closed y (mem_sdiff.mp ya).1 z yz).resolve_right
      (fun h=>Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark ya h yz)
    by_cases zx : z=x
    · exact mem_insert.mpr (Or.inl zx)
    apply mem_insert_of_mem
    by_cases xz : G.Adj x z
    · exact mem_union_left _ (mem_erase.mpr ⟨yz.ne.symm,
        mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr xz,za⟩⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨za,two_of_common hc (Ne.symm zx) xz xy yz⟩)
  have cnt := card_le_card sub
  rw [card_neighborFinset_eq_degree] at cnt
  have ic := card_insert_le x (T.erase y∪U)
  have us := card_union_le (T.erase y) U
  rw [card_erase_of_mem yt] at us
  have pos := card_pos.mpr ⟨y,yt⟩
  change G.degree y≤T.card+U.card
  omega

theorem rank_full_of_two_intersect {S : Finset V} (ss : S.card=3)
    {x y : V} (rx : 2≤rank G S x) (ry : 2≤rank G S y) :
    ∃ t∈S,G.Adj x t ∧ G.Adj y t := by
  classical
  let U := S.filter (G.Adj x)
  let W := S.filter (G.Adj y)
  have a := card_le_card (show U∪W⊆S from union_subset (filter_subset _ _) (filter_subset _ _))
  have b := card_union_add_card_inter U W
  change 2≤U.card at rx
  change 2≤W.card at ry
  obtain ⟨t,tm⟩ := card_pos.mp (show 0<(U∩W).card by omega)
  obtain ⟨tu,tw⟩ := mem_inter.mp tm
  exact ⟨t,(mem_filter.mp tu).1,(mem_filter.mp tu).2,(mem_filter.mp tw).2⟩

#print axioms Shore.degree_eq_inner_add_rank
#print axioms Shore.dark_neighbor_of_high_visible
#print axioms Shore.dark_neighbor_degree_bound
#print axioms rank_full_of_two_intersect
end Graffiti189LongestPath.ThresholdSix.ThreeCut
