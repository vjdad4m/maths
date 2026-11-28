import FourEarMatching384b
import ThirteenSingleLow384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exact_thirteen_independent (sup : Supported G)
    (t : (types G).card=11) (nine : (high G).card=9) (qc : (nonleaves G).card=13)
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (min : ∀ x∈high G,2≤trianglesAt G x)
    (ind : ∀ x∈nonleaves G \ high G,∀ y∈nonleaves G \ high G,¬G.Adj x y) :
    gamma G≤bound G := by
  classical
  let O := nonleaves G \ high G
  let N : V → Finset V := fun e => G.neighborFinset e
  let P := O.biUnion N
  have low : Disjoint O (high G) :=
    Finset.disjoint_left.mpr (fun _ xo xh => (mem_sdiff.mp xo).2 xh)
  have sub : high G ⊆ nonleaves G := by
    intro x xh
    have dg := (mem_filter.mp xh).2
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have four : O.card=4 := by
    have c := card_sdiff_add_card_eq_card sub
    dsimp [O]
    omega
  have deg (e : V) (em : e∈O) : G.degree e=2 := by
    obtain ⟨en,eh⟩ := mem_sdiff.mp em
    have up : ¬3≤G.degree e := fun d => eh (mem_filter.mpr ⟨mem_univ _,d⟩)
    have dn := (mem_filter.mp en).2
    omega
  have anch (e : V) (em : e∈O) : N e ⊆ high G := by
    intro y ym
    have ey := (G.mem_neighborFinset ..).mp ym
    obtain ⟨z,ez,yz⟩ := sup ey
    have pair : ({e,z} : Finset V) ⊆ G.neighborFinset y := insert_subset
      ((G.mem_neighborFinset ..).mpr ey.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr yz))
    have d := card_le_card pair
    rw [card_pair ez.ne,card_neighborFinset_eq_degree] at d
    have yn : y∈nonleaves G := mem_filter.mpr ⟨mem_univ _,d⟩
    by_contra yh
    exact ind e em y (mem_sdiff.mpr ⟨yn,yh⟩) ey
  by_cases seven : P.card≤7
  · exact exact_of_four_low_footprint_seven G t nine four.ge low
      (fun e eo=>(deg e eo).ge) ind
      (fun x _ ⟨e,eo,ex⟩=>mem_biUnion.mpr ⟨e,eo,(G.mem_neighborFinset ..).mpr ex⟩)
      seven
  · have dis : (O : Set V).PairwiseDisjoint N := by
      intro e eo f fo ef
      apply Finset.disjoint_left.mpr
      intro x xe xf
      let Q := (O.erase e).biUnion N
      have xo : x∈Q := mem_biUnion.mpr ⟨f,mem_erase.mpr ⟨ef.symm,fo⟩,xf⟩
      have ee : P=N e∪Q := by
        change O.biUnion N=N e∪(O.erase e).biUnion N
        rw [←biUnion_insert,insert_erase eo]
      have ec : (N e).card=2 := by rw [show (N e).card=G.degree e from
        card_neighborFinset_eq_degree ..,deg e eo]
      have qr : Q.card≤6 := by
        have c := card_biUnion_le_card_mul (O.erase e) N 2
          (fun v vm=>show (N v).card≤2 by rw [show (N v).card=G.degree v from
             card_neighborFinset_eq_degree ..,deg v (mem_of_mem_erase vm)])
        rw [card_erase_of_mem eo,four] at c
        exact c
      have i : 0<(N e∩Q).card := card_pos.mpr ⟨x,mem_inter.mpr ⟨xe,xo⟩⟩
      have eq := card_union_add_card_inter (N e) Q
      rw [←ee,ec] at eq
      omega
    exact exact_of_four_matched_ears G t four low deg anch dis scores min

/-- The 13-nonleaf case of the supported lower profile is exact. -/
theorem exact_thirteen_lower (sup : Supported G) (t : (types G).card=11)
    (nine : (high G).card=9) (q : (nonleaves G).card=13) : gamma G≤bound G := by
  by_contra! bad
  obtain ⟨scores,min⟩ : Set.InjOn (trianglesAt G) (high G : Set V) ∧
      (∀ x∈high G,2≤trianglesAt G x) := by
    rcases split_profile G sup t bad with ⟨qq,_⟩|⟨_,sc,mn,_⟩
    · omega
    · exact ⟨sc,mn⟩
  by_cases has : ∃x∈nonleaves G \ high G,∃y∈nonleaves G \ high G,G.Adj x y
  · obtain ⟨x,xl,y,yl,xy⟩ := has
    exact (not_le_of_gt bad) (exact_thirteen_single_low_edge G t nine q scores min xy xl yl
      (fun a al b bl ab=>low_edge_unique G sup t nine bad xl yl al bl xy ab))
  · exact (not_le_of_gt bad) (exact_thirteen_independent G sup t nine q scores min
      (fun x xl y yl xy=>has ⟨x,xl,y,yl,xy⟩))

#print axioms exact_thirteen_lower
end Graffiti384b.DiversityEleven
