import SixTripleCutSingletonNoIsolate189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.all_adj_of_no_internal_two from SixTripleCutIsolate189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark from SixTripleCutSingleton189

theorem universal_port_saturates_other_shores
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    {S A B C : Finset V} (shA : Shore G S A) (ac : (G.induce (↑A : Set V)).Connected)
    (shB : Shore G S B) (shC : Shore G S C)
    (ab : Disjoint A B) (ac' : Disjoint A C) (bc : Disjoint B C)
    (b3 : 3≤(visible G S B).card) (c3 : 3≤(visible G S C).card)
    {x : V} (xa : x∈A) (un : ∀ t∈S,G.Adj x t) :
    (visible G S B).card=3 ∧ (visible G S C).card=3 ∧
      ∀ w∈A,w=x ∨ G.Adj x w := by
  classical
  let U := visible G S B∪visible G S C
  have inc : U⊆DistanceTwo G x := union_subset
    (shA.foreign_visible_of_universal shB ab hc xa un)
    (shA.foreign_visible_of_universal shC ac' hc xa un)
  have ud : Disjoint (visible G S B) (visible G S C) :=
    bc.mono (filter_subset _ _) (filter_subset _ _)
  have s := card_union_of_disjoint ud
  change U.card=_ at s
  have c := (card_le_card inc).trans (distanceTwo_le_of_even 6 x (cap x))
  have six : U.card=6 := by omega
  have eq : U=DistanceTwo G x := eq_of_subset_of_card_le inc (by rw [six]; exact distanceTwo_le_of_even 6 x (cap x))
  have no (y : V) (ym : y∈A) : y∉DistanceTwo G x := by
    rw [←eq]
    intro h
    rcases mem_union.mp h with hb|hc'
    · exact disjoint_left.mp ab ym (mem_filter.mp hb).1
    · exact disjoint_left.mp ac' ym (mem_filter.mp hc').1
  exact ⟨by omega,by omega,Graffiti189LongestPath.ThresholdSix.ThreeCut.all_adj_of_no_internal_two hc ac xa no⟩

theorem shore_card_of_universal_inside (hc : G.Connected)
    {S A : Finset V} (sh : Shore G S A)
    {x : V} (_xa : x∈A) (un : ∀ t∈S,G.Adj x t)
    (inner : ∀ w∈A,w=x∨G.Adj x w) {t : V} (ts : t∈S) :
    A.card=(ports G A t).card+(localTwo G A t).card := by
  classical
  have eq : ports G A t∪localTwo G A t=A := by
    ext z
    constructor
    · intro h
      exact (mem_union.mp h).elim (fun hz=>(mem_filter.mp hz).1) (fun hz=>(mem_inter.mp hz).1)
    · intro zm
      by_cases adj : G.Adj t z
      · exact mem_union_left _ (mem_filter.mpr ⟨zm,adj⟩)
      have zt : t≠z := fun e=>disjoint_left.mp sh.disjoint zm (e ▸ ts)
      have zx : z≠x := fun e=>adj (e ▸ (un t ts).symm)
      exact mem_union_right _ (mem_inter.mpr ⟨zm,two_of_common hc zt adj
        (un t ts).symm ((inner z zm).resolve_left zx)⟩)
  exact (congrArg Finset.card eq).symm.trans (card_union_of_disjoint (disjoint_ports_localTwo G A t))

theorem full_degree_of_universal_inside {S A : Finset V} (sh : Shore G S A)
    {x : V} (xa : x∈A) (u : ∀ t∈S,G.Adj x t) (inside : ∀ w∈A,w=x∨G.Adj x w) :
    G.degree x+1=A.card+S.card := by
  classical
  have eq : A.erase x∪S=G.neighborFinset x := by
    ext z
    constructor
    · intro h
      apply (G.mem_neighborFinset ..).mpr
      rcases mem_union.mp h with h|h
      · exact (inside z (mem_erase.mp h).2).resolve_left (mem_erase.mp h).1
      · exact u z h
    · intro h
      have xz := (G.mem_neighborFinset ..).mp h
      rcases sh.closed x xa z xz with hz|hz
      · exact mem_union_left _ (mem_erase.mpr ⟨xz.ne.symm,hz⟩)
      · exact mem_union_right _ hz
  have c := card_union_of_disjoint (sh.disjoint.mono_left (erase_subset x A))
  rw [eq,card_neighborFinset_eq_degree,card_erase_of_mem xa] at c
  have pos := card_pos.mpr ⟨x,xa⟩
  omega

theorem seven_of_three_visible_and_all_high {S A : Finset V} (sh : Shore G S A)
    (a4 : 4≤A.card) (v3 : (visible G S A).card=3)
    (high : ∀ z∈A,6≤G.degree z) : 7≤A.card := by
  classical
  have inc : visible G S A⊆A := filter_subset _ _
  obtain ⟨z,zd⟩ := card_pos.mp (show 0<(dark G S A).card by
    unfold dark
    rw [card_sdiff inc,v3]
    omega)
  have za := (mem_sdiff.mp zd).1
  have sub : G.neighborFinset z⊆A.erase z := by
    intro u um
    have zu := (G.mem_neighborFinset ..).mp um
    rcases sh.closed z za u zu with ua|us
    · exact mem_erase.mpr ⟨zu.ne.symm,ua⟩
    · exact (Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark zd us zu).elim
  have le := card_le_card sub
  rw [card_neighborFinset_eq_degree,card_erase_of_mem za] at le
  have h := high z za
  omega

theorem three_local_twos_le_four_at_isolate
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    {S A B C : Finset V} (ss : S.card=3)
    (shA : Shore G S A) (shB : Shore G S B) (shC : Shore G S C)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    {t x : V} (ts : t∈S) (un : ∀ a∈S,G.Adj x a)
    (iso : ∀ a∈S,a≠t → ¬G.Adj t a) :
    (localTwo G A t).card+(localTwo G B t).card+(localTwo G C t).card≤4 := by
  let P := localTwo G A t
  let Q := localTwo G B t
  let R := localTwo G C t
  let T := S.erase t
  have pq : Disjoint P Q := ab.mono inter_subset_left inter_subset_left
  have pr : Disjoint P R := ac.mono inter_subset_left inter_subset_left
  have qr : Disjoint Q R := bc.mono inter_subset_left inter_subset_left
  have tf : T⊆DistanceTwo G t := by
    intro y ym
    obtain ⟨yt,ys⟩ := mem_erase.mp ym
    exact two_of_common hc (Ne.symm yt) (iso y ys yt) (un t ts).symm (un y ys)
  have s (W : Finset V) (sh : Shore G S W) : Disjoint (localTwo G W t) T :=
    sh.disjoint.mono inter_subset_left (erase_subset ..)
  have incl : P∪Q∪R∪T⊆DistanceTwo G t := union_subset
    (union_subset (union_subset inter_subset_right inter_subset_right) inter_subset_right) tf
  have l := (card_le_card incl).trans (distanceTwo_le_of_even 6 t (cap t))
  have dt : Disjoint (P∪Q∪R) T := disjoint_union_left.mpr
    ⟨disjoint_union_left.mpr ⟨s A shA,s B shB⟩,s C shC⟩
  have dr : Disjoint (P∪Q) R := disjoint_union_left.mpr ⟨pr,qr⟩
  rw [card_union_of_disjoint dt,card_union_of_disjoint dr,card_union_of_disjoint pq] at l
  have t2 : T.card=2 := by dsimp [T]; rw [card_erase_of_mem ts,ss]
  change P.card+Q.card+R.card+T.card≤6 at l
  change P.card+Q.card+R.card≤4
  omega

#print axioms universal_port_saturates_other_shores
#print axioms shore_card_of_universal_inside
#print axioms three_local_twos_le_four_at_isolate
end Graffiti189LongestPath.ThresholdSix.ThreeCut
