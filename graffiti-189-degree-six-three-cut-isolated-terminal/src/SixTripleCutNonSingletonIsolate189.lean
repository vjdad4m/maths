import SixTripleCutUniversalBudget189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark from SixTripleCutSingleton189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.low_of_small_nonport from SixTripleCutIsolate189

private theorem ports_subset_visible {S W : Finset V} {t : V} (ts : t∈S) :
    ports G W t⊆visible G S W := by
  intro z zm
  obtain ⟨zw,tz⟩ := mem_filter.mp zm
  exact mem_filter.mpr ⟨zw,t,ts,tz.symm⟩

/-- Eliminates the nonsingleton three-shore configuration with an
isolated terminal, after the universal port and low-only shore have
been found. No assumptions on the other two terminals' edge are needed. -/
theorem no_nonsingleton_three_shores_of_isolated_terminal
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (cutconn : ThreeConnected G)
    {S A B C : Finset V} (ss : S.card=3)
    (shA : Shore G S A) (shB : Shore G S B) (shC : Shore G S C)
    (cA : (G.induce (↑A : Set V)).Connected) (cB : (G.induce (↑B : Set V)).Connected)
    (cC : (G.induce (↑C : Set V)).Connected)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (a4 : 4≤A.card) (b4 : 4≤B.card) (c4 : 4≤C.card)
    (bh : ∀ w∈B,6≤G.degree w) (ch : ∀ w∈C,6≤G.degree w)
    {t s x : V} (ts : t∈S) (iso : ∀ u∈S,u≠t → ¬G.Adj t u)
    (sa : s∈A) (low : G.degree s<6) (mins : 3≤G.degree s)
    (ats : G.Adj t s) (only : ∀ u∈A,G.Adj t u → u=s)
    (xc : x∈C) (ux : ∀ v∈S,G.Adj x v) : False := by
  classical
  let PA := ports G A t
  let PB := ports G B t
  let PC := ports G C t
  let QA := localTwo G A t
  let QB := localTwo G B t
  let QC := localTwo G C t
  have va := shA.visible_lower ss cutconn (by omega)
  have vb := shB.visible_lower ss cutconn (by omega)
  have vc := shC.visible_lower ss cutconn (by omega)
  obtain ⟨va3,vb3,insideC⟩ :=
    universal_port_saturates_other_shores hc cap shC cC shA shB ac.symm bc.symm ab va vb xc ux
  have sum := three_local_twos_le_four_at_isolate hc cap ss shA shB shC ab ac bc ts ux iso
  change QA.card+QB.card+QC.card≤4 at sum
  have cEq := shore_card_of_universal_inside hc shC xc ux insideC ts
  change C.card=PC.card+QC.card at cEq
  have sr : rank G S s≤2 := by
    by_cases has : ∃ z∈S,¬G.Adj s z
    · obtain ⟨z,zs,na⟩ := has
      exact rank_le_two_of_missing ss zs na
    exfalso
    have un (z : V) (zs : z∈S) : G.Adj s z := by
      by_cases e : G.Adj s z
      · exact e
      exfalso
      exact has ⟨z,zs,e⟩
    obtain ⟨_,_,inside⟩ := universal_port_saturates_other_shores hc cap shA cA shB shC ab ac bc vb vc sa un
    have d := full_degree_of_universal_inside shA sa un inside
    omega
  have qa : 1≤QA.card := by
    have neigh : ∃ w∈A,G.Adj s w := by
      by_cases yes : ∃ w∈A,G.Adj s w
      · exact yes
      exfalso
      have inc : G.neighborFinset s⊆S.filter (G.Adj s) := by
        intro u um
        have su := (G.mem_neighborFinset ..).mp um
        rcases shA.closed s sa u su with ua|us
        · exact (yes ⟨u,ua,su⟩).elim
        · exact mem_filter.mpr ⟨us,su⟩
      have l := card_le_card inc
      rw [card_neighborFinset_eq_degree] at l
      change G.degree s≤rank G S s at l
      omega
    obtain ⟨w,wa,sw⟩ := neigh
    have ne : t≠w := fun e=>disjoint_left.mp shA.disjoint wa (e ▸ ts)
    have na : ¬G.Adj t w := fun e=>sw.ne (only w wa e).symm
    exact card_pos.mpr ⟨w,mem_inter.mpr ⟨wa,two_of_common hc ne na ats sw⟩⟩
  have rankB (y : V) (yb : y∈B) : rank G S y≤2 := by
    by_cases has : ∃ z∈S,¬G.Adj y z
    · obtain ⟨z,zs,na⟩ := has
      exact rank_le_two_of_missing ss zs na
    exfalso
    have un (z : V) (zs : z∈S) : G.Adj y z := by
      by_cases e : G.Adj y z
      · exact e
      exfalso
      exact has ⟨z,zs,e⟩
    obtain ⟨_,vc3,insideB⟩ := universal_port_saturates_other_shores hc cap shB cB shA shC
      ab.symm bc ac va vc yb un
    have b7 := seven_of_three_visible_and_all_high shB b4 vb3 bh
    have c7 := seven_of_three_visible_and_all_high shC c4 vc3 ch
    have eq := shore_card_of_universal_inside hc shB yb un insideB ts
    have cb := card_le_card (ports_subset_visible (G:=G) (W:=B) ts)
    have cc := card_le_card (ports_subset_visible (G:=G) (W:=C) ts)
    change B.card=PB.card+QB.card at eq
    change PB.card≤(visible G S B).card at cb
    change PC.card≤(visible G S C).card at cc
    omega
  obtain ⟨u,um,tu⟩ := shB.hit ss cutconn ts
  have up : u∈PB := mem_filter.mpr ⟨um,tu⟩
  have ucost := shB.port_cost_rank hc ts up
  change G.degree u+1≤PB.card+QB.card+rank G S u at ucost
  have uh := bh u um
  have ur := rankB u um
  have pb_le : PB.card≤3 := by
    have l := card_le_card (ports_subset_visible (G:=G) (W:=B) ts)
    change PB.card≤(visible G S B).card at l
    omega
  have qb2 : 2≤QB.card := by omega
  have pc4 : 4≤PC.card := by
    by_contra! small
    have csz : C.card=4 := by omega
    have pe : PC=C := by
      apply eq_of_subset_of_card_le (filter_subset _ _)
      apply card_le_card
      intro z zm
      by_cases zp : z∈PC
      · exact zp
      exfalso
      have h := Graffiti189LongestPath.ThresholdSix.ThreeCut.low_of_small_nonport shC ss csz ts zm zp
      have k := ch z zm
      omega
    rw [pe] at small
    omega
  have sp : s∈PA := mem_filter.mpr ⟨sa,ats⟩
  have spb : PB⊆DistanceTwo G s := fun _ h => shA.foreign_distance_two shB ab hc sp h
  have spc : PC⊆DistanceTwo G s := fun _ h => shA.foreign_distance_two shC ac hc sp h
  have psep : Disjoint PB PC := bc.mono (filter_subset _ _) (filter_subset _ _)
  have pcaps := (card_le_card (union_subset spb spc)).trans (distanceTwo_le_of_even 6 s (cap s))
  rw [card_union_of_disjoint psep] at pcaps
  have pb2 : PB.card=2 := by omega
  have pc4' : PC.card=4 := by omega
  have qb3 : QB.card=3 := by omega
  have qc0 : QC.card=0 := by omega
  have pcwhole : PC=C := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  let F := insert s C
  have sf : s∉C := fun h=>disjoint_left.mp ac sa h
  have f5 : F.card=5 := by
    change (insert s C).card=5
    rw [card_insert_of_not_mem sf]
    omega
  have foreign : F⊆DistanceTwo G u := by
    apply insert_subset (shB.foreign_distance_two shA ab.symm hc up sp)
    intro z zm
    have zp : z∈PC := by rw [pcwhole]; exact zm
    exact shB.foreign_distance_two shC bc hc up zp
  let T := (PB.erase u∪QB)∪(S.filter (G.Adj u))
  have nsub : G.neighborFinset u⊆T := by
    intro z zm
    have pair := shB.port_neighbor_cover hc ts up zm
    rcases mem_union.mp pair with z1|z2
    · exact mem_union_left _ z1
    · exact mem_union_right _ (mem_filter.mpr ⟨z2,(G.mem_neighborFinset ..).mp zm⟩)
  have T6 : T.card≤6 := by
    have k := card_union_le (PB.erase u∪QB) (S.filter (G.Adj u))
    have l := card_union_le (PB.erase u) QB
    change T.card≤(PB.erase u∪QB).card+rank G S u at k
    rw [card_erase_of_mem up,pb2,qb3] at l
    omega
  have adjAll : G.neighborFinset u=T := eq_of_subset_of_card_le nsub
    (by rw [card_neighborFinset_eq_degree]; exact T6.trans uh)
  obtain ⟨y,yq,yd⟩ : ∃ y∈QB,y∉visible G S B := by
    by_cases yes : ∃ y∈QB,y∉visible G S B
    · exact yes
    exfalso
    have inc : QB⊆visible G S B := by
      intro y ym
      by_cases vis : y∈visible G S B
      · exact vis
      · exact (yes ⟨y,ym,vis⟩).elim
    have pp : PB⊆visible G S B := ports_subset_visible ts
    have sub := card_le_card (union_subset pp inc)
    rw [card_union_of_disjoint (disjoint_ports_localTwo G B t),vb3] at sub
    change PB.card+QB.card≤3 at sub
    omega
  have yb := (mem_inter.mp yq).1
  have darkY : y∈dark G S B := mem_sdiff.mpr ⟨yb,yd⟩
  have uy : G.Adj u y := (G.mem_neighborFinset ..).mp
    (adjAll.symm ▸ mem_union_left _ (mem_union_right _ yq))
  let H := PB∪QB
  let D := G.neighborFinset y \ H
  have hy : y∈H := mem_union_right _ yq
  have h5 : H.card≤5 := by
    have c := card_union_le PB QB
    rw [pb2,qb3] at c
    exact c
  have inc : G.neighborFinset y⊆H.erase y∪D := by
    intro z zm
    by_cases h : z∈H
    · exact mem_union_left _ (mem_erase.mpr ⟨((G.mem_neighborFinset ..).mp zm).ne.symm,h⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨zm,h⟩)
  have cnt := (card_le_card inc).trans (card_union_le _ _)
  rw [card_neighborFinset_eq_degree,card_erase_of_mem hy] at cnt
  have d2 : 2≤D.card := by have h := bh y yb; omega
  have sub : D⊆B∩DistanceTwo G u := by
    intro z zm
    obtain ⟨zN,zH⟩ := mem_sdiff.mp zm
    have yz := (G.mem_neighborFinset ..).mp zN
    have zb := (shB.closed y yb z yz).resolve_right
      (fun s=>Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark darkY s yz)
    have ne : u≠z := fun e=>zH (mem_union_left _ (e ▸ up))
    have no : ¬G.Adj u z := fun e=>by
      have ins := nsub ((G.mem_neighborFinset ..).mpr e)
      rcases mem_union.mp ins with k|k
      · exact zH ((mem_union.mp k).elim (fun z=>mem_union_left _ (mem_erase.mp z).2) (mem_union_right _))
      · exact disjoint_left.mp shB.disjoint zb (mem_filter.mp k).1
    exact mem_inter.mpr ⟨zb,two_of_common hc ne no uy yz⟩
  have dj : Disjoint F D := by
    apply disjoint_left.mpr
    intro z zf zd
    have zb := (mem_inter.mp (sub zd)).1
    rcases mem_insert.mp zf with zs|zc
    · exact disjoint_left.mp ab sa (zs ▸ zb)
    · exact disjoint_left.mp bc zb zc
  have final := (card_le_card (union_subset foreign (sub.trans inter_subset_right))).trans
    (distanceTwo_le_of_even 6 u (cap u))
  rw [card_union_of_disjoint dj,f5] at final
  omega

#print axioms no_nonsingleton_three_shores_of_isolated_terminal
end Graffiti189LongestPath.ThresholdSix.ThreeCut
