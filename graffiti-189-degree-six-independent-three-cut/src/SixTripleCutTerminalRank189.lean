import SixTripleCutIsolate189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
open scoped BigOperators
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_cards_le from SixTripleCutFourShore189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.all_adj_of_no_internal_two from SixTripleCutIsolate189
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

def rank (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (S.filter (G.Adj v)).card

def Good (G : SimpleGraph V) [DecidableRel G.Adj] (A : Fin 3→Finset V) (a : V) : Prop :=
  ∀ i,∃ x∈ports G (A i) a,6≤G.degree x

theorem Shore.port_cost_rank {S A : Finset V} (sh : Shore G S A) (hc : G.Connected)
    {a x : V} (as' : a∈S) (xp : x∈ports G A a) :
    G.degree x+1≤(ports G A a).card+(localTwo G A a).card+rank G S x := by
  classical
  let P := ports G A a
  let Q := localTwo G A a
  let M := P∪Q
  let R := S.filter (G.Adj x)
  have px : x∈M := mem_union_left _ xp
  have sub : G.neighborFinset x⊆M.erase x∪R := by
    intro y ym
    have xy := (G.mem_neighborFinset ..).mp ym
    rcases sh.closed x (mem_filter.mp xp).1 y xy with ya|ys
    · have ay : y≠a := fun h => disjoint_left.mp sh.disjoint ya (h ▸ as')
      apply mem_union_left _
      refine mem_erase.mpr ⟨xy.ne.symm,?_⟩
      by_cases ay' : G.Adj a y
      · exact mem_union_left _ (mem_filter.mpr ⟨ya,ay'⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨ya,two_of_common hc (Ne.symm ay) ay' (mem_filter.mp xp).2 xy⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨ys,xy⟩)
  have c := (card_le_card sub).trans (card_union_le _ _)
  rw [card_neighborFinset_eq_degree,card_erase_of_mem px] at c
  have hm := card_union_le P Q
  change M.card≤P.card+Q.card at hm
  have pos := card_pos.mpr ⟨x,px⟩
  change G.degree x+1≤P.card+Q.card+R.card
  omega

theorem rank_le_two_of_missing {S : Finset V} (ss : S.card=3)
    {x t : V} (ts : t∈S) (miss : ¬G.Adj x t) : rank G S x≤2 := by
  classical
  have sub : S.filter (G.Adj x)⊆S.erase t := by
    intro z zm
    obtain ⟨zS,xz⟩ := mem_filter.mp zm
    exact mem_erase.mpr ⟨fun e=>miss (e ▸ xz),zS⟩
  have c := card_le_card sub
  rwa [card_erase_of_mem ts,ss] at c

theorem foreign_shore_port_sum
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    {S : Finset V} (A : Fin 3→Finset V)
    (sh : ∀ i,Shore G S (A i)) (dis : Pairwise fun i j=>Disjoint (A i) (A j))
    {a : V} {i : Fin 3} {x : V} (xp : x∈ports G (A i) a) :
    (∑ j∈univ.erase i,(ports G (A j) a).card)≤6 := by
  exact (Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_cards_le (univ.erase i)
    (fun j=>ports G (A j) a)
    (fun _ _ h=>(dis h).mono (filter_subset _ _) (filter_subset _ _))
    (fun j jm _ yj=>(sh i).foreign_distance_two (sh j) (dis (mem_erase.mp jm).1.symm) hc xp yj))
    |>.trans (distanceTwo_le_of_even 6 x (cap x))

/-- A foreign distance-two sum of exactly six fills every slot.
A chosen terminal port then sees its whole connected shore. -/
theorem saturated_shore_card
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    {S : Finset V} (A : Fin 3→Finset V)
    (sh : ∀ i,Shore G S (A i)) (conn : ∀ i,(G.induce (↑(A i) : Set V)).Connected)
    (dis : Pairwise fun i j=>Disjoint (A i) (A j))
    {a : V} (as' : a∈S) {i : Fin 3} {x : V} (xp : x∈ports G (A i) a)
    (full : (∑ j∈univ.erase i,(ports G (A j) a).card)=6) :
    (A i).card=(ports G (A i) a).card+(localTwo G (A i) a).card := by
  classical
  let U := (univ.erase i).biUnion (fun j=>ports G (A j) a)
  have sz : U.card=6 := (card_biUnion (fun _ _ _ _ ne =>
    (dis ne).mono (filter_subset _ _) (filter_subset _ _))).trans full
  have sub : U⊆DistanceTwo G x := by
    intro y ym
    obtain ⟨j,jm,yp⟩ := mem_biUnion.mp ym
    exact (sh i).foreign_distance_two (sh j) (dis (mem_erase.mp jm).1.symm) hc xp yp
  have eq : U=DistanceTwo G x := eq_of_subset_of_card_le sub (by rw [sz]; exact distanceTwo_le_of_even 6 x (cap x))
  have no (y : V) (ym : y∈A i) : y∉DistanceTwo G x := by
    rw [←eq]
    intro h
    obtain ⟨j,jm,yp⟩ := mem_biUnion.mp h
    exact disjoint_left.mp (dis (mem_erase.mp jm).1.symm) ym (mem_filter.mp yp).1
  have adj := Graffiti189LongestPath.ThresholdSix.ThreeCut.all_adj_of_no_internal_two hc
    (conn i) (mem_filter.mp xp).1 no
  have cover : ports G (A i) a ∪ localTwo G (A i) a=A i := by
    ext z
    constructor
    · intro z'
      exact (mem_union.mp z').elim (fun t=>(mem_filter.mp t).1) (fun t=>(mem_inter.mp t).1)
    · intro zi
      by_cases az : G.Adj a z
      · exact mem_union_left _ (mem_filter.mpr ⟨zi,az⟩)
      have zx : z≠x := fun e=>az (e ▸ (mem_filter.mp xp).2)
      have na : a≠z := fun e=>disjoint_left.mp (sh i).disjoint zi (e ▸ as')
      exact mem_union_right _ (mem_inter.mpr ⟨zi,two_of_common hc na az (mem_filter.mp xp).2 ((adj z zi).resolve_left zx)⟩)
  have pd : Disjoint (ports G (A i) a) (localTwo G (A i) a) := by
    apply disjoint_left.mpr
    intro z zp zq
    have m : G.dist a z=1 := dist_eq_one_iff_adj.mpr (mem_filter.mp zp).2
    have n : G.dist a z=2 := by simpa [DistanceTwo] using (mem_inter.mp zq).2
    omega
  exact (congrArg Finset.card cover).symm.trans (card_union_of_disjoint pd)

/-- With three shores and at most two terminals at each shore vertex,
a terminal having a high port in every shore forces exact 3+2 slots
on every shore. Consequently every shore has five vertices. -/
theorem good_terminal_exact_five
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    {S : Finset V} (A : Fin 3→Finset V)
    (sh : ∀ i,Shore G S (A i)) (conn : ∀ i,(G.induce (↑(A i) : Set V)).Connected)
    (dis : Pairwise fun i j=>Disjoint (A i) (A j))
    (two : ∀ (i : Fin 3) (x : V),x∈A i → rank G S x≤2)
    {a : V} (as' : a∈S) (good : Good G A a) :
    ∀ i,(ports G (A i) a).card=3 ∧ (localTwo G (A i) a).card=2 ∧ (A i).card=5 := by
  classical
  let p (i : Fin 3) := (ports G (A i) a).card
  let q (i : Fin 3) := (localTwo G (A i) a).card
  let P := ∑ i,p i
  let Q := ∑ i,q i
  have qcap : Q≤6 := 
    (Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_cards_le univ (fun j=>localTwo G (A j) a)
      (fun _ _ h=>(dis h).mono inter_subset_left inter_subset_left)
      (fun _ _=>inter_subset_right)).trans (distanceTwo_le_of_even 6 a (cap a))
  have cost (i : Fin 3) : 5≤p i+q i := by
    obtain ⟨x,xp,high⟩ := good i
    have a := (sh i).port_cost_rank hc as' xp
    have b := two i x (mem_filter.mp xp).1
    change G.degree x+1≤p i+q i+rank G S x at a
    omega
  have foreign (i : Fin 3) : (∑ j∈univ.erase i,p j)≤6 := by
    obtain ⟨x,xp,_⟩ := good i
    exact foreign_shore_port_sum hc cap A sh dis xp
  have formula (i : Fin 3) : (∑ j∈univ.erase i,p j)+p i=P :=
    sum_erase_add univ p (mem_univ i)
  have bound (i : Fin 3) : P≤6+p i := by have x:=foreign i; have y:=formula i; omega
  have pe : P=p 0+p 1+p 2 := sum_fin_three p
  have qe : Q=q 0+q 1+q 2 := sum_fin_three q
  have a := bound 0; have b:=bound 1; have c:=bound 2
  have w := cost 0; have x := cost 1; have y := cost 2
  have p9 : P=9 := by omega
  have q6 : Q=6 := by omega
  intro i
  have pi : p i=3 := by
    rcases (show i=0∨i=1∨i=2 from (by decide : ∀ j : Fin 3,j=0∨j=1∨j=2) i) with rfl|rfl|rfl <;> omega
  have qi : q i=2 := by
    rcases (show i=0∨i=1∨i=2 from (by decide : ∀ j : Fin 3,j=0∨j=1∨j=2) i) with rfl|rfl|rfl <;> omega
  have u := formula i
  have full : (∑ j∈univ.erase i,p j)=6 := by omega
  obtain ⟨x,xp,_⟩ := good i
  have cs := saturated_shore_card hc cap A sh conn dis as' xp full
  change (A i).card=p i+q i at cs
  exact ⟨pi,qi,by omega⟩

#print axioms Shore.port_cost_rank
#print axioms saturated_shore_card
#print axioms good_terminal_exact_five
end Graffiti189LongestPath.ThresholdSix.ThreeCut
