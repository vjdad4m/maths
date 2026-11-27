import DegreeFiveUniquePortClosureTest189
import DegreeFiveFourPort189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private side_universal_if_no_local_d2 from DegreeFiveFourPort189
open private left_boundary from AdjacentCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Split G a b)
set_option linter.unusedSectionVars false

def leftNonports : Finset V := S.L.filter (fun z=> ¬ G.Adj a z ∧ ¬ G.Adj b z)

private theorem both_shore_shells_le_four {c d : V} (off : d∉S.L ∧ d∉S.R)
    (two : G.dist c d=2) (even : ∀ x,(EvenFrom G x).card≤6) :
    (secondA G S.L c).card+(secondA G S.R c).card≤4 := by
  classical
  let L := secondA G S.L c
  let R := secondA G S.R c
  have d2 : d∈DistanceTwo G c := by simp [DistanceTwo,two]
  have dn : d∉L∪R := by
    intro h
    exact (mem_union.mp h).elim (fun h=>off.1 (mem_inter.mp h).1)
      (fun h=>off.2 (mem_inter.mp h).1)
  have sub : insert d (L∪R)⊆DistanceTwo G c := by
    intro z hz
    rcases mem_insert.mp hz with rfl|h
    · exact d2
    exact (mem_union.mp h).elim (fun h=>(mem_inter.mp h).2) (fun h=>(mem_inter.mp h).2)
  have dis : Disjoint L R := S.dis.mono inter_subset_left inter_subset_left
  have h := card_le_card sub
  rw [card_insert_of_not_mem dn,card_union_of_disjoint dis] at h
  have cap := distanceTwo_le_of_even 5 c (even c)
  change L.card+R.card≤4
  omega

theorem order_add_left_nonports_le_sixteen_of_five_foreign
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {x : V} (xL : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (one : (CommonPorts G a b).card=1) (five : S.foreignPorts.card=5) :
    Fintype.card V+(leftNonports S).card≤16 := by
  classical
  let LA := secondA G S.L a
  let LB := secondA G S.L b
  let RA := secondA G S.R a
  let RB := secondA G S.R b
  have ba : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have ac := both_shore_shells_le_four S ⟨S.leftOff.2,S.rightOff.2⟩ two even
  have bc := both_shore_shells_le_four S ⟨S.leftOff.1,S.rightOff.1⟩ ba even
  change LA.card+RA.card≤4 at ac
  change LB.card+RB.card≤4 at bc
  have xcover : S.foreignPorts⊆DistanceTwo G x := by
    intro y yp
    obtain ⟨yr,hit⟩ := mem_filter.mp yp
    have n : x≠y := fun e=>disjoint_left.mp S.dis xL (e.symm ▸ yr)
    have no := S.cross x xL y yr
    exact hit.elim (fun h=>d2 hc n no ax.symm h) (fun h=>d2 hc n no bx.symm h)
  have xc := distanceTwo_le_of_even 5 x (even x)
  have same : S.foreignPorts=DistanceTwo G x := eq_of_subset_of_card_le xcover (by omega)
  have universal : ∀ z∈S.L,z=x ∨ G.Adj x z := by
    apply side_universal_if_no_local_d2 S hc xL
    intro z zl zd
    exact disjoint_left.mp S.dis zl (mem_filter.mp (same.symm ▸ zd)).1
  have rad (z : V) : G.dist x z≤3 := by
    apply Classical.byContradiction
    intro bad
    have far : 4≤G.dist x z := by omega
    have lo := distanceTwo_add_two_le_even_of_far hc far
    have lower := card_le_card xcover
    have c := even x
    omega
  have only : CommonPorts G a b={x} := by
    symm
    apply eq_of_subset_of_card_le
    · intro z zm
      rw [mem_singleton] at zm
      subst z
      exact mem_inter.mpr ⟨(mem_neighborFinset G a x).mpr ax,(mem_neighborFinset G b x).mpr bx⟩
    simp [one]
  have leftCover : S.L⊆insert x (LA∪LB) := by
    intro z zl
    by_cases zx : z=x
    · exact mem_insert.mpr (.inl zx)
    have xz := (universal z zl).resolve_left zx
    have naz : a≠z := fun e=>S.leftOff.1 (e.symm ▸ zl)
    have nbz : b≠z := fun e=>S.leftOff.2 (e.symm ▸ zl)
    apply mem_insert_of_mem
    by_cases az : G.Adj a z
    · have nb : ¬G.Adj b z := by
        intro bz
        have t : z∈CommonPorts G a b :=
          mem_inter.mpr ⟨(mem_neighborFinset G a z).mpr az,(mem_neighborFinset G b z).mpr bz⟩
        exact zx (by simpa [only] using t)
      exact mem_union_right _ (mem_inter.mpr ⟨zl,d2 hc nbz nb bx xz⟩)
    exact mem_union_left _ (mem_inter.mpr ⟨zl,d2 hc naz az ax xz⟩)
  have inner : leftNonports S⊆LA∩LB := by
    intro z zn
    obtain ⟨zl,az,bz⟩ := mem_filter.mp zn
    have xz := (universal z zl).resolve_left (fun e=>az (e.symm ▸ ax))
    have na : a≠z := fun e=>S.leftOff.1 (e.symm ▸ zl)
    have nb : b≠z := fun e=>S.leftOff.2 (e.symm ▸ zl)
    exact mem_inter.mpr ⟨mem_inter.mpr ⟨zl,d2 hc na az ax xz⟩,
      mem_inter.mpr ⟨zl,d2 hc nb bz bx xz⟩⟩
  have leftC := (card_le_card leftCover).trans (card_insert_le x _)
  have innerC := card_le_card inner
  have leftId := card_union_add_card_inter LA LB
  have rightCover : S.R⊆ S.foreignPorts∪(RA∪RB) := by
    intro z zr
    by_cases hit : G.Adj a z ∨ G.Adj b z
    · exact mem_union_left _ (mem_filter.mpr ⟨zr,hit⟩)
    have na : a≠z := fun e=>S.rightOff.1 (e.symm ▸ zr)
    have nb : b≠z := fun e=>S.rightOff.2 (e.symm ▸ zr)
    have la := hc.one_lt_dist_of_ne_of_not_adj na (fun h=>hit (.inl h))
    have lb := hc.one_lt_dist_of_ne_of_not_adj nb (fun h=>hit (.inr h))
    have cross := cross_metric S.L hc xL (fun h=>disjoint_left.mp S.dis h zr) (left_boundary S)
    have e1 := dist_eq_one_iff_adj.mpr ax.symm
    have e2 := dist_eq_one_iff_adj.mpr bx.symm
    have dz := rad z
    rw [cross,e1,e2] at dz
    have near : G.dist a z=2 ∨ G.dist b z=2 := by omega
    apply mem_union_right
    rcases near with h|h
    · exact mem_union_left _ (mem_inter.mpr ⟨zr,by simp [DistanceTwo,h]⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zr,by simp [DistanceTwo,h]⟩)
  have cR := (card_le_card rightCover).trans (card_union_le S.foreignPorts (RA∪RB))
  have rightId := card_union_le RA RB
  let all := insert a (insert b (S.L∪S.R))
  have allCover : (univ : Finset V)⊆all := by
    intro z _
    rcases S.cover z with rfl|rfl|lz|rz
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_self _ _)
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ lz))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ rz))
  have ord := card_le_card allCover
  rw [card_univ] at ord
  have c1 := card_insert_le a (insert b (S.L∪S.R))
  have c2 := card_insert_le b (S.L∪S.R)
  have c3 := card_union_le S.L S.R
  change all.card≤_ at c1
  omega

#print axioms order_add_left_nonports_le_sixteen_of_five_foreign
end Graffiti189LongestPath.CrossSaturation.Split.Five
