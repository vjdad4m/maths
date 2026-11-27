import DegreeFiveFourForeign189
import DegreeFiveFiveForeign189
import DegreeFiveUniquePortClosureTest189
import DegreeFiveFourPort189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private both_shore_shells_le_four from DegreeFiveFiveForeign189
open private opposite_ports_at_exclusive_le_four from DegreeFiveUniquePortClosureTest189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Split G a b)
set_option linter.unusedSectionVars false

def sharedOnLeft : Finset V := S.L.filter (fun x=>G.Adj a x ∧ G.Adj b x)

theorem order_le_fifteen_add_shared_of_four_foreign
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {x : V} (xL : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (four : 4≤S.foreignPorts.card) :
    Fintype.card V≤15+(sharedOnLeft S).card := by
  classical
  let LA := secondA G S.L a
  let LB := secondA G S.L b
  let RA := secondA G S.R a
  let RB := secondA G S.R b
  let X := secondA G S.L x
  let W := Shell G x 4
  have ba : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have ac := both_shore_shells_le_four S ⟨S.leftOff.2,S.rightOff.2⟩ two even
  have bc := both_shore_shells_le_four S ⟨S.leftOff.1,S.rightOff.1⟩ ba even
  change LA.card+RA.card≤4 at ac
  change LB.card+RB.card≤4 at bc
  have near := (near_universal_at_four_foreign S hc even conn xL ax bx four).2
  have foreign : S.foreignPorts⊆DistanceTwo G x := by
    intro y yp
    obtain ⟨yr,hit⟩ := mem_filter.mp yp
    have n : x≠y := fun e=>disjoint_left.mp S.dis xL (e.symm ▸ yr)
    have no := S.cross x xL y yr
    exact hit.elim (fun h=>d2 hc n no ax.symm h) (fun h=>d2 hc n no bx.symm h)
  have dis : Disjoint X S.foreignPorts := S.dis.mono inter_subset_left (filter_subset _ _)
  have q := card_le_card (union_subset (show X⊆DistanceTwo G x from inter_subset_right) foreign)
  rw [card_union_of_disjoint dis] at q
  have budget := shell_two_four_le_of_even (x:=x) (d:=5) (even x)
  rw [shell_two] at budget
  change _+W.card≤5 at budget
  have rad (z : V) : G.dist x z≤4 := by
    apply Classical.byContradiction
    intro bad
    have far : 4<G.dist x z := by omega
    have cap := shell_card_of_far hc 2 conn (i:=4) (by decide) far
    change 2≤W.card at cap
    omega
  let K := sharedOnLeft S
  have leftCover : S.L⊆K∪((LA∪LB)∪X) := by
    intro z zl
    by_cases both : G.Adj a z ∧ G.Adj b z
    · exact mem_union_left _ (mem_filter.mpr ⟨zl,both⟩)
    have zx : z≠x := fun e=>both (e.symm ▸ ⟨ax,bx⟩)
    apply mem_union_right
    by_cases xz : G.Adj x z
    · have naz : a≠z := fun e=>S.leftOff.1 (e.symm ▸ zl)
      have nbz : b≠z := fun e=>S.leftOff.2 (e.symm ▸ zl)
      apply mem_union_left
      by_cases az : G.Adj a z
      · have nb : ¬G.Adj b z := fun bz=>both ⟨az,bz⟩
        exact mem_union_right _ (mem_inter.mpr ⟨zl,d2 hc nbz nb bx xz⟩)
      exact mem_union_left _ (mem_inter.mpr ⟨zl,d2 hc naz az ax xz⟩)
    have lower := hc.one_lt_dist_of_ne_of_not_adj (Ne.symm zx) xz
    have upper := near z zl
    exact mem_union_right _ (mem_inter.mpr ⟨zl,
      by simp [DistanceTwo,show G.dist x z=2 by omega]⟩)
  have rightCover : S.R⊆ (S.foreignPorts∪(RA∪RB))∪W := by
    intro z zr
    by_cases hit : G.Adj a z ∨ G.Adj b z
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zr,hit⟩))
    by_cases z4 : G.dist x z=4
    · exact mem_union_right _ (mem_shell.mpr z4)
    have na : a≠z := fun e=>S.rightOff.1 (e.symm ▸ zr)
    have nb : b≠z := fun e=>S.rightOff.2 (e.symm ▸ zr)
    have la := hc.one_lt_dist_of_ne_of_not_adj na (fun h=>hit (.inl h))
    have lb := hc.one_lt_dist_of_ne_of_not_adj nb (fun h=>hit (.inr h))
    have cross := cross_metric S.L hc xL (fun h=>disjoint_left.mp S.dis h zr) (left_boundary S)
    have e1 := dist_eq_one_iff_adj.mpr ax.symm
    have e2 := dist_eq_one_iff_adj.mpr bx.symm
    have dz := rad z
    rw [cross,e1,e2] at dz z4
    have near : G.dist a z=2 ∨ G.dist b z=2 := by omega
    apply mem_union_left
    apply mem_union_right
    rcases near with h|h
    · exact mem_union_left _ (mem_inter.mpr ⟨zr,by simp [DistanceTwo,h]⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zr,by simp [DistanceTwo,h]⟩)
  have l1 := (card_le_card leftCover).trans (card_union_le K ((LA∪LB)∪X))
  have l2 := card_union_le (LA∪LB) X
  have l3 := card_union_le LA LB
  have r1 := (card_le_card rightCover).trans (card_union_le (S.foreignPorts∪(RA∪RB)) W)
  have r2 := card_union_le S.foreignPorts (RA∪RB)
  have r3 := card_union_le RA RB
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
  change Fintype.card V≤15+K.card
  omega

theorem order_le_nineteen_of_exclusive_four_foreign
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (rightConn : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ u∈S.R,G.Adj a u) (rightB : ∃ u∈S.R,G.Adj b u)
    (none : ∀ u∈S.R,¬(G.Adj a u ∧ G.Adj b u))
    {x : V} (xL : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (four : 4≤S.foreignPorts.card) : Fintype.card V≤19 := by
  classical
  let T := switch S rightConn rightA rightB
  obtain ⟨u,ur,au⟩ := rightA
  have h := opposite_ports_at_exclusive_le_four T hc even ur au (fun bu=>none u ur ⟨au,bu⟩)
  have m : sharedOnLeft S⊆T.foreignA := by
    intro z zz
    obtain ⟨zl,az,_⟩ := mem_filter.mp zz
    exact mem_filter.mpr ⟨zl,az⟩
  have k := (card_le_card m).trans h
  have bound := order_le_fifteen_add_shared_of_four_foreign S hc two even conn xL ax bx four
  omega

#print axioms order_le_fifteen_add_shared_of_four_foreign
#print axioms order_le_nineteen_of_exclusive_four_foreign
end Graffiti189LongestPath.CrossSaturation.Split.Five
