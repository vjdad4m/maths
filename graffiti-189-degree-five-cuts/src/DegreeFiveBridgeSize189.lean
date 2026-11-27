import DegreeFiveFourPort189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 foreign_subset from CrossSaturation189
open private left_boundary from AdjacentCut189
open private mem_positive from AdjacentCut189
open private cut_not_adj not_common high_a_port_cost secondA_right_and_left_le_five
  from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

private theorem count_cut_a (far : 3≤G.dist a b) :
    G.degree a=S.localA.card+S.foreignA.card := by
  classical
  have eq : G.neighborFinset a=S.localA∪S.foreignA := by
    ext x
    constructor
    · intro xv
      have e := (mem_neighborFinset G a x).mp xv
      rcases S.cover x with rfl|rfl|xl|xr
      · exact (e.ne rfl).elim
      · exact (cut_not_adj far e).elim
      · exact mem_union_left _ (mem_filter.mpr ⟨xl,e⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨xr,e⟩)
    intro h
    rcases mem_union.mp h with h|h
    · exact (mem_neighborFinset G a x).mpr (mem_filter.mp h).2
    · exact (mem_neighborFinset G a x).mpr (mem_filter.mp h).2
  have dis : Disjoint S.localA S.foreignA :=
    S.dis.mono (filter_subset _ _) (filter_subset _ _)
  have e := congrArg Finset.card eq
  rw [card_neighborFinset_eq_degree,card_union_of_disjoint dis] at e
  exact e

/-- At cut-endpoint degree exactly five and no four-port shore, both
second shells are tight and exhaust the full even budget. -/
theorem tight_a_second_shells_at_degree_five (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (da : G.degree a=5) (p : S.localA.card≤3) (q : S.foreignA.card≤3) :
    S.localA.card+(secondA G S.L a).card=5 ∧
      S.foreignA.card+(secondA G S.R a).card=5 ∧
      (∀ z,G.dist a z≤3) := by
  classical
  let T := switch S rightConnected rightA rightB
  have deg := count_cut_a S far
  have lpos : 1<S.localA.card := by omega
  have rpos : 1<T.localA.card := by change 1<S.foreignA.card; omega
  have lower (S' : Split G a b) (p' : 1<S'.localA.card) :
      5≤S'.localA.card+(secondA G S'.L a).card := by
    obtain ⟨u,up,v,vp,uv⟩ := one_lt_card.mp p'
    rcases degree u v uv with h|h
    · exact high_a_port_cost S' hc far up h
    · exact high_a_port_cost S' hc far vp h
  have loL := lower S lpos
  have loR := lower T rpos
  change 5≤S.foreignA.card+(secondA G S.R a).card at loR
  have m := secondA_right_and_left_le_five S even
  refine ⟨by omega,by omega,?_⟩
  have dis : Disjoint (secondA G S.L a) (secondA G S.R a) :=
    S.dis.mono inter_subset_left inter_subset_left
  have sub : secondA G S.L a ∪ secondA G S.R a ⊆ DistanceTwo G a :=
    union_subset inter_subset_right inter_subset_right
  have n := card_le_card sub
  rw [card_union_of_disjoint dis] at n
  intro z
  apply Nat.le_of_not_gt
  intro too
  have h := distanceTwo_add_two_le_even_of_far hc (show 4≤G.dist a z by omega)
  have ca := even a
  omega

noncomputable def inner (G : SimpleGraph V) (R : Finset V) (a b : V)
    [DecidableRel G.Adj] : Finset V := R.filter (fun z=>¬G.Adj a z ∧ ¬G.Adj b z)

/-- Opposite a mixed edge, each nonporter consumes either
a second-shell slot at b or a fourth-shell slot at the b-porter. -/
theorem opposite_inner_bound_from_bridge (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (radiusA : ∀ z,G.dist a z≤3) (radiusB : ∀ z,G.dist b z≤3)
    (bShell : (S.R.filter (G.Adj b)).card+(secondA G S.R b).card=5)
    (bridge : portBridge S) :
    (inner G S.R a b).card+2*(S.R.filter (G.Adj b)).card≤9 := by
  classical
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
  let B := S.R.filter (G.Adj b)
  let F := secondA G S.R b
  let I := inner G S.R a b
  have Boff : a∉B := fun h=>S.rightOff.1 (mem_filter.mp h).1
  have noAY : ¬G.Adj a y := by
    intro e
    exact not_common far e by'
  have ay : a≠y := fun e=>S.leftOff.1 (e.symm ▸ yl)
  have ya2 := d2 hc ay noAY ax xy
  have ya2' : G.dist y a=2 := by
    rw [SimpleGraph.dist_comm]
    exact (mem_filter.mp ya2).2
  have yb1 := dist_eq_one_iff_adj.mpr by'.symm
  have a_even : a∈PositiveEven G y := by
    apply mem_positive.mpr
    refine ⟨ay,?_⟩
    rw [ya2']
    decide
  have port_even : B ⊆ PositiveEven G y := by
    intro z zz
    obtain ⟨zr,bz⟩ := mem_filter.mp zz
    have yz : y≠z := fun e=>disjoint_left.mp S.dis yl (e ▸ zr)
    have e := d2 hc yz (S.cross _ yl _ zr) by'.symm bz
    apply mem_positive.mpr
    refine ⟨Ne.symm yz,?_⟩
    rw [(mem_filter.mp e).2]
    decide
  have inner_even : I\F ⊆ PositiveEven G y := by
    intro z zz
    obtain ⟨zi,zf⟩ := mem_sdiff.mp zz
    obtain ⟨zr,az,bz⟩ := mem_filter.mp zi
    have zo : z∉S.L := fun e=>disjoint_left.mp S.dis e zr
    have da := hc.one_lt_dist_of_ne_of_not_adj (show a≠z from fun e=>S.rightOff.1 (e.symm ▸ zr)) az
    have db := hc.one_lt_dist_of_ne_of_not_adj (show b≠z from fun e=>S.rightOff.2 (e.symm ▸ zr)) bz
    have d2no : G.dist b z≠2 := by
      intro e
      exact zf (mem_inter.mpr ⟨zr,by simp [DistanceTwo,e]⟩)
    have e := cross_metric S.L hc yl zo (left_boundary S)
    have hb := radiusB z
    have ha := radiusA z
    have yz4 : G.dist y z=4 := by omega
    apply mem_positive.mpr
    refine ⟨fun h=>zo (h.symm ▸ yl),?_⟩
    rw [yz4]
    decide
  have sub : insert a B ∪ (I\F) ⊆ PositiveEven G y := by
    intro z zz
    rcases mem_union.mp zz with za|zi
    · rcases mem_insert.mp za with rfl|zb
      · exact a_even
      exact port_even zb
    exact inner_even zi
  have dis : Disjoint (insert a B) (I\F) := by
    apply disjoint_left.mpr
    intro z zb zi
    obtain ⟨zr,_,bz⟩ := mem_filter.mp (mem_sdiff.mp zi).1
    rcases mem_insert.mp zb with rfl|zb
    · exact S.rightOff.1 zr
    exact bz (mem_filter.mp zb).2
  have cap : (PositiveEven G y).card≤5 := by
    have ym : y∈EvenFrom G y := by simp [EvenFrom,SimpleGraph.dist_self]
    have e := card_erase_of_mem ym
    have m := even y
    change ((EvenFrom G y).erase y).card≤5
    omega
  have n := card_le_card sub
  rw [card_union_of_disjoint dis,card_insert_of_not_mem Boff] at n
  have rest : I.card≤F.card+(I\F).card := by
    have cover : I⊆F∪(I\F) := by
      intro u ui
      by_cases uf : u∈F
      · exact mem_union_left _ uf
      exact mem_union_right _ (mem_sdiff.mpr ⟨ui,uf⟩)
    exact (card_le_card cover).trans (card_union_le _ _)
  change B.card+F.card=5 at bShell
  change I.card+2*B.card≤9
  omega

/-- If both cut vertices have degree five and each attachment class has at
most three vertices, the shore opposite a mixed edge has order at most nine.
If it has exactly five attachments, its order is at most eight. -/
theorem opposite_bridge_shore_le_nine_exact_cut_degree (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a5 : G.degree a=5) (b5 : G.degree b=5)
    (aL : S.localA.card≤3) (aR : S.foreignA.card≤3)
    (bL : (S.L.filter (G.Adj b)).card≤3) (bR : (S.R.filter (G.Adj b)).card≤3)
    (bridge : portBridge S) :
    S.R.card≤9 ∧
      (S.foreignA.card+(S.R.filter (G.Adj b)).card=5 → S.R.card≤8) := by
  classical
  let T := S.flip
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have aT := tight_a_second_shells_at_degree_five S hc far even degree rightConnected rightA rightB a5 aL aR
  have bT := tight_a_second_shells_at_degree_five T hc far' even degree rightConnected rightB rightA b5 bL bR
  have bBridge : portBridge T := by
    obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
    exact ⟨y,yl,x,xl,by',xy.symm,ax⟩
  have q := opposite_inner_bound_from_bridge S hc far even aT.2.2 bT.2.2 bT.2.1 bridge
  have p := opposite_inner_bound_from_bridge T hc far' even bT.2.2 aT.2.2 aT.2.1 bBridge
  have hI : inner G T.R b a = inner G S.R a b := by
    change inner G S.R b a = inner G S.R a b
    ext v
    simp [inner,and_comm]
  rw [hI] at p
  change (inner G S.R a b).card+2*S.foreignA.card≤9 at p
  have cover : S.R⊆(S.foreignA∪(S.R.filter (G.Adj b)))∪inner G S.R a b := by
    intro z zr
    by_cases az : G.Adj a z
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zr,az⟩))
    by_cases bz : G.Adj b z
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨zr,bz⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨zr,az,bz⟩)
  have n := (card_le_card cover).trans (card_union_le _ _)
  have e := card_union_le S.foreignA (S.R.filter (G.Adj b))
  constructor
  · omega
  intro total
  omega

#print axioms tight_a_second_shells_at_degree_five
#print axioms opposite_inner_bound_from_bridge
#print axioms opposite_bridge_shore_le_nine_exact_cut_degree
end Graffiti189LongestPath.CrossSaturation.Split.Five
