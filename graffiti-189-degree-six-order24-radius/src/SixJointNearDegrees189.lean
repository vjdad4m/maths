import SixJointNearGeometry189

namespace Graffiti189LongestPath
open SimpleGraph Finset
open private mem_distanceTwo from SmallSeparator189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace RadiusFiveNearEquality

theorem no_edges_between_active_and_full_inactive (hc : G.Connected)
    {x d a b : V} (Q : RadiusFiveNearEquality G x)
    (aT : a∈Q.T) (bT : b∈Q.T)
    (d4 : d∈Shell G x 4) (live : Q.Active d a) (dead : ¬Q.Active d b)
    (full : (JointFarGroup G x b).card=4) :
    ¬G.Adj a b ∧ ¬G.Adj (Q.rep a) (Q.rep b) := by
  have far := Q.far_of_full_inactive hc bT full d4 dead
  have close := Q.dist_le_three_of_active hc aT live
  obtain ⟨c,_,ac,cd⟩ := live
  have qa := hc.dist_triangle (u:=Q.rep a) (v:=c) (w:=d)
  have two := dist_eq_one_iff_adj.mpr ac
  have three := dist_eq_one_iff_adj.mpr cd
  constructor
  · intro e
    have one := dist_eq_one_iff_adj.mpr e.symm
    have u := hc.dist_triangle (u:=b) (v:=a) (w:=d)
    omega
  · intro e
    have one := dist_eq_one_iff_adj.mpr (Q.adj b bT)
    have mid := dist_eq_one_iff_adj.mpr e.symm
    have u := hc.dist_triangle (u:=b) (v:=Q.rep b) (w:=d)
    have w := hc.dist_triangle (u:=Q.rep b) (v:=Q.rep a) (w:=d)
    omega

theorem rep_no_extra_of_nonadj_to_full (hc : G.Connected)
    {x a b : V} (Q : RadiusFiveNearEquality G x)
    (aT : a∈Q.T) (bT : b∈Q.T) (ab : a≠b)
    (fullB : (JointFarGroup G x b).card=4) (no : ¬G.Adj b a) :
    ∀ z∈Shell G x 1,z∉Q.T → ¬G.Adj (Q.rep a) z := by
  intro z z1 zT az
  have bz := Q.adj_extra_near hc bT fullB z1 zT
  have n := mem_shell.mp (Q.near bT)
  have r := mem_shell.mp (Q.middle a aT)
  have ne : b≠Q.rep a := by intro e; rw [e] at n; omega
  have no' := Q.private_rep a aT b bT ab.symm
  have dist := Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne no' bz az.symm
  exact Q.no_rep_at_distance_two_if_nonadj hc aT bT fullB no dist

theorem selected_degree_le_five_plus_allowed (hc : G.Connected)
    {x a : V} (dx : G.degree x≤6) (Q : RadiusFiveNearEquality G x)
    (aT : a∈Q.T) (J : Finset V)
    (allowed : ∀ z∈Q.T,G.Adj a z → z∈J) :
    G.degree a≤5+J.card := by
  classical
  let A := Shell G x 1
  let R := A\Q.T
  have a1 := mem_shell.mp (Q.near aT)
  have a6 : A.card≤6 := by
    have eq : A=G.neighborFinset x := by
      ext z
      change z∈Shell G x 1 ↔ _
      rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
    rw [eq,G.card_neighborFinset_eq_degree]
    exact dx
  have r3 : R.card≤3 := by
    have h := card_sdiff_add_card_eq_card (show Q.T⊆A from Q.near)
    rw [Q.t3] at h
    change R.card+3=A.card at h
    omega
  have sub : G.neighborFinset a⊆insert x (insert (Q.rep a) (R∪J)) := by
    intro z zm
    have az := (G.mem_neighborFinset ..).mp zm
    have o := dist_eq_one_iff_adj.mpr az
    have d := hc.dist_triangle (u:=x) (v:=a) (w:=z)
    have cases : G.dist x z=0 ∨ G.dist x z=1 ∨ G.dist x z=2 := by omega
    apply mem_insert.mpr
    rcases cases with h|h|h
    · exact Or.inl ((hc.dist_eq_zero_iff.mp h).symm)
    · right
      apply mem_insert.mpr
      right
      by_cases zT : z∈Q.T
      · exact mem_union_right _ (allowed z zT az)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_shell.mpr h,zT⟩)
    · obtain ⟨j,jt,je⟩ := Q.rep_cover z (mem_shell.mpr h)
      have aj : a=j := by
        by_contra ne
        exact Q.private_rep j jt a aT ne (je.symm ▸ az)
      subst j
      exact Or.inr (mem_insert.mpr (.inl je.symm))
  have l := (card_le_card sub).trans (card_insert_le x (insert (Q.rep a) (R∪J)))
  have q := card_insert_le (Q.rep a) (R∪J)
  have k := card_union_le R J
  rw [G.card_neighborFinset_eq_degree] at l
  omega

theorem rep_degree_le_one_plus_group_plus_allowed (hc : G.Connected)
    {x a : V} (Q : RadiusFiveNearEquality G x)
    (aT : a∈Q.T) (J : Finset V)
    (noExtra : ∀ z∈Shell G x 1,z∉Q.T → ¬G.Adj (Q.rep a) z)
    (allowed : ∀ z∈Q.T,G.Adj (Q.rep a) (Q.rep z) → Q.rep z∈J) :
    G.degree (Q.rep a)≤1+(Shell G x 3∩JointFarGroup G x a).card+J.card := by
  classical
  let F := Shell G x 3∩JointFarGroup G x a
  have r2 := mem_shell.mp (Q.middle a aT)
  have a1 := mem_shell.mp (Q.near aT)
  have sub : G.neighborFinset (Q.rep a)⊆insert a (F∪J) := by
    intro z zm
    have az := (G.mem_neighborFinset ..).mp zm
    have o := dist_eq_one_iff_adj.mpr az
    have q := dist_eq_one_iff_adj.mpr az.symm
    have d := hc.dist_triangle (u:=x) (v:=Q.rep a) (w:=z)
    have e := hc.dist_triangle (u:=x) (v:=z) (w:=Q.rep a)
    have cases : G.dist x z=1 ∨ G.dist x z=2 ∨ G.dist x z=3 := by omega
    apply mem_insert.mpr
    rcases cases with h|h|h
    · left
      have zT : z∈Q.T := Classical.byContradiction (fun n=>noExtra z (mem_shell.mpr h) n az)
      by_contra no
      exact Q.private_rep a aT z zT no az.symm
    · right
      obtain ⟨j,jt,je⟩ := Q.rep_cover z (mem_shell.mpr h)
      exact mem_union_right _ (je ▸ allowed j jt (je.symm ▸ az))
    · right
      have ne : a≠z := by intro e; rw [e] at a1; omega
      have no : ¬G.Adj a z := by
        intro e
        have o := dist_eq_one_iff_adj.mpr e
        have t := hc.dist_triangle (u:=x) (v:=a) (w:=z)
        omega
      have tz := Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne no (Q.adj a aT) az
      exact mem_union_left _ (mem_inter.mpr ⟨mem_shell.mpr h,
        mem_union_left _ (mem_inter.mpr ⟨mem_shell.mpr h,tz⟩)⟩)
  have l := (card_le_card sub).trans (card_insert_le a (F∪J))
  have k := card_union_le F J
  rw [G.card_neighborFinset_eq_degree] at l
  change G.degree (Q.rep a)≤1+F.card+J.card
  omega

theorem third_group_le_three_of_fifth {x : V} (Q : RadiusFiveNearEquality G x)
    {a e : V} (aT : a∈Q.T) (e5 : e∈Shell G x 5) (eG : e∈JointFarGroup G x a) :
    (Shell G x 3∩JointFarGroup G x a).card≤3 := by
  have n : e∉Shell G x 3 := fun h=>by
    have a := mem_shell.mp h
    have b := mem_shell.mp e5
    omega
  have sub : Shell G x 3∩JointFarGroup G x a⊆(JointFarGroup G x a).erase e := by
    intro z zm
    obtain ⟨z3,zG⟩ := mem_inter.mp zm
    exact mem_erase.mpr ⟨fun h=>n (h ▸ z3),zG⟩
  have k := card_le_card sub
  rw [card_erase_of_mem eG] at k
  have q := Q.far_card a aT
  omega

end RadiusFiveNearEquality

#print axioms RadiusFiveNearEquality.no_edges_between_active_and_full_inactive
#print axioms RadiusFiveNearEquality.rep_degree_le_one_plus_group_plus_allowed
end Graffiti189LongestPath
