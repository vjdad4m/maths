import SixOrder25ThirdUniversal189

namespace Graffiti189LongestPath
open SimpleGraph Finset
open private mem_distanceTwo from SmallSeparator189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace RadiusFiveEquality

theorem root_and_fourth_sub_two
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : Fintype.card V=25)
    (Q : RadiusFiveEquality G x) {a : V} (aT : a∈Q.T) :
    insert x (Shell G x 4) ⊆ DistanceTwo G (Q.rep a) := by
  have b2 := mem_shell.mp (Q.middle a aT)
  intro z zm
  rcases mem_insert.mp zm with rfl|d4
  · exact mem_distanceTwo.mpr (by rw [dist_comm]; exact b2)
  obtain ⟨c,_,bc,cz⟩ := Q.fourth_meets_every_group hc cap conn high dx n aT d4
  have hz := mem_shell.mp d4
  have ne : Q.rep a≠z := by intro e; rw [e] at b2; omega
  have no : ¬G.Adj (Q.rep a) z := by
    intro e
    have o := dist_eq_one_iff_adj.mpr e
    have t := hc.dist_triangle (u:=x) (v:=Q.rep a) (w:=z)
    omega
  exact Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne no bc cz

theorem joint_groups_anticomplete
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : Fintype.card V=25)
    (near6 : (Shell G x 1).card=6) (d3 : (Shell G x 4).card=3)
    (Q : RadiusFiveEquality G x) :
    ∀ a∈Q.T,∀ b∈Q.T,a≠b →
      ∀ c∈Shell G x 3,∀ d∈Shell G x 3,
      G.Adj (Q.rep a) c → G.Adj (Q.rep b) d → ¬G.Adj c d := by
  classical
  let A := Shell G x 1
  let D := Shell G x 4
  let X := insert x D
  let R := A\Q.T
  have xD : x∉D := fun e=>by have d := mem_shell.mp e; rw [dist_self] at d; omega
  have X4 : X.card=4 := by
    change (insert x D).card=4
    rw [card_insert_of_not_mem xD,d3]
  have R3 : R.card=3 := by
    have c := card_sdiff_add_card_eq_card (show Q.T⊆A from Q.near)
    rw [Q.t3,near6] at c
    change R.card=3
    change R.card+3=6 at c
    omega
  have x_dis {Y : Finset V} (sub : Y⊆A) : Disjoint X Y := by
    apply disjoint_left.mpr
    intro z zx zy
    have z1 := mem_shell.mp (sub zy)
    rcases mem_insert.mp zx with e|e
    · rw [e,dist_self] at z1
      omega
    · have w := mem_shell.mp e
      omega
  have pre (a : V) (aT : a∈Q.T) :
      X⊆DistanceTwo G (Q.rep a) := Q.root_and_fourth_sub_two hc cap conn high dx n aT
  have spare (a : V) (aT : a∈Q.T) : ∃ z∈R,G.Adj (Q.rep a) z := by
    by_contra! deny
    have sub : R⊆DistanceTwo G (Q.rep a) := by
      intro z zm
      obtain ⟨z1,zn⟩ := mem_sdiff.mp zm
      have zed := Q.adj_extra_near hc aT z1 zn
      have ne : Q.rep a≠z := by
        intro e
        have k := mem_shell.mp (Q.middle a aT)
        have l := mem_shell.mp z1
        rw [e] at k
        omega
      exact Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne
        (deny z zm) (Q.adj a aT).symm zed
    have h := (card_le_card (union_subset (pre a aT) sub)).trans
      (distanceTwo_le_of_even 6 (Q.rep a) (cap (Q.rep a)))
    rw [card_union_of_disjoint (x_dis sdiff_subset),X4,R3] at h
    omega
  have clique (a : V) (aT : a∈Q.T) (b : V) (bT : b∈Q.T) (ab : a≠b) :
      G.Adj a b := by
    by_contra no
    obtain ⟨z,zm,bz⟩ := spare b bT
    obtain ⟨z1,zn⟩ := mem_sdiff.mp zm
    have az := Q.adj_extra_near hc aT z1 zn
    have ne : a≠Q.rep b := by
      intro e
      have k := mem_shell.mp (Q.near aT)
      have l := mem_shell.mp (Q.middle b bT)
      rw [e] at k
      omega
    have d := Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne
      (Q.private_rep b bT a aT ab) az bz.symm
    exact Q.no_rep_at_distance_two_if_nonadj hc bT aT no d
  have allSel (a : V) (aT : a∈Q.T) :
      Q.T.erase a⊆DistanceTwo G (Q.rep a) := by
    intro z zm
    obtain ⟨ne,zT⟩ := mem_erase.mp zm
    have r : Q.rep a≠z := by
      intro e
      have k := mem_shell.mp (Q.middle a aT)
      have l := mem_shell.mp (Q.near zT)
      rw [e] at k
      omega
    have not : ¬G.Adj (Q.rep a) z := fun e=>Q.private_rep a aT z zT ne e.symm
    exact Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc r not
      (Q.adj a aT).symm (clique a aT z zT ne.symm)
  have full (a : V) (aT : a∈Q.T) :
      X∪Q.T.erase a=DistanceTwo G (Q.rep a) := by
    apply eq_of_subset_of_card_le (union_subset (pre a aT) (allSel a aT))
    have le := distanceTwo_le_of_even 6 (Q.rep a) (cap (Q.rep a))
    rw [card_union_of_disjoint (x_dis ((erase_subset ..).trans Q.near)),
      X4,card_erase_of_mem aT,Q.t3]
    exact le
  intro a aT b bT ab c c3 d d3' ac bd cd
  have da : ¬G.Adj (Q.rep a) d := by
    intro edge
    exact disjoint_left.mp (Q.far_dis a aT b bT ab)
      (Q.third_of_rep_adj hc aT d3' edge) (Q.third_of_rep_adj hc bT d3' bd)
  have ne : Q.rep a≠d := by
    intro e
    have k := mem_shell.mp (Q.middle a aT)
    have l := mem_shell.mp d3'
    rw [e] at k
    omega
  have h := Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne da ac cd
  rw [← full a aT] at h
  have ddep := mem_shell.mp d3'
  rcases mem_union.mp h with hd|hd
  · rcases mem_insert.mp hd with rfl|hd
    · rw [dist_self] at ddep
      omega
    · have l := mem_shell.mp hd
      omega
  · have l := mem_shell.mp (Q.near (mem_erase.mp hd).2)
    omega

end RadiusFiveEquality

#print axioms RadiusFiveEquality.joint_groups_anticomplete
end Graffiti189LongestPath
