import SixOrder25ThirdAnticomplete189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private mem_distanceTwo from SmallSeparator189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace RadiusFiveEquality

theorem adj_rep_of_third_group
    (hc : G.Connected) {x : V} (Q : RadiusFiveEquality G x) {a c : V}
    (aT : a∈Q.T) (c3 : c∈Shell G x 3) (cg : c∈JointFarGroup G x a) :
    G.Adj (Q.rep a) c := by
  have c3' := mem_shell.mp c3
  have a1 := mem_shell.mp (Q.near aT)
  have ac2 : G.dist a c=2 := by
    rcases mem_union.mp cg with j|j
    · exact mem_distanceTwo.mp (mem_inter.mp j).2
    · have bad := mem_shell.mp (mem_inter.mp j).1
      omega
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a c
  have l := hp.trans ac2
  let d := p.getVert 1
  have ad : G.Adj a d := by simpa [d] using p.adj_getVert_succ (i:=0) (by omega)
  have dc : G.Adj d c := by
    have q := p.adj_getVert_succ (i:=1) (by omega)
    have r : p.getVert 2=c := by rw [←l,getVert_length]
    simpa only [r] using q
  have q := hc.dist_triangle (u:=x) (v:=a) (w:=d)
  have r := hc.dist_triangle (u:=x) (v:=d) (w:=c)
  have da := dist_eq_one_iff_adj.mpr ad
  have dd := dist_eq_one_iff_adj.mpr dc
  have d2 : d∈Shell G x 2 := mem_shell.mpr (by omega)
  obtain ⟨b,bT,br⟩ := Q.rep_cover d d2
  have ab : a=b := by
    by_contra ne
    exact Q.private_rep b bT a aT ne (br.symm ▸ ad)
  subst b
  exact br.symm ▸ dc

end RadiusFiveEquality

theorem no_order25_second_shell_three_at_degree_six
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : Fintype.card V=25)
    (b3 : (Shell G x 2).card=3) : False := by
  classical
  let A := Shell G x 1
  let B := Shell G x 2
  let C := Shell G x 3
  let D := Shell G x 4
  have rad := eccentricity_le_four_at_order25_degree_six hc cap conn high dx n
  have e0 : Shell G x 5=∅ := eq_empty_iff_forall_not_mem.mpr (fun w wm=>by
    have k := mem_shell.mp wm
    have r := rad w
    omega)
  have cover : (univ : Finset V) ⊆ insert x (A∪B∪C∪D) := by
    intro w _
    have r := rad w
    have cases : G.dist x w=0 ∨ G.dist x w=1 ∨ G.dist x w=2 ∨ G.dist x w=3 ∨ G.dist x w=4 := by omega
    rcases cases with d|d|d|d|d
    · exact mem_insert.mpr (.inl ((hc.dist_eq_zero_iff.mp d).symm))
    · exact mem_insert.mpr (.inr (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_shell.mpr d)))))
    · exact mem_insert.mpr (.inr (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_shell.mpr d)))))
    · exact mem_insert.mpr (.inr (mem_union_left _ (mem_union_right _ (mem_shell.mpr d))))
    · exact mem_insert.mpr (.inr (mem_union_right _ (mem_shell.mpr d)))
  have a6 : A.card≤6 := by
    have eq : A=G.neighborFinset x := by
      ext z
      change z∈Shell G x 1 ↔ _
      rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
    rw [eq,G.card_neighborFinset_eq_degree]
    exact dx
  have d3 : D.card≤3 := by
    have w := shell_two_four_le_of_even (cap x)
    change B.card+D.card≤6 at w
    change B.card=3 at b3
    omega
  have c12 : C.card≤12 := third_shell_le_twelve_at_degree_six hc cap x dx
  have s := (card_le_card cover).trans (card_insert_le x (A∪B∪C∪D))
  rw [card_univ,n] at s
  have u := card_union_le (A∪B∪C) D
  have v := card_union_le (A∪B) C
  have w := card_union_le A B
  change B.card=3 at b3
  have aExact : A.card=6 := by omega
  have cExact : C.card=12 := by omega
  have dExact : D.card=3 := by omega
  have eq : (Shell G x 3).card+(Shell G x 5).card=12 := by
    rw [e0,card_empty,add_zero]
    exact cExact
  obtain ⟨Q⟩ := radius_five_equality hc cap x dx b3 eq
  let P (a : V) := JointFarGroup G x a
  let F (c : V) := D.filter (G.Adj c)
  have pC (a : V) : P a⊆C := by
    intro y ym
    rcases mem_union.mp ym with j|j
    · exact (mem_inter.mp j).1
    · have b := (mem_inter.mp j).1
      rw [e0] at b
      exact False.elim (not_mem_empty _ b)
  have group (c : V) (cm : c∈C) : ∃ a∈Q.T,c∈P a :=
    mem_biUnion.mp (Q.far_cover (mem_union_left _ cm))
  have p2 (a : V) (aT : a∈Q.T) (c : V) (cg : c∈P a) (ch : 6≤G.degree c) :
      2≤(F c).card := by
    have c3 := mem_shell.mp (pC a cg)
    have sub : G.neighborFinset c ⊆ insert (Q.rep a) ((P a).erase c ∪ F c) := by
      intro z zm
      have cz := (G.mem_neighborFinset ..).mp zm
      have z1 := dist_eq_one_iff_adj.mpr cz
      have z2 := dist_eq_one_iff_adj.mpr cz.symm
      have r := hc.dist_triangle (u:=x) (v:=c) (w:=z)
      have t := hc.dist_triangle (u:=x) (v:=z) (w:=c)
      have cases : G.dist x z=2 ∨ G.dist x z=3 ∨ G.dist x z=4 := by omega
      rcases cases with k|k|k
      · obtain ⟨b,bT,br⟩ := Q.rep_cover z (mem_shell.mpr k)
        have ca := Q.third_of_rep_adj hc bT (pC a cg) (br.symm ▸ cz.symm)
        have same : a=b := by
          by_contra ne
          exact disjoint_left.mp (Q.far_dis a aT b bT ne) cg ca
        subst b
        exact mem_insert.mpr (.inl br.symm)
      · obtain ⟨b,bT,bg⟩ := group z (mem_shell.mpr k)
        have same : a=b := by
          by_contra ne
          exact Q.joint_groups_anticomplete hc cap conn high dx n aExact dExact a aT b bT ne
            c (pC a cg) z (pC b bg) (Q.adj_rep_of_third_group hc aT (pC a cg) cg)
            (Q.adj_rep_of_third_group hc bT (pC b bg) bg) cz
        subst b
        exact mem_insert.mpr (.inr (mem_union_left _ (mem_erase.mpr ⟨cz.ne.symm,bg⟩)))
      · exact mem_insert.mpr (.inr (mem_union_right _ (mem_filter.mpr ⟨mem_shell.mpr k,cz⟩)))
    have s := (card_le_card sub).trans (card_insert_le (Q.rep a) ((P a).erase c∪F c))
    have r := card_union_le ((P a).erase c) (F c)
    rw [card_erase_of_mem cg,Q.far_card a aT] at r
    rw [G.card_neighborFinset_eq_degree] at s
    omega
  obtain ⟨i,im,j,jm,ne⟩ := one_lt_card.mp (show 1<C.card by omega)
  obtain ⟨c,cm,ch⟩ : ∃ c∈C,6≤G.degree c :=
    (high i j ne).elim (fun h=>⟨i,im,h⟩) (fun h=>⟨j,jm,h⟩)
  obtain ⟨a,aT,cg⟩ := group c cm
  have c2 := p2 a aT c cg ch
  let J := C\P a
  let H := J.filter (fun z=>6≤G.degree z)
  have j8 : J.card=8 := by
    have k := card_sdiff_add_card_eq_card (pC a)
    rw [Q.far_card a aT,cExact] at k
    change J.card+4=12 at k
    omega
  have low : (J\H).card≤1 := by
    by_contra! over
    obtain ⟨i,im,j,jm,ij⟩ := one_lt_card.mp over
    obtain ⟨iJ,iH⟩ := mem_sdiff.mp im
    obtain ⟨jJ,jH⟩ := mem_sdiff.mp jm
    exact (high i j ij).elim (fun e=>iH (mem_filter.mpr ⟨iJ,e⟩))
      (fun e=>jH (mem_filter.mpr ⟨jJ,e⟩))
  have sub : H⊆DistanceTwo G c := by
    intro z zm
    obtain ⟨zj,zh⟩ := mem_filter.mp zm
    obtain ⟨zc,zout⟩ := mem_sdiff.mp zj
    obtain ⟨b,bT,zg⟩ := group z zc
    have ne : a≠b := fun e=>zout (e.symm ▸ zg)
    have z2 := p2 b bT z zg zh
    have incl : F c∪F z⊆D := union_subset (filter_subset _ _) (filter_subset _ _)
    have union := (card_le_card incl).trans d3
    have form := card_union_add_card_inter (F c) (F z)
    obtain ⟨y,ym⟩ := card_pos.mp (show 0<(F c∩F z).card by omega)
    obtain ⟨yc,yz⟩ := mem_inter.mp ym
    have no := Q.joint_groups_anticomplete hc cap conn high dx n aExact dExact a aT b bT ne
      c cm z zc (Q.adj_rep_of_third_group hc aT cm cg) (Q.adj_rep_of_third_group hc bT zc zg)
    have cn : c≠z := fun e=>zout (e ▸ cg)
    exact Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc cn no
      (mem_filter.mp yc).2 (mem_filter.mp yz).2.symm
  have hh := (card_le_card sub).trans (distanceTwo_le_of_even 6 c (cap c))
  have coverH := card_sdiff_add_card_eq_card (show H⊆J from filter_subset _ _)
  omega

open private order_sum_odd_shells_of_radius_six from SixThreeRadiusFive189

theorem four_le_second_shell_at_order25_degree_six
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : Fintype.card V=25) :
    4≤(Shell G x 2).card := by
  have rad := eccentricity_le_four_at_order25_degree_six hc cap conn high dx n
  have e0 : Shell G x 5=∅ := eq_empty_iff_forall_not_mem.mpr (fun w wm=>by
    have k := mem_shell.mp wm
    have r := rad w
    omega)
  have b := order_sum_odd_shells_of_radius_six cap x dx (fun y=>(rad y).trans (by decide))
  rw [n,e0,card_empty] at b
  obtain ⟨y,ym⟩ := card_pos.mp (show 0<(Shell G x 3).card by omega)
  have yd := mem_shell.mp ym
  have h := shell_card_of_far hc 3 conn (x:=x) (y:=y) (i:=2) (by decide) (by omega)
  by_contra! bad
  exact no_order25_second_shell_three_at_degree_six hc cap conn high dx n (by omega)

#print axioms no_order25_second_shell_three_at_degree_six
#print axioms four_le_second_shell_at_order25_degree_six
end Graffiti189LongestPath
