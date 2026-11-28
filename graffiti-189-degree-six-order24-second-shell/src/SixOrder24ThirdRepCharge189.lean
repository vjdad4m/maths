import SixOrder24ThirdNearGeometry189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private mem_distanceTwo from SmallSeparator189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace RadiusFiveNearEquality

theorem adj_rep_of_third_group
    (hc : G.Connected) {x : V} (Q : RadiusFiveNearEquality G x) {a c : V}
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

theorem third_of_rep_adj
    (hc : G.Connected) {x : V} (Q : RadiusFiveNearEquality G x) {a c : V}
    (atT : a∈Q.T) (c3 : c∈Shell G x 3) (ac : G.Adj (Q.rep a) c) :
    c∈JointFarGroup G x a := by
  have aa := mem_shell.mp (Q.near atT)
  have cc := mem_shell.mp c3
  have ne : a≠c := by intro e; rw [e] at aa; omega
  have na : ¬G.Adj a c := by
    intro e
    have z := dist_eq_one_iff_adj.mpr e
    have t := hc.dist_triangle (u:=x) (v:=a) (w:=c)
    omega
  exact mem_union_left _ (mem_inter.mpr ⟨c3,
    Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne na (Q.adj a atT) ac⟩)

noncomputable def missingSpare {x : V} (Q : RadiusFiveNearEquality G x) (a : V) : Finset V :=
  ((Shell G x 1)\Q.T).filter (fun z=>¬G.Adj (Q.rep a) z)

noncomputable def nearPartners {x : V} (Q : RadiusFiveNearEquality G x) (a : V) : Finset V :=
  Q.T.filter (G.Adj a)

noncomputable def foreignThird {x : V} (Q : RadiusFiveNearEquality G x) (a : V) : Finset V := by
  let _ := Q
  exact (Shell G x 3).filter (fun c=>c∉JointFarGroup G x a ∧
    ∃ z∈JointFarGroup G x a,G.Adj z c)

theorem radius_four_group_sub_third {x a : V}
    (none : Shell G x 5=∅) : JointFarGroup G x a⊆Shell G x 3 := by
  intro z zm
  rcases mem_union.mp zm with zf|zf
  · exact (mem_inter.mp zf).1
  · exact False.elim (not_mem_empty _ (none ▸ (mem_inter.mp zf).1))

theorem rep_four_part_charge
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x a : V} (dx : G.degree x≤6) (n : 24≤Fintype.card V)
    (Q : RadiusFiveNearEquality G x) (aT : a∈Q.T)
    (full : (JointFarGroup G x a).card=4) (none : Shell G x 5=∅) :
    1+(Shell G x 4).card+(Q.missingSpare a).card+(Q.nearPartners a).card+(Q.foreignThird a).card≤6 := by
  classical
  let D := Shell G x 4
  let X := insert x D
  let R := Q.missingSpare a
  let K := Q.nearPartners a
  let F := Q.foreignThird a
  let b := Q.rep a
  have b2 := mem_shell.mp (Q.middle a aT)
  change G.dist x b=2 at b2
  have ax : x∉D := fun m=>by
    have r : G.dist x x=4 := mem_shell.mp m
    rw [dist_self] at r
    omega
  have disDepth {s : Finset V} {i : ℕ} (ne1 : i≠0) (ne2 : i≠4)
      (su : s⊆Shell G x i) : Disjoint X s := by
    apply disjoint_left.mpr
    intro z zx zs
    have zi := mem_shell.mp (su zs)
    rcases mem_insert.mp zx with rfl|h
    · rw [dist_self] at zi
      exact ne1 zi.symm
    · have z4 := mem_shell.mp h
      omega
  have r1 : R⊆Shell G x 1 := fun z m=>(mem_sdiff.mp (mem_filter.mp m).1).1
  have k1 : K⊆Shell G x 1 := (filter_subset _ _).trans Q.near
  have f3 : F⊆Shell G x 3 := filter_subset _ _
  have rk : Disjoint R K := by
    apply disjoint_left.mpr
    intro z zr zk
    exact (mem_sdiff.mp (mem_filter.mp zr).1).2 (mem_filter.mp zk).1
  have rf : Disjoint R F := by
    apply disjoint_left.mpr
    intro z zr zf
    have h := mem_shell.mp (r1 zr)
    have k := mem_shell.mp (f3 zf)
    omega
  have kf : Disjoint K F := by
    apply disjoint_left.mpr
    intro z zk zf
    have h := mem_shell.mp (k1 zk)
    have k := mem_shell.mp (f3 zf)
    omega
  have xr : Disjoint X R := disDepth (by decide) (by decide) r1
  have xk : Disjoint X K := disDepth (by decide) (by decide) k1
  have xf : Disjoint X F := disDepth (by decide) (by decide) f3
  have subX : X⊆DistanceTwo G b := by
    intro z zm
    rcases mem_insert.mp zm with rfl|d4
    · exact mem_distanceTwo.mpr (by rw [dist_comm]; exact b2)
    obtain ⟨c,_,bc,cz⟩ := Q.fourth_meets_full_group hc cap conn high dx n aT full d4
    have hz := mem_shell.mp d4
    have ne : b≠z := by intro e; rw [e] at b2; omega
    have no : ¬G.Adj b z := by
      intro e
      have o := dist_eq_one_iff_adj.mpr e
      have t := hc.dist_triangle (u:=x) (v:=b) (w:=z)
      omega
    exact Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne no bc cz
  have subR : R⊆DistanceTwo G b := by
    intro z zm
    obtain ⟨zA,zn⟩ := mem_filter.mp zm
    obtain ⟨z1,zNo⟩ := mem_sdiff.mp zA
    have q := Q.adj_extra_near hc aT full z1 zNo
    have ne : b≠z := by
      intro e
      rw [e] at b2
      have o := mem_shell.mp z1
      omega
    exact Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne zn (Q.adj a aT).symm q
  have subK : K⊆DistanceTwo G b := by
    intro z zm
    obtain ⟨zT,az⟩ := mem_filter.mp zm
    have ne : b≠z := by
      intro e
      rw [e] at b2
      have h := mem_shell.mp (Q.near zT)
      omega
    have no : ¬G.Adj b z := fun e=>Q.private_rep a aT z zT az.ne.symm e.symm
    exact Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne no (Q.adj a aT).symm az
  have subF : F⊆DistanceTwo G b := by
    intro z zm
    obtain ⟨z3,notG,y,ym,yz⟩ := mem_filter.mp zm
    have by' := Q.adj_rep_of_third_group hc aT (radius_four_group_sub_third none ym) ym
    have ne : b≠z := by
      intro e
      rw [e] at b2
      have h := mem_shell.mp z3
      omega
    have no : ¬G.Adj b z := fun e=>notG (Q.third_of_rep_adj hc aT z3 e)
    exact Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne no by' yz
  have sub := union_subset (union_subset (union_subset subX subR) subK) subF
  have k := (card_le_card sub).trans (distanceTwo_le_of_even 6 b (cap b))
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨xf,rf⟩,kf⟩),
    card_union_of_disjoint (disjoint_union_left.mpr ⟨xk,rk⟩),card_union_of_disjoint xr] at k
  change X.card+R.card+K.card+F.card≤6 at k
  have xc : X.card=D.card+1 := card_insert_of_not_mem ax
  change 1+D.card+R.card+K.card+F.card≤6
  omega

theorem near_partners_full_of_spare_rep_neighbor (hc : G.Connected)
    {x a : V} (Q : RadiusFiveNearEquality G x) (aT : a∈Q.T)
    (fullOthers : ∀ b∈Q.T,b≠a → (JointFarGroup G x b).card=4)
    {z : V} (z1 : z∈Shell G x 1) (zT : z∉Q.T) (az : G.Adj (Q.rep a) z) :
    (Q.nearPartners a).card=2 := by
  have edge (b : V) (bT : b∈Q.T) (ba : b≠a) : G.Adj a b := by
    by_contra no
    exact Q.rep_no_extra_of_nonadj_to_full hc aT bT ba.symm (fullOthers b bT ba)
      (fun e=>no e.symm) z z1 zT az
  have eq : Q.nearPartners a=Q.T.erase a := by
    ext b
    constructor
    · intro h
      obtain ⟨bT,bb⟩ := mem_filter.mp h
      exact mem_erase.mpr ⟨bb.ne.symm,bT⟩
    · intro h
      obtain ⟨ba,bT⟩ := mem_erase.mp h
      exact mem_filter.mpr ⟨bT,edge b bT ba⟩
  rw [eq,card_erase_of_mem aT,Q.t3]

end RadiusFiveNearEquality

#print axioms RadiusFiveNearEquality.rep_four_part_charge
#print axioms RadiusFiveNearEquality.near_partners_full_of_spare_rep_neighbor
end Graffiti189LongestPath
