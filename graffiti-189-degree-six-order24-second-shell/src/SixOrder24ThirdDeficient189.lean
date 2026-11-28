import SixOrder24ThirdOverlap189

namespace Graffiti189LongestPath
open SimpleGraph Finset
open private mem_distanceTwo from SmallSeparator189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace RadiusFiveNearEquality

theorem deficient_selector_spare_neighbors
    (hc : G.Connected) {x k : V} (Q : RadiusFiveNearEquality G x)
    (kT : k∈Q.T) (k3 : (JointFarGroup G x k).card=3)
    (a6 : (Shell G x 1).card=6) (none : Shell G x 5=∅) :
    2≤(((Shell G x 1)\Q.T).filter (G.Adj k)).card := by
  classical
  let R := (Shell G x 1)\Q.T
  let W := R.filter (fun z=>¬G.Adj k z)
  have k1 := mem_shell.mp (Q.near kT)
  have h := Q.extra k kT W (by
    intro z zm
    obtain ⟨zr,nz⟩ := mem_filter.mp zm
    obtain ⟨z1,zt⟩ := mem_sdiff.mp zr
    have ne : k≠z := fun e=>zt (e ▸ kT)
    have kx := (dist_eq_one_iff_adj.mp k1).symm
    have xz := dist_eq_one_iff_adj.mp (mem_shell.mp z1)
    have t := Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne nz kx xz
    exact mem_nonself_even_of_distance k z ne.symm (by rw [mem_distanceTwo.mp t]; decide)) (by
      apply disjoint_left.mpr
      intro z zm zg
      have h := mem_shell.mp (mem_sdiff.mp (mem_filter.mp zm).1).1
      have r := mem_shell.mp (radius_four_group_sub_third none zg)
      omega) (by
      intro z zm a am eq
      have z1 := mem_shell.mp (mem_sdiff.mp (mem_filter.mp zm).1).1
      have zT := (mem_sdiff.mp (mem_filter.mp zm).1).2
      have aT := (mem_erase.mp am).2
      by_cases ka : G.Adj k a
      · rw [if_pos ka] at eq
        rw [eq] at z1
        have d := mem_shell.mp (Q.middle a aT)
        omega
      · rw [if_neg ka] at eq
        exact zT (eq.symm ▸ aT))
  have rs := card_sdiff_add_card_eq_card Q.near
  rw [Q.t3,a6] at rs
  change R.card+3=6 at rs
  have ar := filter_card_add_filter_neg_card_eq_card (s:=R) (G.Adj k)
  change (R.filter (G.Adj k)).card+W.card=R.card at ar
  change 2≤(R.filter (G.Adj k)).card
  omega

theorem deficient_has_active_selected_edge
    (hc : G.Connected) {x k a b : V} (Q : RadiusFiveNearEquality G x)
    (kT : k∈Q.T) (aT : a∈Q.T) (bT : b∈Q.T)
    (ka : k≠a) (kb : k≠b) (ab : a≠b) (labels : Q.T={k,a,b})
    (k3 : (JointFarGroup G x k).card=3) (none : Shell G x 5=∅)
    (a6 : (Shell G x 1).card=6)
    (uA : (Q.missingSpare a).card≤1) (uB : (Q.missingSpare b).card≤1) :
    G.Adj k a ∨ G.Adj k b := by
  classical
  by_contra no
  have na : ¬G.Adj k a := fun e=>no (Or.inl e)
  have nb : ¬G.Adj k b := fun e=>no (Or.inr e)
  let R := (Shell G x 1)\Q.T
  let A := R.filter (G.Adj k)
  have rb := card_sdiff_add_card_eq_card Q.near
  rw [Q.t3,a6] at rb
  change R.card+3=6 at rb
  have a2 : 2≤A.card := Q.deficient_selector_spare_neighbors hc kT k3 a6 none
  have touch (w : V) (wt : w∈Q.T) (kw : k≠w) (mu : (Q.missingSpare w).card≤1) :
      Q.rep w∈DistanceTwo G k := by
    let W := R.filter (G.Adj (Q.rep w))
    have h := filter_card_add_filter_neg_card_eq_card (s:=R) (G.Adj (Q.rep w))
    change W.card+(Q.missingSpare w).card=R.card at h
    have m := card_le_card (show A∪W⊆R from union_subset (filter_subset _ _) (filter_subset _ _))
    have v := card_union_add_card_inter A W
    obtain ⟨z,zm⟩ := card_pos.mp (show 0<(A∩W).card by omega)
    obtain ⟨za,zw⟩ := mem_inter.mp zm
    have ne : k≠Q.rep w := by
      intro e
      have j := mem_shell.mp (Q.near kT)
      have q := mem_shell.mp (Q.middle w wt)
      rw [e] at j
      omega
    exact Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne
      (Q.private_rep w wt k kT kw) (mem_filter.mp za).2 (mem_filter.mp zw).2.symm
  have tad := touch a aT ka uA
  have tbd := touch b bT kb uB
  have k1 := mem_shell.mp (Q.near kT)
  have repsNe : Q.rep a≠Q.rep b := fun e=>Q.private_rep b bT a aT ab (e ▸ Q.adj a aT)
  let W : Finset V := {Q.rep a,Q.rep b}
  have dep (z : V) (zm : z∈W) : z∈Shell G x 2 := by
    simp only [W,mem_insert,mem_singleton] at zm
    rcases zm with rfl|rfl
    · exact Q.middle a aT
    · exact Q.middle b bT
  have allow := Q.extra k kT W (by
    intro z zm
    have zz : z∈DistanceTwo G k := by
      simp only [W,mem_insert,mem_singleton] at zm
      rcases zm with rfl|rfl
      · exact tad
      · exact tbd
    have ne : z≠k := by
      intro e
      have d := mem_shell.mp (dep z zm)
      rw [e] at d
      omega
    exact mem_nonself_even_of_distance k z ne (by rw [mem_distanceTwo.mp zz]; decide)) (by
      apply disjoint_left.mpr
      intro z zm zg
      have q := mem_shell.mp (dep z zm)
      have r := mem_shell.mp (radius_four_group_sub_third none zg)
      omega) (by
      intro z zm i im eq
      have zi := mem_shell.mp (dep z zm)
      obtain ⟨ik,it⟩ := mem_erase.mp im
      have only : i=k ∨ i=a ∨ i=b := by simpa only [labels,mem_insert,mem_singleton] using it
      rcases only with rfl|rfl|rfl
      · exact ik rfl
      · rw [if_neg na] at eq
        rw [eq] at zi
        have d := mem_shell.mp (Q.near aT)
        omega
      · rw [if_neg nb] at eq
        rw [eq] at zi
        have d := mem_shell.mp (Q.near bT)
        omega)
  have w2 : W.card=2 := by
    change ({Q.rep a,Q.rep b}:Finset V).card=2
    rw [card_insert_of_not_mem (by simpa using repsNe),card_singleton]
  omega

theorem no_order24_one_deficient_third
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x k : V} (dx : G.degree x≤6) (n : 24≤Fintype.card V)
    (Q : RadiusFiveNearEquality G x) (none : Shell G x 5=∅)
    (a6 : (Shell G x 1).card=6) (c11 : (Shell G x 3).card=11) (d3 : (Shell G x 4).card=3)
    (kT : k∈Q.T) (deficient : (JointFarGroup G x k).card<4) : False := by
  classical
  let R := (Shell G x 1)\Q.T
  let C := Shell G x 3
  let P (a : V) := JointFarGroup G x a
  let H (a : V) := Q.foreignThird a
  let L (z : V) := thirdPorts (x:=x) G z
  have cCov : C⊆Q.T.biUnion P := fun z zc=>Q.far_cover (mem_union_left _ zc)
  obtain ⟨k3,full,sep⟩ := near_cover_deficient_members Q.T P C Q.t3 cCov
    (by rw [c11]) Q.far_card kT deficient
  have r3 : R.card=3 := by
    have h := card_sdiff_add_card_eq_card Q.near
    rw [Q.t3,a6] at h
    change R.card+3=6 at h
    omega
  have t2 : (Q.T.erase k).card=2 := by rw [card_erase_of_mem kT,Q.t3]
  obtain ⟨a,am⟩ := card_pos.mp (show 0<(Q.T.erase k).card by omega)
  obtain ⟨ak,aT⟩ := mem_erase.mp am
  obtain ⟨b,bT,bk,ba,labels⟩ := label_three_of_mem Q.t3 kT aT ak.symm
  have ar (i : V) (iT : i∈Q.T) (ik : i≠k) :
      (Q.missingSpare i).card+(Q.nearPartners i).card+(H i).card≤2 := by
    have h := Q.rep_four_part_charge hc cap conn high dx n iT (full i iT ik) none
    rw [d3] at h
    change 1+3+(Q.missingSpare i).card+(Q.nearPartners i).card+(H i).card≤6 at h
    omega
  have spare (i : V) (iT : i∈Q.T) (ik : i≠k) : ∃ z∈R,G.Adj (Q.rep i) z := by
    by_contra no
    have eq : Q.missingSpare i=R := eq_of_subset_of_card_le (filter_subset _ _)
      (card_le_card (show R⊆Q.missingSpare i from fun z zm=>
        mem_filter.mpr ⟨zm,fun e=>no ⟨z,zm,e⟩⟩))
    have h := ar i iT ik
    rw [eq,r3] at h
    omega
  obtain ⟨z,zm,za⟩ := spare a aT ak
  obtain ⟨z1,zT⟩ := mem_sdiff.mp zm
  have ab : G.Adj a b := by
    by_contra no
    exact Q.rep_no_extra_of_nonadj_to_full hc aT bT ba.symm (full b bT bk)
      (fun e=>no e.symm) z z1 zT za
  have nearOne {i j : V} (jT : j∈Q.T) (e : G.Adj i j) :
      1≤(Q.nearPartners i).card := card_pos.mpr ⟨j,mem_filter.mpr ⟨jT,e⟩⟩
  have missA : (Q.missingSpare a).card≤1 := by
    have h := ar a aT ak
    have j := nearOne bT ab
    omega
  have missB : (Q.missingSpare b).card≤1 := by
    have h := ar b bT bk
    have j := nearOne aT ab.symm
    omega
  have own (i : V) (iT : i∈Q.T) (z : V) (zi : z∈P i) :
      ∀ j∈Q.T,z∈P j → i=j := by
    intro j jt zj
    by_contra h
    exact disjoint_left.mp (sep i iT j jt h) zi zj
  have finish {a b : V} (aT : a∈Q.T) (bT : b∈Q.T) (ak : a≠k) (bk : b≠k)
      (_abN : a≠b) (labels : Q.T={k,a,b}) (ab : G.Adj a b) (ka : G.Adj k a) : False := by
    have two : 2≤(Q.nearPartners a).card := by
      have sub : ({k,b}:Finset V)⊆Q.nearPartners a :=
        insert_subset_iff.mpr ⟨mem_filter.mpr ⟨kT,ka.symm⟩,
          singleton_subset_iff.mpr (mem_filter.mpr ⟨bT,ab⟩)⟩
      have h := card_le_card sub
      rwa [card_insert_of_not_mem (by simpa using bk.symm),card_singleton] at h
    have ah := ar a aT ak
    have bh := ar b bT bk
    have one := nearOne aT ab.symm
    have a0 : (H a).card=0 := by omega
    have b1 : (H b).card≤1 := by omega
    let U := P k\H b
    have u2 : 2≤U.card := by
      have g := card_sdiff_add_card_eq_card (show P k∩H b⊆P k from inter_subset_left)
      have h := card_le_card (show P k∩H b⊆H b from inter_subset_right)
      have eq : P k\(P k∩H b)=U := by
        ext j
        simp [U]
      rw [eq,k3] at g
      omega
    obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp (show 1<U.card by omega)
    obtain ⟨y,yu,yh⟩ : ∃ y∈U,6≤G.degree y :=
      (high u v uv).elim (fun e=>⟨u,um,e⟩) (fun e=>⟨v,vm,e⟩)
    obtain ⟨yk,yn⟩ := mem_sdiff.mp yu
    have no (z : V) (zc : z∈C) (zk : z∉P k) : ¬G.Adj y z := by
      intro yz
      obtain ⟨j,jT,zj⟩ := mem_biUnion.mp (cCov zc)
      have cls : j=k ∨ j=a ∨ j=b := by simpa only [labels,mem_insert,mem_singleton] using jT
      rcases cls with e|e|e
      · exact zk (e ▸ zj)
      · subst j
        have n : y∉P a := fun e=>ak ((own k kT y yk a aT e).symm)
        have m : y∈H a := mem_filter.mpr ⟨radius_four_group_sub_third none yk,n,z,zj,yz.symm⟩
        exact not_mem_empty y ((card_eq_zero.mp a0) ▸ m)
      · subst j
        have n : y∉P b := fun e=>bk ((own k kT y yk b bT e).symm)
        exact yn (mem_filter.mpr ⟨radius_four_group_sub_third none yk,n,z,zj,yz.symm⟩)
    have yPorts := Q.third_ports_of_no_cross hc kT yk yh none (own k kT y yk) no
    rw [k3] at yPorts
    change 6≤3+(L y).card at yPorts
    let S := C\P k
    let F := S.filter (fun z=>6≤G.degree z)
    have s8 : S.card=8 := by
      have s := card_sdiff_add_card_eq_card (show P k⊆C from radius_four_group_sub_third none)
      rw [k3,c11] at s
      change S.card+3=11 at s
      omega
    have low : (S\F).card≤1 := by
      by_contra h
      have over : 1<(S\F).card := by omega
      obtain ⟨i,im,j,jm,ij⟩ := one_lt_card.mp over
      obtain ⟨iS,iF⟩ := mem_sdiff.mp im
      obtain ⟨jS,jF⟩ := mem_sdiff.mp jm
      exact (high i j ij).elim (fun e=>iF (mem_filter.mpr ⟨iS,e⟩))
        (fun e=>jF (mem_filter.mpr ⟨jS,e⟩))
    have f7 : 7≤F.card := by
      have h := card_sdiff_add_card_eq_card (show F⊆S from filter_subset _ _)
      omega
    have yOut : y∉F := fun m=>(mem_sdiff.mp (mem_filter.mp m).1).2 yk
    have yno (z : V) (zm : z∈F) : ¬G.Adj y z := by
      obtain ⟨zc,zk⟩ := mem_sdiff.mp (mem_filter.mp zm).1
      exact no z zc zk
    refine cross_port_overload hc cap (x:=x) F yOut f7 yno ?_
    intro z zm
    obtain ⟨zS,zh⟩ := mem_filter.mp zm
    obtain ⟨zc,zk⟩ := mem_sdiff.mp zS
    obtain ⟨j,jT,zj⟩ := mem_biUnion.mp (cCov zc)
    have jk : j≠k := fun e=>zk (e ▸ zj)
    have nm := Q.third_degree_bound_of_unique_group hc jT zj none (own j jT z zj)
    rw [full j jT jk] at nm
    have cls : j=k ∨ j=a ∨ j=b := by simpa only [labels,mem_insert,mem_singleton] using jT
    have l : (H j).card≤1 := by
      rcases cls with h|h|h
      · exact False.elim (jk h)
      · rw [h]
        omega
      · rw [h]
        exact b1
    change G.degree z≤4+(H j).card+(L z).card at nm
    change (L y).card+(L z).card>(Shell G x 4).card
    omega
  rcases Q.deficient_has_active_selected_edge hc kT aT bT ak.symm bk.symm ba.symm labels k3
    none a6 missA missB with ka|kb
  · exact finish aT bT ak bk ba.symm labels ab ka
  · have ll : Q.T={k,b,a} := by rw [labels]; ext i; simp only [mem_insert,mem_singleton]; tauto
    exact finish bT aT bk ak ba ll ab.symm kb

end RadiusFiveNearEquality

#print axioms RadiusFiveNearEquality.no_order24_one_deficient_third
end Graffiti189LongestPath
