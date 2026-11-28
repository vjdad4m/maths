import SixOrder24ThirdFullFamily189

namespace Graffiti189LongestPath
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem near_cover_shared_member {I X : Type*} [DecidableEq I] [DecidableEq X]
    (T : Finset I) (F : I→Finset X) (U : Finset X)
    (t3 : T.card=3) (cov : U⊆T.biUnion F) (u11 : U.card=11)
    (sub : ∀ t∈T,F t⊆U) (full : ∀ i∈T,(F i).card=4) :
    ∃ a∈T,∃ b∈T,∃ c∈T,∃ z : X,a≠b ∧ a≠c ∧ b≠c ∧
      T={a,b,c} ∧ F a∩F b={z} ∧ Disjoint (F a∪F b) (F c) := by
  classical
  have a3 : 1<T.card := by rw [t3]; decide
  obtain ⟨a,aT,b,bT,ab⟩ := one_lt_card.mp a3
  obtain ⟨c,cT,ca,cb,labels⟩ := label_three_of_mem t3 aT bT ab
  have aux {a b c : I} (aT : a∈T) (bT : b∈T) (cT : c∈T)
      (ab : a≠b) (ac : a≠c) (bc : b≠c) (labels : T={a,b,c})
      (nd : ¬Disjoint (F a) (F b)) :
      ∃ a∈T,∃ b∈T,∃ c∈T,∃ z : X,a≠b ∧ a≠c ∧ b≠c ∧
        T={a,b,c} ∧ F a∩F b={z} ∧ Disjoint (F a∪F b) (F c) := by
    obtain ⟨z,za,zb⟩ := not_disjoint_iff.mp nd
    have lo := card_le_card cov
    rw [labels,biUnion_three,u11] at lo
    have ea := card_union_add_card_inter (F a) (F b)
    have eb := card_union_add_card_inter (F a∪F b) (F c)
    rw [full a aT,full b bT] at ea
    rw [full c cT] at eb
    have pos : 1≤(F a∩F b).card := card_pos.mpr ⟨z,mem_inter.mpr ⟨za,zb⟩⟩
    have one : (F a∩F b).card=1 := by omega
    have zero : ((F a∪F b)∩F c).card=0 := by omega
    have eq : F a∩F b={z} := (eq_of_subset_of_card_le
      (singleton_subset_iff.mpr (mem_inter.mpr ⟨za,zb⟩)) (by rw [one,card_singleton])).symm
    exact ⟨a,aT,b,bT,c,cT,z,ab,ac,bc,labels,eq,
      disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp zero)⟩
  by_cases dab : Disjoint (F a) (F b)
  · by_cases dac : Disjoint (F a) (F c)
    · by_cases dbc : Disjoint (F b) (F c)
      · exfalso
        have s := card_le_card (union_subset (union_subset (sub a aT) (sub b bT)) (sub c cT))
        rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨dac,dbc⟩),
          card_union_of_disjoint dab,full a aT,full b bT,full c cT,u11] at s
        omega
      · have l : T={b,c,a} := by rw [labels]; ext v; simp only [mem_insert,mem_singleton]; tauto
        exact aux bT cT aT cb.symm ab.symm ca l dbc
    · have l : T={a,c,b} := by rw [labels]; ext v; simp only [mem_insert,mem_singleton]; tauto
      exact aux aT cT bT ca.symm ab cb l dac
  · exact aux aT bT cT ab ca.symm cb.symm labels dab

namespace RadiusFiveNearEquality

theorem zero_foreign_if_all_full_and_three_fourth
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x a : V} (dx : G.degree x≤6) (n : 24≤Fintype.card V)
    (Q : RadiusFiveNearEquality G x) (none : Shell G x 5=∅)
    (a6 : (Shell G x 1).card=6) (d3 : (Shell G x 4).card=3)
    (full : ∀ i∈Q.T,(JointFarGroup G x i).card=4) (aT : a∈Q.T) :
    (Q.foreignThird a).card=0 := by
  classical
  let R := (Shell G x 1)\Q.T
  have r3 : R.card=3 := by
    have h := card_sdiff_add_card_eq_card Q.near
    rw [Q.t3,a6] at h
    change R.card+3=6 at h
    omega
  have l := Q.rep_four_part_charge hc cap conn high dx n aT (full a aT) none
  rw [d3] at l
  have spare : ∃ z∈R,G.Adj (Q.rep a) z := by
    by_contra no
    have eq : Q.missingSpare a=R := eq_of_subset_of_card_le (filter_subset _ _)
      (card_le_card (show R⊆Q.missingSpare a from fun z zm=>
        mem_filter.mpr ⟨zm,fun e=>no ⟨z,zm,e⟩⟩))
    rw [eq,r3] at l
    omega
  obtain ⟨z,zm,za⟩ := spare
  obtain ⟨z1,zT⟩ := mem_sdiff.mp zm
  have k := Q.near_partners_full_of_spare_rep_neighbor hc aT (fun i iT _=>full i iT) z1 zT za
  omega

theorem no_order24_one_shared_third
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : 24≤Fintype.card V)
    (Q : RadiusFiveNearEquality G x) (none : Shell G x 5=∅)
    (a6 : (Shell G x 1).card=6) (c11 : (Shell G x 3).card=11) (d3 : (Shell G x 4).card=3)
    (full : ∀ i∈Q.T,(JointFarGroup G x i).card=4) : False := by
  classical
  let C := Shell G x 3
  let P (a : V) := JointFarGroup G x a
  let D := Shell G x 4
  have cCov : C⊆Q.T.biUnion P := fun z zc=>Q.far_cover (mem_union_left _ zc)
  obtain ⟨a,aT,b,bT,c,cT,s,ab,ac,bc,labels,shared,sep⟩ := near_cover_shared_member
    Q.T P C Q.t3 cCov c11 (fun _ _=>radius_four_group_sub_third none) full
  have sepA : Disjoint (P a) (P c) := sep.mono_left subset_union_left
  have sepB : Disjoint (P b) (P c) := sep.mono_left subset_union_right
  have sh : s∈P a∩P b := by rw [shared]; exact mem_singleton.mpr rfl
  obtain ⟨sa,sb⟩ := mem_inter.mp sh
  have noForeign (i : V) (iT : i∈Q.T) (u : V) (ui : u∈P i)
      (v : V) (vc : v∈C) (uv : G.Adj u v) : v∈P i := by
    have f := Q.zero_foreign_if_all_full_and_three_fourth hc cap conn high dx n none a6 d3 full iT
    by_contra bad
    have hm : v∈Q.foreignThird i := mem_filter.mpr ⟨vc,bad,u,ui,uv⟩
    exact not_mem_empty v ((card_eq_zero.mp f) ▸ hm)
  have noC (z : V) (zc : z∈C) : ¬G.Adj s z := by
    intro sz
    have both := mem_inter.mpr ⟨noForeign a aT s sa z zc sz,noForeign b bT s sb z zc sz⟩
    rw [shared,mem_singleton] at both
    exact sz.ne both.symm
  have choices (i : V) (iT : i∈Q.T) : i=a ∨ i=b ∨ i=c := by
    simpa only [labels,mem_insert,mem_singleton] using iT
  have s3 := mem_shell.mp (radius_four_group_sub_third none sa)
  have shy : G.degree s<6 := by
    have sub : G.neighborFinset s⊆insert (Q.rep a) (insert (Q.rep b) D) := by
      intro z zm
      have sz := (G.mem_neighborFinset ..).mp zm
      have o := dist_eq_one_iff_adj.mpr sz
      have t := dist_eq_one_iff_adj.mpr sz.symm
      have p := hc.dist_triangle (u:=x) (v:=s) (w:=z)
      have q := hc.dist_triangle (u:=x) (v:=z) (w:=s)
      have dep : G.dist x z=2 ∨ G.dist x z=3 ∨ G.dist x z=4 := by omega
      rcases dep with n|n|n
      · obtain ⟨i,iT,ir⟩ := Q.rep_cover z (mem_shell.mpr n)
        rcases choices i iT with rfl|rfl|rfl
        · exact mem_insert.mpr (.inl ir.symm)
        · exact mem_insert.mpr (.inr (mem_insert.mpr (.inl ir.symm)))
        · have zs := Q.third_of_rep_adj hc cT (mem_shell.mpr s3) (ir.symm ▸ sz.symm)
          exact False.elim (disjoint_left.mp sepA sa zs)
      · exact False.elim (noC z (mem_shell.mpr n) sz)
      · exact mem_insert.mpr (.inr (mem_insert.mpr (.inr (mem_shell.mpr n))))
    have l := (card_le_card sub).trans (card_insert_le (Q.rep a) (insert (Q.rep b) D))
    have r := card_insert_le (Q.rep b) D
    rw [G.card_neighborFinset_eq_degree] at l
    change D.card=3 at d3
    omega
  have away (z : V) (zs : z≠s) : 6≤G.degree z :=
    (high z s zs).resolve_right (by omega)
  have own (i : V) (iT : i∈Q.T) (z : V) (zi : z∈P i) (zs : z≠s) :
      ∀ j∈Q.T,z∈P j → i=j := by
    intro j jT zj
    have no : ¬(z∈P a ∧ z∈P b) := by
      intro bad
      have both := mem_inter.mpr bad
      rw [shared,mem_singleton] at both
      exact zs both
    rcases choices i iT with rfl|rfl|rfl <;> rcases choices j jT with rfl|rfl|rfl
    · rfl
    · exact False.elim (no ⟨zi,zj⟩)
    · exact False.elim (disjoint_left.mp sepA zi zj)
    · exact False.elim (no ⟨zj,zi⟩)
    · rfl
    · exact False.elim (disjoint_left.mp sepB zi zj)
    · exact False.elim (disjoint_left.mp sepA zj zi)
    · exact False.elim (disjoint_left.mp sepB zj zi)
    · rfl
  let Y := C\P a
  have y7 : Y.card=7 := by
    have h := card_sdiff_add_card_eq_card (show P a⊆C from radius_four_group_sub_third none)
    rw [full a aT,c11] at h
    change Y.card+4=11 at h
    omega
  have non : ((P a).erase s).card=3 := by rw [card_erase_of_mem sa, full a aT]
  obtain ⟨w,wm⟩ := card_pos.mp (show 0<((P a).erase s).card by omega)
  obtain ⟨ws,wa⟩ := mem_erase.mp wm
  have wHigh := away w ws
  have wPorts := Q.third_ports_of_no_cross hc aT wa wHigh none (own a aT w wa ws)
    (fun z zc zv wz=>zv (noForeign a aT w wa z zc wz))
  rw [full a aT] at wPorts
  have wo : w∉Y := fun h=>(mem_sdiff.mp h).2 wa
  have no (z : V) (zY : z∈Y) : ¬G.Adj w z :=
    fun wz=>(mem_sdiff.mp zY).2 (noForeign a aT w wa z (mem_sdiff.mp zY).1 wz)
  refine cross_port_overload hc cap (x:=x) Y wo y7.ge no ?_
  intro z zY
  obtain ⟨zc,zna⟩ := mem_sdiff.mp zY
  have zs : z≠s := fun e=>zna (e.symm ▸ sa)
  obtain ⟨i,iT,zi⟩ := mem_biUnion.mp (cCov zc)
  have ports := Q.third_ports_of_no_cross hc iT zi (away z zs) none (own i iT z zi zs)
    (fun v vc vz e=>vz (noForeign i iT z zi v vc e))
  rw [full i iT] at ports
  omega

end RadiusFiveNearEquality

#print axioms near_cover_shared_member
#print axioms RadiusFiveNearEquality.no_order24_one_shared_third
end Graffiti189LongestPath
