import DegreeFiveTwoTwoCommonGeometry189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset ArticulationPair
open private Shore shore_off shore_closed from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private shore_neighbor_cover from DegreeFiveDistanceTwoSingletonClose189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- A 3+3 common shore at the (2,2) contact profile has a single low
nonporter and only one point in each cut-local distance-two shell. -/
theorem low_nonporter_of_three_three_opposite_two_two
    (hc : G.Connected) (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (shared : 3≤(sharedPortSet C).card)
    (size : (Shore C).card≤(sharedPortSet C).card+3)
    (oneA : (secondShore C a).card≤1) (oneB : (secondShore C b).card≤1)
    (cA : (portColor C a).card=3) (cB : (portColor C b).card=3) :
    (Shore C).card=4 ∧ (secondShore C a).card=1 ∧ (secondShore C b).card=1 ∧
      ∃ z∈Shore C,G.dist z a=2 ∧ G.dist z b=2 ∧ G.degree z<5 := by
  classical
  let K := sharedPortSet C
  let S := Shore C
  let N := S\K
  let H := N.filter (fun z=>5≤G.degree z)
  have ka : K⊆portColor C a := fun z zm=>mem_filter.mpr ⟨(mem_filter.mp zm).1,(mem_filter.mp zm).2.1⟩
  have kb : K⊆portColor C b := fun z zm=>mem_filter.mpr ⟨(mem_filter.mp zm).1,(mem_filter.mp zm).2.2⟩
  have ks : K⊆S := filter_subset _ _
  have k3 : K.card=3 := by
    have q := card_le_card ka
    change 3≤K.card at shared
    omega
  have ea : K=portColor C a := eq_of_subset_of_card_le ka (by omega)
  have eb : K=portColor C b := eq_of_subset_of_card_le kb (by omega)
  have ns : N.card+K.card=S.card := card_sdiff_add_card_eq_card ks
  have hpart : (N\H).card+H.card=N.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have pn {z : V} (zn : z∈N) : ¬G.Adj a z ∧ ¬G.Adj b z := by
    obtain ⟨zs,zk⟩ := mem_sdiff.mp zn
    constructor
    · intro az
      apply zk
      rw [ea]
      exact mem_filter.mpr ⟨zs,az⟩
    intro bz
    apply zk
    rw [eb]
    exact mem_filter.mpr ⟨zs,bz⟩
  have sub : H⊆secondShore C a := by
    intro z zh
    obtain ⟨zn,hi⟩ := mem_filter.mp zh
    have zs := (mem_sdiff.mp zn).1
    have p := pn zn
    have hit : ∃ y∈K,G.Adj z y := by
      apply Classical.byContradiction
      intro no
      have sub : G.neighborFinset z⊆N := by
        intro t tm
        have zt := (mem_neighborFinset G _ _).mp tm
        rcases shore_closed C z zs t zt with rfl|rfl|ts
        · exact (p.1 zt.symm).elim
        · exact (p.2 zt.symm).elim
        exact mem_sdiff.mpr ⟨ts,fun tk=>no ⟨t,tk,zt⟩⟩
      have h := card_le_card sub
      rw [card_neighborFinset_eq_degree] at h
      change S.card≤K.card+3 at size
      omega
    obtain ⟨w,wk,zw⟩ := hit
    have aw := (mem_filter.mp wk).2.1
    have anz : a≠z := fun e=>(shore_off C).1 (Eq.mp (congrArg (fun v : V => v∈Shore C) e.symm) (show z∈Shore C from zs))
    exact mem_inter.mpr ⟨zs,d2 hc anz p.1 aw zw.symm⟩
  have hc1 := (card_le_card sub).trans oneA
  have low1 : (N\H).card≤1 := by
    apply Classical.byContradiction
    intro no
    have excess : 1<(N\H).card := by omega
    obtain ⟨u,ul,v,vl,uv⟩ := one_lt_card.mp excess
    have off (w : V) (wo : w∈N\H) : ¬5≤G.degree w :=
      fun h=>(mem_sdiff.mp wo).2 (mem_filter.mpr ⟨(mem_sdiff.mp wo).1,h⟩)
    exact (degree u v uv).elim (off u ul) (off v vl)
  have s5 : S.card≤5 := by omega
  have nlow (z : V) (zn : z∈N) : G.degree z<5 := by
    have p := pn zn
    have zs := (mem_sdiff.mp zn).1
    have sub : G.neighborFinset z⊆S.erase z := by
      intro t tm
      have zt := (mem_neighborFinset G _ _).mp tm
      rcases shore_closed C z zs t zt with rfl|rfl|ts
      · exact (p.1 zt.symm).elim
      · exact (p.2 zt.symm).elim
      exact mem_erase.mpr ⟨zt.ne.symm,ts⟩
    have h := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_erase_of_mem zs] at h
    omega
  have n1 : N.card≤1 := by
    apply Classical.byContradiction
    intro no
    have excess : 1<N.card := by omega
    obtain ⟨u,un,v,vn,uv⟩ := one_lt_card.mp excess
    have u4 := nlow u un
    have v4 := nlow v vn
    exact (degree u v uv).elim (fun h=>by omega) (fun h=>by omega)
  have s4 : S.card=4 := by
    apply Classical.byContradiction
    intro no
    have s3 : S.card≤3 := by omega
    obtain ⟨u,uk,v,vk,uv⟩ := one_lt_card.mp (show 1<K.card by omega)
    have low (w : V) (wk : w∈K) : G.degree w<5 := by
      have ws := ks wk
      have sub : inside G S w⊆S.erase w := by
        intro y ym
        obtain ⟨ys,wy⟩ := mem_filter.mp ym
        exact mem_erase.mpr ⟨wy.ne.symm,ys⟩
      have h := card_le_card sub
      rw [card_erase_of_mem ws] at h
      have q := card_le_card (shore_neighbor_cover C ws)
      rw [card_neighborFinset_eq_degree] at q
      change G.degree w≤(insert a (insert b (inside G S w))).card at q
      have l := card_insert_le a (insert b (inside G S w))
      have r := card_insert_le b (inside G S w)
      omega
    have hu := low u uk
    have hv := low v vk
    exact (degree u v uv).elim (fun h=>by omega) (fun h=>by omega)
  obtain ⟨z,zn⟩ := card_pos.mp (show 0<N.card by omega)
  obtain ⟨w,wk⟩ := card_pos.mp (show 0<K.card by omega)
  have zs := (mem_sdiff.mp zn).1
  have ws := ks wk
  have wz : w≠z := fun e=>(mem_sdiff.mp zn).2 (e ▸ wk)
  have zd := nlow z zn
  have w5 := (degree w z wz).resolve_right (by omega)
  have edge : G.Adj w z := by
    apply Classical.byContradiction
    intro off
    have sub : G.neighborFinset w⊆insert a (insert b ((S.erase w).erase z)) := by
      intro y ym
      have wy := (mem_neighborFinset G _ _).mp ym
      rcases shore_closed C w ws y wy with rfl|rfl|ys
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_self _ _)
      have yz : y≠z := fun e=>off (Eq.mp (congrArg (G.Adj w) e) wy)
      exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨yz,mem_erase.mpr ⟨wy.ne.symm,ys⟩⟩))
    have k := card_le_card sub
    rw [card_neighborFinset_eq_degree] at k
    have zc : z∈S.erase w := mem_erase.mpr ⟨wz.symm,zs⟩
    have ss : ((S.erase w).erase z).card=2 := by
      rw [card_erase_of_mem zc,card_erase_of_mem ws,s4]
    have l := card_insert_le a (insert b ((S.erase w).erase z))
    have r := card_insert_le b ((S.erase w).erase z)
    omega
  have p := pn zn
  have an : a≠z := fun e=>(shore_off C).1 (Eq.mp (congrArg (fun v : V => v∈Shore C) e.symm) (show z∈Shore C from zs))
  have bn : b≠z := fun e=>(shore_off C).2 (Eq.mp (congrArg (fun v : V => v∈Shore C) e.symm) (show z∈Shore C from zs))
  have aZ := d2 hc an p.1 (mem_filter.mp wk).2.1 edge
  have bZ := d2 hc bn p.2 (mem_filter.mp wk).2.2 edge
  have pa := card_pos.mpr ⟨z,show z∈secondShore C a from mem_inter.mpr ⟨zs,aZ⟩⟩
  have pb := card_pos.mpr ⟨z,show z∈secondShore C b from mem_inter.mpr ⟨zs,bZ⟩⟩
  have da := (mem_filter.mp aZ).2
  have db := (mem_filter.mp bZ).2
  exact ⟨s4,by omega,by omega,z,zs,by rwa [SimpleGraph.dist_comm],
    by rwa [SimpleGraph.dist_comm],zd⟩

#print axioms low_nonporter_of_three_three_opposite_two_two
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
