import AdjacentCutFiveSingletonGeometry189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_nonempty shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Vis vis_sub vis_card_ge_two degree_le_shore_add_one positive_cap
  from AdjacentCutFiveComponents189
open private mem_positive d2 from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp := (CutGraph (G:=G) a b).ConnectedComponent

theorem three_components_no_singleton_at_adjacent_cut (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (three : Nat.card (CutGraph (G := G) a b).ConnectedComponent = 3)
    (D : Cmp (G:=G) (a:=a) (b:=b)) : (Shore D).card ≠ 1 := by
  classical
  intro single
  have maxD := depth_le_three_of_three_and_singleton hc ab.ne even conn degree three D single
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent=3 at three
  rw [Nat.card_eq_fintype_card] at three
  let T : Finset J.ConnectedComponent := univ.erase D
  have t2 : T.card = 2 := by simp [T,three]
  obtain ⟨C,F,CF,tEq⟩ := card_eq_two.mp t2
  have CD : C≠D := (mem_erase.mp (show C∈T by simp [tEq])).1
  have FD : F≠D := (mem_erase.mp (show F∈T by simp [tEq])).1
  obtain ⟨x,dx⟩ := card_eq_one.mp single
  obtain ⟨xa,ha,ax⟩ := shore_hit_a ab.ne conn D
  obtain ⟨xb,hb,bx⟩ := shore_hit_b ab.ne conn D
  rw [dx,mem_singleton] at ha hb
  subst xa
  subst xb
  have xD : x∈Shore D := by simp [dx]
  have low : G.degree x < 5 := by
    have q := degree_le_shore_add_one D xD
    omega
  have neX {K : J.ConnectedComponent} (KD : K≠D) {z : V} (zk : z∈Shore K) : z≠x := by
    intro e
    exact disjoint_left.mp (shore_disjoint KD) zk (by simpa only [← e] using xD)
  have high {K : J.ConnectedComponent} (KD : K≠D) {z : V} (zk : z∈Shore K) : 5≤G.degree z :=
    (degree z x (neX KD zk)).resolve_right (by omega)
  have four {K : J.ConnectedComponent} (KD : K≠D) : 4 ≤ (Shore K).card := by
    obtain ⟨z,zk⟩ := shore_nonempty K
    have h := high KD zk
    have q := degree_le_shore_add_one K zk
    omega
  have Osub {K : J.ConnectedComponent} (KD : K≠D) : OddDepth K ⊆ PositiveEven G x := by
    intro z hz
    obtain ⟨zk,dn⟩ := mem_odd_depth.mp hz
    have pos := depth_pos_of_shore hc zk
    have up := maxD z
    have zx := neX KD zk
    apply mem_positive.mpr
    refine ⟨zx,?_⟩
    rw [singleton_dist_succ_depth hc D dx ax bx zx]
    have poss : depth G a b z = 1 ∨ depth G a b z = 3 := by omega
    rcases poss with p|p <;> rw [p] <;> decide
  have Odis : Disjoint (OddDepth C) (OddDepth F) :=
    (shore_disjoint CF).mono (fun _ e=>(mem_odd_depth.mp e).1) (fun _ e=>(mem_odd_depth.mp e).1)
  have Ocap : (OddDepth C).card + (OddDepth F).card ≤ 5 := by
    have sub : OddDepth C ∪ OddDepth F ⊆ PositiveEven G x := by
      intro z hz
      exact (mem_union.mp hz).elim (fun h=>Osub CD h) (fun h=>Osub FD h)
    have c := card_le_card sub
    rw [card_union_of_disjoint Odis] at c
    exact c.trans (positive_cap x even)
  have O2 {K : J.ConnectedComponent} (KD : K≠D) : 2≤(OddDepth K).card :=
    (vis_card_ge_two ab.ne conn K (by have q:=four KD; omega)).trans (card_le_card (vis_sub_odd hc K))
  have cO := O2 CD
  have fO := O2 FD
  have c3 : (OddDepth C).card≤3 := by omega
  have f3 : (OddDepth F).card≤3 := by omega
  have six {K : J.ConnectedComponent} (KD : K≠D) (o3 : (OddDepth K).card≤3) :
      6 ≤ (Shore K).card := by
    have part := shore_partition_depth K
    have q := four KD
    have ne : (NearTwo K).Nonempty := card_pos.mp (by omega)
    obtain ⟨z,zk⟩ := ne
    obtain ⟨zs,dz⟩ := mem_near_two.mp zk
    have nn := dark_neighbors_in_shore hc zs (by omega)
    have le := card_le_card nn
    rw [card_neighborFinset_eq_degree] at le
    have h := high KD zs
    have card := card_erase_add_one zs
    omega
  have c6 := six CD c3
  have f6 := six FD f3
  have cp := shore_partition_depth C
  have fp := shore_partition_depth F
  have near4 {K L : J.ConnectedComponent} (KL : K≠L) (KD : K≠D)
      (K6 : 6≤(Shore K).card) (L6 : 6≤(Shore L).card)
      (sum : (OddDepth K).card + (OddDepth L).card ≤ 5) (o3 : (OddDepth K).card≤3) :
      4≤(NearTwo K).card := by
    have p := shore_partition_depth K
    have p' := shore_partition_depth L
    by_contra! no
    have size : (Shore K).card=6 := by omega
    have e3 : (NearTwo K).card=3 := by omega
    obtain ⟨z,zn⟩ : (NearTwo K).Nonempty := card_pos.mp (by omega)
    obtain ⟨zk,z2⟩ := mem_near_two.mp zn
    obtain ⟨ca,cb⟩ := high_shore_six_dark_common hc ab conn size zk z2 (high KD zk)
    have lb := common_near_two_forbids_four_foreign hc ab even KL zk ca cb
    omega
  have c4 := near4 CF CD c6 f6 Ocap c3
  have f4 := near4 CF.symm FD f6 c6 (by omega) f3
  have common_free {K L : J.ConnectedComponent} (KL : K≠L)
      (fourL : 4≤(NearTwo L).card) {z : V} (zk : z∈Shore K) :
      ¬ (G.dist a z=2 ∧ G.dist b z=2) := by
    intro both
    have m := common_near_two_forbids_four_foreign hc ab even KL zk both.1 both.2
    omega
  have seven {K L : J.ConnectedComponent} (KL : K≠L) (KD : K≠D)
      (K6 : 6≤(Shore K).card) (K4 : 4≤(NearTwo K).card) (L4 : 4≤(NearTwo L).card) :
      7≤(Shore K).card := by
    by_contra! no
    have size : (Shore K).card = 6 := by omega
    obtain ⟨z,zn⟩ : (NearTwo K).Nonempty := card_pos.mp (by omega)
    obtain ⟨zk,z2⟩ := mem_near_two.mp zn
    exact common_free KL L4 zk (high_shore_six_dark_common hc ab conn size zk z2 (high KD zk))
  have c7 := seven CF CD c6 c4 f4
  have f7 := seven CF.symm FD f6 f4 c4
  have ep {K L : J.ConnectedComponent} (KL : K≠L)
      (K4 : 4≤(NearTwo K).card) (L4 : 4≤(NearTwo L).card) :
      ∃ w∈Shore K, (G.Adj a w ∧ ¬G.Adj b w) ∨ (G.Adj b w ∧ ¬G.Adj a w) := by
    obtain ⟨z,zn⟩ : (NearTwo K).Nonempty := card_pos.mp (by omega)
    obtain ⟨zk,z2⟩ := mem_near_two.mp zn
    have notBoth := common_free KL L4 zk
    by_cases za : G.dist a z = 2
    · obtain ⟨w,wk,e⟩ := exclusive_port_of_near_two hc zk z2 za (fun zb=>notBoth ⟨za,zb⟩)
      exact ⟨w,wk,.inl e⟩
    · have zb : G.dist b z=2 := by unfold depth at z2; omega
      obtain ⟨w,wk,e⟩ := exclusive_port_of_near_two_right hc zk z2 zb za
      exact ⟨w,wk,.inr e⟩
  obtain ⟨r,rc,er⟩ := ep CF c4 f4
  obtain ⟨s,sf,es⟩ := ep CF.symm f4 c4
  have rs : r≠s := fun h=>disjoint_left.mp (shore_disjoint CF) rc (by simpa only [← h] using sf)
  let A := PositiveEven G a ∪ PositiveEven G b
  let B := NearTwo C ∪ NearTwo F
  have charge {z : V} (za : z≠a) (zb : z≠b)
      (e : (G.Adj a z ∧ ¬G.Adj b z) ∨ (G.Adj b z ∧ ¬G.Adj a z)) : z∈A := by
    rcases e with ⟨az,nz⟩|⟨bz,nz⟩
    · have d := d2 hc zb.symm nz ab.symm az
      exact mem_union.mpr (.inr (mem_positive.mpr ⟨zb,by simp [(mem_filter.mp d).2]⟩))
    · have d := d2 hc za.symm nz ab bz
      exact mem_union.mpr (.inl (mem_positive.mpr ⟨za,by simp [(mem_filter.mp d).2]⟩))
  have rcA : r∈A := charge (fun e=>(shore_off C).1 (by simpa only [e] using rc)) (fun e=>(shore_off C).2 (by simpa only [e] using rc)) er
  have sfA : s∈A := charge (fun e=>(shore_off F).1 (by simpa only [e] using sf)) (fun e=>(shore_off F).2 (by simpa only [e] using sf)) es
  have nr : r∉B := by
    intro h
    have dd := depth_eq_one_of_port (a:=a) (b:=b) hc (fun e=>(shore_off C).1 (by simpa only [e] using rc))
      (fun e=>(shore_off C).2 (by simpa only [e] using rc)) (er.imp And.left And.left)
    have ee := (mem_union.mp h).elim (fun e => (mem_near_two.mp e).2) (fun e => (mem_near_two.mp e).2)
    omega
  have ns : s∉B := by
    intro h
    have dd := depth_eq_one_of_port (a:=a) (b:=b) hc (fun e=>(shore_off F).1 (by simpa only [e] using sf))
      (fun e=>(shore_off F).2 (by simpa only [e] using sf)) (es.imp And.left And.left)
    have ee := (mem_union.mp h).elim (fun e => (mem_near_two.mp e).2) (fun e => (mem_near_two.mp e).2)
    omega
  have sub : insert r (insert s B) ⊆ A := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact rcA
    rcases mem_insert.mp hz with rfl | hz
    · exact sfA
    obtain ⟨za,zb,dz⟩ : z≠a ∧ z≠b ∧ depth G a b z=2 := by
      rcases mem_union.mp hz with zn|zn
      · obtain ⟨zc,d⟩ := mem_near_two.mp zn
        exact ⟨fun e=>(shore_off C).1 (by simpa only [e] using zc),fun e=>(shore_off C).2 (by simpa only [e] using zc),d⟩
      · obtain ⟨zf,d⟩ := mem_near_two.mp zn
        exact ⟨fun e=>(shore_off F).1 (by simpa only [e] using zf),fun e=>(shore_off F).2 (by simpa only [e] using zf),d⟩
    have disj : G.dist a z = 2 ∨ G.dist b z = 2 := by unfold depth at dz; omega
    rcases disj with da|db
    · exact mem_union.mpr (.inl (mem_positive.mpr ⟨za,by rw [da]; decide⟩))
    · exact mem_union.mpr (.inr (mem_positive.mpr ⟨zb,by rw [db]; decide⟩))
  have dB : Disjoint (NearTwo C) (NearTwo F) :=
    (shore_disjoint CF).mono (fun _ e=>(mem_near_two.mp e).1) (fun _ e=>(mem_near_two.mp e).1)
  have cb : B.card=(NearTwo C).card+(NearTwo F).card := card_union_of_disjoint dB
  have nr' : r∉insert s B := by simp [rs,nr]
  have cnt := card_le_card sub
  rw [card_insert_of_not_mem nr',card_insert_of_not_mem ns,cb] at cnt
  have Acap : A.card≤10 := by
    have h := card_union_le (PositiveEven G a) (PositiveEven G b)
    have ea := positive_cap a even
    have eb := positive_cap b even
    dsimp [A]
    omega
  omega

#print axioms three_components_no_singleton_at_adjacent_cut
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
