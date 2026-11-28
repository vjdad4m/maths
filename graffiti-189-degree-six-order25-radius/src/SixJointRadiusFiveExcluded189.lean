import SixJointEqualityGeometry189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic mem_distanceTwo from SmallSeparator189
open private order_sum_odd_shells_of_radius_six from SixThreeRadiusFive189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

namespace RadiusFiveEquality

theorem adj_extra_near
    (hc : G.Connected) {x : V} (Q : RadiusFiveEquality G x)
    {a z : V} (aT : a∈Q.T) (z1 : z∈Shell G x 1) (zT : z∉Q.T) :
    G.Adj a z := by
  by_contra nz
  have ne : a≠z := fun e=>zT (e ▸ aT)
  have ax := (dist_eq_one_iff_adj.mp (mem_shell.mp (Q.near aT))).symm
  have xz := dist_eq_one_iff_adj.mp (mem_shell.mp z1)
  have zd := Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc ne nz ax xz
  have ze := mem_nonself_even_of_distance (G:=G) a z ne.symm (by rw [mem_distanceTwo.mp zd]; decide)
  rcases Q.saturated a aT z ze with zf|⟨b,bm,eq⟩
  · rcases mem_union.mp zf with h|h
    · have v := mem_shell.mp (mem_inter.mp h).1
      have j := mem_shell.mp z1
      omega
    · have v := mem_shell.mp (mem_inter.mp h).1
      have j := mem_shell.mp z1
      omega
  · have bt := (mem_erase.mp bm).2
    by_cases ab : G.Adj a b
    · rw [if_pos ab] at eq
      have v := mem_shell.mp (Q.middle b bt)
      rw [←eq] at v
      have j := mem_shell.mp z1
      omega
    · rw [if_neg ab] at eq
      exact zT (eq.symm ▸ bt)

theorem no_rep_at_distance_two_if_nonadj
    (_hc : G.Connected) {x : V} (Q : RadiusFiveEquality G x)
    {a b : V} (aT : a∈Q.T) (bT : b∈Q.T) (no : ¬G.Adj b a) :
    Q.rep a∉DistanceTwo G b := by
  intro md
  have rep2 := mem_shell.mp (Q.middle a aT)
  have b1 := mem_shell.mp (Q.near bT)
  have ne : Q.rep a≠b := by intro e; rw [e] at rep2; omega
  have ee := mem_nonself_even_of_distance (G:=G) b (Q.rep a) ne
    (by rw [mem_distanceTwo.mp md]; decide)
  rcases Q.saturated b bT (Q.rep a) ee with zf|⟨j,jm,eq⟩
  · rcases mem_union.mp zf with h|h
    · have v := mem_shell.mp (mem_inter.mp h).1
      omega
    · have v := mem_shell.mp (mem_inter.mp h).1
      omega
  · have jt := (mem_erase.mp jm).2
    by_cases bj : G.Adj b j
    · rw [if_pos bj] at eq
      by_cases aj : a=j
      · exact no (aj.symm ▸ bj)
      exact Q.private_rep j jt a aT aj (eq ▸ Q.adj a aT)
    · rw [if_neg bj] at eq
      have v := mem_shell.mp (Q.near jt)
      rw [←eq] at v
      omega

theorem two_low_of_fifth_nonempty
    (hc : G.Connected) {x : V} (dx : G.degree x≤6)
    (Q : RadiusFiveEquality G x) {e : V} (e5 : e∈Shell G x 5) :
    ∃ a b : V, a≠b ∧ G.degree a<6 ∧ G.degree b<6 := by
  classical
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x e
  have len : p.length=5 := hp.trans (mem_shell.mp e5)
  let b := p.getVert 2
  let c := p.getVert 3
  let d := p.getVert 4
  have b2 : b∈Shell G x 2 := mem_shell.mpr (distance_on_geodesic hc p hp 2 (by omega))
  have c3 : c∈Shell G x 3 := mem_shell.mpr (distance_on_geodesic hc p hp 3 (by omega))
  have d4 : d∈Shell G x 4 := mem_shell.mpr (distance_on_geodesic hc p hp 4 (by omega))
  have bc : G.Adj b c := p.adj_getVert_succ (i:=2) (by omega)
  have cd : G.Adj c d := p.adj_getVert_succ (i:=3) (by omega)
  have de : G.Adj d e := by
    have s := p.adj_getVert_succ (i:=4) (by omega)
    have t : p.getVert 5=e := by rw [←len,getVert_length]
    simpa only [t] using s
  obtain ⟨a,aT,ar⟩ := Q.rep_cover b b2
  have a1 := mem_shell.mp (Q.near aT)
  have b2' := mem_shell.mp b2
  have d4' := mem_shell.mp d4
  have ax : a≠b := by intro eq; rw [eq] at a1; omega
  have ab : G.Adj a b := ar ▸ Q.adj a aT
  have bcd : G.dist b d≤2 := by
    have c1 := dist_eq_one_iff_adj.mpr bc
    have d1 := dist_eq_one_iff_adj.mpr cd
    have t := hc.dist_triangle (u:=b) (v:=c) (w:=d)
    omega
  have ad : G.dist a d≤3 := by
    have d1 := dist_eq_one_iff_adj.mpr ab
    have t := hc.dist_triangle (u:=a) (v:=b) (w:=d)
    omega
  have far (z : V) (zt : z∈Q.T) (za : z≠a) : 5≤G.dist z d :=
    Q.dist_fifth_support_of_different_selection hc e5 d4 c3 cd de aT zt za.symm (ar.symm ▸ bc)
  have avoidA (z : V) (zt : z∈Q.T) (za : z≠a) : ¬G.Adj a z := by
    intro az
    have o := dist_eq_one_iff_adj.mpr az.symm
    have t := hc.dist_triangle (u:=z) (v:=a) (w:=d)
    have f := far z zt za
    omega
  have avoidB (z : V) (zt : z∈Q.T) (za : z≠a) : ¬G.Adj b (Q.rep z) := by
    intro bz
    have o := dist_eq_one_iff_adj.mpr bz.symm
    have zz := dist_eq_one_iff_adj.mpr (Q.adj z zt)
    have t := hc.dist_triangle (u:=z) (v:=Q.rep z) (w:=d)
    have u := hc.dist_triangle (u:=Q.rep z) (v:=b) (w:=d)
    have f := far z zt za
    omega
  let A := Shell G x 1
  have a6 : A.card≤6 := by
    have eq : A=G.neighborFinset x := by
      ext z
      change z∈Shell G x 1 ↔ _
      rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
    rw [eq,G.card_neighborFinset_eq_degree]
    exact dx
  have an : (A\Q.T).card≤3 := by
    have w := card_sdiff_add_card_eq_card (show Q.T⊆A from Q.near)
    rw [Q.t3] at w
    omega
  have aLow : G.degree a<6 := by
    have sub : G.neighborFinset a⊆insert x (insert b (A\Q.T)) := by
      intro z zm
      have az := (G.mem_neighborFinset ..).mp zm
      have o := dist_eq_one_iff_adj.mpr az
      have d := hc.dist_triangle (u:=x) (v:=a) (w:=z)
      have cases : G.dist x z=0 ∨ G.dist x z=1 ∨ G.dist x z=2 := by omega
      rcases cases with h|h|h
      · exact mem_insert.mpr (.inl ((hc.dist_eq_zero_iff.mp h).symm))
      · have zt : z∉Q.T := fun zt=>avoidA z zt az.ne.symm az
        exact mem_insert.mpr (.inr (mem_insert.mpr (.inr (mem_sdiff.mpr ⟨mem_shell.mpr h,zt⟩))))
      · obtain ⟨j,jt,je⟩ := Q.rep_cover z (mem_shell.mpr h)
        have aj : a=j := by
          by_contra ne
          exact Q.private_rep j jt a aT ne (je.symm ▸ az)
        subst j
        exact mem_insert.mpr (.inr (mem_insert.mpr (.inl (je.symm.trans ar))))
    have l := (card_le_card sub).trans (card_insert_le x (insert b (A\Q.T)))
    have k := card_insert_le b (A\Q.T)
    rw [G.card_neighborFinset_eq_degree] at l
    omega
  have bLow : G.degree b<6 := by
    have te : (Q.T.erase a).card=2 := by rw [card_erase_of_mem aT,Q.t3]
    obtain ⟨j,jm⟩ := card_pos.mp (show 0<(Q.T.erase a).card by omega)
    obtain ⟨ja,jt⟩ := mem_erase.mp jm
    have noAj := avoidA j jt ja
    have sub : G.neighborFinset b⊆insert a (JointFarGroup G x a) := by
      intro z zm
      have bz := (G.mem_neighborFinset ..).mp zm
      have o := dist_eq_one_iff_adj.mpr bz
      have o' := dist_eq_one_iff_adj.mpr bz.symm
      have d := hc.dist_triangle (u:=x) (v:=b) (w:=z)
      have d' := hc.dist_triangle (u:=x) (v:=z) (w:=b)
      have cases : G.dist x z=1 ∨ G.dist x z=2 ∨ G.dist x z=3 := by omega
      rcases cases with h|h|h
      · by_cases za : z=a
        · exact mem_insert.mpr (.inl za)
        have zt : z∉Q.T := fun zt=>Q.private_rep a aT z zt za (ar.symm ▸ bz.symm)
        have jz := Q.adj_extra_near hc jt (mem_shell.mpr h) zt
        have njb : ¬G.Adj j b := fun e=>Q.private_rep a aT j jt ja (ar.symm ▸ e)
        have jne : j≠b := by
          intro e
          have d := mem_shell.mp (Q.near jt)
          rw [e] at d
          omega
        have jb2 := Graffiti189LongestPath.ThresholdSix.ThreeCut.two_of_common hc jne njb jz bz.symm
        exact False.elim (Q.no_rep_at_distance_two_if_nonadj hc aT jt (fun e=>noAj e.symm)
          (ar.symm ▸ jb2))
      · obtain ⟨k,kt,kr⟩ := Q.rep_cover z (mem_shell.mpr h)
        by_cases ka : k=a
        · subst k
          exact False.elim (bz.ne (ar.symm.trans kr))
        exact False.elim (avoidB k kt ka (kr.symm ▸ bz))
      · exact mem_insert.mpr (.inr (Q.third_of_rep_adj hc aT (mem_shell.mpr h) (ar.symm ▸ bz)))
    have l := (card_le_card sub).trans (card_insert_le a (JointFarGroup G x a))
    rw [G.card_neighborFinset_eq_degree,Q.far_card a aT] at l
    omega
  exact ⟨a,b,ax,aLow,bLow⟩

end RadiusFiveEquality

theorem no_order25_radius_five_at_degree_six
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : Fintype.card V=25)
    {e : V} (e5 : e∈Shell G x 5) : False := by
  have far := mem_shell.mp e5
  have b := shell_card_of_far hc 3 conn (x:=x) (y:=e) (i:=2) (by decide) (by omega)
  have d := shell_card_of_far hc 3 conn (x:=x) (y:=e) (i:=4) (by decide) (by omega)
  have es := shell_two_four_le_of_even (cap x)
  have b3 : (Shell G x 2).card=3 := by omega
  have rad := diameter_bound_from_inner_even_layers hc 6 3 2 cap conn (by decide)
  have s := order_sum_odd_shells_of_radius_six cap x dx (rad x)
  have j := third_and_fifth_shells_le_twelve_at_degree_six hc cap x dx
  obtain ⟨Q⟩ := radius_five_equality hc cap x dx b3 (by omega)
  obtain ⟨a,b,ab,al,bl⟩ := Q.two_low_of_fifth_nonempty hc dx e5
  exact (high a b ab).elim (fun a=>Nat.not_le_of_gt al a) (fun b=>Nat.not_le_of_gt bl b)

theorem eccentricity_le_four_at_order25_degree_six
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : Fintype.card V=25) :
    ∀ y,G.dist x y≤4 := by
  intro y
  by_contra! far
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  have d := distance_on_geodesic hc p hp 5 (by omega)
  exact no_order25_radius_five_at_degree_six hc cap conn high dx n
    (mem_shell.mpr d)

#print axioms RadiusFiveEquality.two_low_of_fifth_nonempty
#print axioms no_order25_radius_five_at_degree_six
#print axioms eccentricity_le_four_at_order25_degree_six
end Graffiti189LongestPath
