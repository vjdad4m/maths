import AdjacentCutFiveFifteenSingletonMixedCore189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint from AdjacentCutFiveActual189
open private key classSet key_facts from AdjacentCutFiveTopProfiles189
open private not_both_b_ports_adjacent_common b_port_selected_by_common_misses_b_even
  b_ports_no_edge_of_four_even_exhausted adj_forbidden_by_dist from AdjacentCutFiveFifteenSingletonMixedCore189
open private right_even_has_actual_b_port all_common_of_adjacent_singleton_profile_two
  separator_of_only_one_actual_b_at_mixed_profile from AdjacentCutFiveFifteenSingletonMixed189
open private even_two_three_info restrict_unique_profile from AdjacentCutFiveSixteenSingletonGeometry189
open private left_even_adjoins_exclusive from AdjacentCutFiveSixteenSingletonDepth189
open private d2 from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem degree_at_most_four_from_choices {v a b c d : V}
    (h : ∀ w, G.Adj v w → w=a ∨ w=b ∨ w=c ∨ w=d) : G.degree v≤4 := by
  classical
  have sub : G.neighborFinset v⊆{a,b,c,d} := by
    intro w wm
    rcases h w ((G.mem_neighborFinset v w).mp wm) with rfl|rfl|rfl|rfl <;> simp
  have lt := card_le_card sub
  rw [card_neighborFinset_eq_degree] at lt
  have c₁ := card_insert_le a ({b,c,d}:Finset V)
  have c₂ := card_insert_le b ({c,d}:Finset V)
  have c₃ := card_insert_le c ({d}:Finset V)
  rw [card_singleton] at c₃
  omega

private theorem impossibility_of_two_actual_b_at_mixed_profile
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ w,(EvenFrom G w).card≤6)
    {C D : Cmp G a b} (CD : C≠D) {s : V} (sc : s∈Shore C) (as' : G.Adj a s) (bs' : G.Adj b s)
    {x y z c d : V} (xd : x∈Shore D) (yd : y∈Shore D) (zd : z∈Shore D) (cd : c∈Shore D)
    (ax : G.Adj a x) (nx : ¬G.Adj b x)
    (by' : G.Adj b y) (ny : ¬G.Adj a y) (bz : G.Adj b z) (nz : ¬G.Adj a z)
    (ac : G.Adj a c) (bc : G.Adj b c)
    (three : (classSet D 0).card=3) (four : (classSet D 1).card=4)
    (dA : ∀ w∈classSet D 0,G.dist a w=2 ∧ G.dist b w=3)
    (dB : ∀ w∈classSet D 1,G.dist a w=3 ∧ G.dist b w=2)
    (xAll : ∀ w∈classSet D 0,G.Adj x w)
    (LA : classSet D 3={x}) (RB : classSet D 4={y,z}) (OC : classSet D 5={c,d})
    (zer : (classSet D 2).card=0)
    (high : ∀ v∈Shore D,5≤G.degree v) : False := by
  classical
  have exhaust {w : V} (wd : w∈Shore D) :
      w∈classSet D 0 ∨ w∈classSet D 1 ∨ w=x ∨ w=y ∨ w=z ∨ w=c ∨ w=d := by
    rcases (by decide : ∀ i : Fin 6,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5) (key G a b w) with i|i|i|i|i|i
    · exact .inl (mem_filter.mpr ⟨wd,i⟩)
    · exact .inr (.inl (mem_filter.mpr ⟨wd,i⟩))
    · have e := card_pos.mpr (show (classSet D 2).Nonempty from ⟨w,mem_filter.mpr ⟨wd,i⟩⟩)
      omega
    · have h : w∈classSet D 3 := mem_filter.mpr ⟨wd,i⟩
      exact .inr (.inr (.inl (by simpa [LA] using h)))
    · have h : w∈classSet D 4 := mem_filter.mpr ⟨wd,i⟩
      have j : w=y ∨ w=z := by simpa [RB] using h
      exact j.elim (fun e=>.inr (.inr (.inr (.inl e)))) (fun e=>.inr (.inr (.inr (.inr (.inl e)))))
    · have h : w∈classSet D 5 := mem_filter.mpr ⟨wd,i⟩
      have j : w=c ∨ w=d := by simpa [OC] using h
      exact .inr (.inr (.inr (.inr (.inr j))))
  have cover : ∀ w∈classSet D 1,G.Adj y w ∨ G.Adj z w := by
    intro w wm
    obtain ⟨t,tm,_,_,tw⟩ := right_even_has_actual_b_port hc ab (mem_filter.mp wm).1 (dB w wm).1 (dB w wm).2
    have j : t=y ∨ t=z := by simpa [RB] using tm
    rcases j with rfl|rfl
    · exact .inl tw
    · exact .inr tw
  have cpos := high c cd
  have choices : ∀ w,G.Adj c w → w=a ∨ w=b ∨ w=x ∨ w=y ∨ w=z ∨ w=d := by
    intro w cw
    rcases shore_closed D _ cd _ cw with q|q|wd
    · exact .inl q
    · exact .inr (.inl q)
    rcases exhaust wd with m|m|q|q|q|q|q
    · have f : G.dist b c+1<G.dist b w := by rw [dist_eq_one_iff_adj.mpr bc,(dA w m).2]; decide
      exact (adj_forbidden_by_dist hc f cw).elim
    · have f : G.dist a c+1<G.dist a w := by rw [dist_eq_one_iff_adj.mpr ac,(dB w m).1]; decide
      exact (adj_forbidden_by_dist hc f cw).elim
    · exact .inr (.inr (.inl q))
    · exact .inr (.inr (.inr (.inl q)))
    · exact .inr (.inr (.inr (.inr (.inl q))))
    · exact (cw.ne q.symm).elim
    · exact .inr (.inr (.inr (.inr (.inr q))))
  have excl : ¬(G.Adj c y ∧ G.Adj c z) := fun h=>
    not_both_b_ports_adjacent_common hc ab even CD sc as' cd xd ac bc ax nx three four dA dB xAll cover h.1 h.2
  have cx : G.Adj c x := by
    by_contra no
    by_cases yy : G.Adj c y
    · have zz : ¬G.Adj c z := fun h=>excl ⟨yy,h⟩
      have small : G.degree c≤4 := degree_at_most_four_from_choices (a:=a) (b:=b) (c:=y) (d:=d) (by
        intro w cw
        rcases choices w cw with rfl|rfl|rfl|rfl|rfl|rfl
        · exact .inl rfl
        · exact .inr (.inl rfl)
        · exact (no cw).elim
        · exact .inr (.inr (.inl rfl))
        · exact (zz cw).elim
        · exact .inr (.inr (.inr rfl)))
      omega
    · have small : G.degree c≤4 := degree_at_most_four_from_choices (a:=a) (b:=b) (c:=z) (d:=d) (by
        intro w cw
        rcases choices w cw with rfl|rfl|rfl|rfl|rfl|rfl
        · exact .inl rfl
        · exact .inr (.inl rfl)
        · exact (no cw).elim
        · exact (yy cw).elim
        · exact .inr (.inr (.inl rfl))
        · exact .inr (.inr (.inr rfl)))
      omega
  have cyz : G.Adj c y ∨ G.Adj c z := by
    by_contra no
    have small : G.degree c≤4 := degree_at_most_four_from_choices (a:=a) (b:=b) (c:=x) (d:=d) (by
      intro w cw
      rcases choices w cw with rfl|rfl|rfl|rfl|rfl|rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl rfl))
      · exact (no (.inl cw)).elim
      · exact (no (.inr cw)).elim
      · exact .inr (.inr (.inr rfl)))
    omega
  have contradiction {p q : V}
      (pd : p∈Shore D) (qd : q∈Shore D) (bp : G.Adj b p) (np : ¬G.Adj a p)
      (bq : G.Adj b q) (nq : ¬G.Adj a q)
      (portCover : ∀ w∈classSet D 1,G.Adj p w ∨ G.Adj q w)
      (r : ∀ w, w=y ∨ w=z → w=p ∨ w=q)
      (cp : G.Adj c p) (cq : ¬G.Adj c q) : False := by
    have miss := b_port_selected_by_common_misses_b_even hc even CD sc as' cd qd ac bc bq nq three dA dB xAll cx cp cq
    have allQ : ∀ w∈classSet D 1,G.Adj q w := fun w wm=>(portCover w wm).resolve_left (miss w wm)
    have pq := b_ports_no_edge_of_four_even_exhausted hc ab even CD sc bs' pd bp np four (fun w wm=>(dB w wm).2) miss allQ
    have small : G.degree p≤4 := degree_at_most_four_from_choices (a:=b) (b:=x) (c:=c) (d:=d) (by
      intro w pw
      have inB (h : w=y ∨ w=z) : False := by
        rcases r w h with rfl|rfl
        · exact (G.loopless _ pw)
        · exact pq pw
      rcases shore_closed D _ pd _ pw with rfl|rfl|wd
      · exact (np pw.symm).elim
      · exact .inl rfl
      rcases exhaust wd with m|m|e|e|e|e|e
      · have f : G.dist b p+1<G.dist b w := by rw [dist_eq_one_iff_adj.mpr bp,(dA w m).2]; decide
        exact (adj_forbidden_by_dist hc f pw).elim
      · exact (miss w m pw).elim
      · exact .inr (.inl e)
      · exact (inB (.inl e)).elim
      · exact (inB (.inr e)).elim
      · exact .inr (.inr (.inl e))
      · exact .inr (.inr (.inr e)))
    have h := high p pd
    omega
  rcases cyz with cy|cz
  · exact contradiction yd zd by' ny bz nz cover (fun _ h=>h) cy (fun cz=>excl ⟨cy,cz⟩)
  · exact contradiction zd yd bz nz by' ny (fun w h=>(cover w h).symm) (fun _ h=>h.symm) cz (fun cy=>excl ⟨cy,cz⟩)

#print axioms impossibility_of_two_actual_b_at_mixed_profile

theorem nonadjacent_separator_of_mixed_singleton_twelve_profile
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ w,(EvenFrom G w).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (CD : C≠D)
    (shoreCover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    {s : V} (sc : s∈Shore C) (single : Shore C={s}) (as' : G.Adj a s) (bs' : G.Adj b s)
    (three : (classSet D 0).card=3) (four : (classSet D 1).card=4)
    (zer : (classSet D 2).card=0) (oa : (classSet D 3).card=1)
    (ob : (classSet D 4).card=2) (oc : (classSet D 5).card=2) :
    ∃ u v : V,u≠v ∧ ¬G.Adj u v ∧ ¬(G.induce {z : V | z≠u ∧ z≠v}).Connected := by
  classical
  have dA : ∀ w∈classSet D 0,G.dist a w=2 ∧ G.dist b w=3 :=
    fun _ m=> even_two_three_info hc ab oa m
  have dB : ∀ w∈classSet D 1,G.dist a w=3 ∧ G.dist b w=2 := by
    intro w wm
    obtain ⟨wd,k⟩ := mem_filter.mp wm
    have h := right_even_depth_two_of_adjacent_singleton_twelve_profile hc ab degree CD single
      (by omega) four zer oa ob wd k
    obtain ⟨u,v,_⟩ := key_facts hc ab w
    rw [k] at u v
    change G.dist a w=depth G a b w+1 at u
    change G.dist b w=depth G a b w+0 at v
    exact ⟨by omega,h⟩
  obtain ⟨e,em⟩ := card_pos.mp (show 0<(classSet D 0).card by omega)
  have ed := (mem_filter.mp em).1
  have ee := dA e em
  obtain ⟨x,xd,ax,nx⟩ := exclusive_left_port_of_strictly_nearer hc ed (by omega)
  have xB : x≠b := fun eq=>(shore_off D).2 (eq ▸ xd)
  have xk : key G a b x=3 := by
    have dx := (mem_filter.mp (d2 hc xB.symm nx ab.symm ax)).2
    simp [key,dist_eq_one_iff_adj.mpr ax,dx]
  have LA := restrict_unique_profile oa xd xk
  have xAll : ∀ w∈classSet D 0,G.Adj x w := by
    intro w wm
    have wd := dA w wm
    exact left_even_adjoins_exclusive hc ab LA (mem_filter.mp wm).1 wd.1 wd.2
  obtain ⟨e,em⟩ := card_pos.mp (show 0<(classSet D 1).card by omega)
  have ee := dB e em
  obtain ⟨y,ym,by',ny,_⟩ := right_even_has_actual_b_port hc ab (mem_filter.mp em).1 ee.1 ee.2
  have yd := (mem_filter.mp ym).1
  by_cases no : ∀ z∈classSet D 4,G.Adj b z → z=y
  · exact separator_of_only_one_actual_b_at_mixed_profile hc ab even CD sc as' zer four xd yd ax nx by' ny LA no dB
  · push_neg at no
    obtain ⟨z,zm,bz,zy⟩ := no
    have zd := (mem_filter.mp zm).1
    have nz : ¬G.Adj a z := by
      intro az
      have da := dist_eq_one_iff_adj.mpr az
      have db := dist_eq_one_iff_adj.mpr bz
      have k := (mem_filter.mp zm).2
      rw [show key G a b z=5 by simp [key,da,db]] at k
      exact (by decide : (5:Fin 6)≠4) k
    have sub : ({y,z}:Finset V)⊆classSet D 4 := by
      intro w wm
      have h : w=y ∨ w=z := by simpa using wm
      rcases h with rfl|rfl
      · exact ym
      · exact zm
    have RB := (eq_of_subset_of_card_le sub (by simp [ob,zy.symm])).symm
    obtain ⟨c,d,_,OC⟩ := card_eq_two.mp oc
    have cm : c∈classSet D 5 := by simp [OC]
    have cd := (mem_filter.mp cm).1
    have terminal := adjacent_singleton_terminal_count ab degree CD shoreCover (show (Shore C).card=1 by simp [single])
    have cc := all_common_of_adjacent_singleton_profile_two hc ab terminal.1 oa oc c cm
    exact (impossibility_of_two_actual_b_at_mixed_profile hc ab even CD sc as' bs' xd yd zd cd ax nx by' ny bz nz cc.1 cc.2
      three four dA dB xAll LA RB OC zer terminal.2.2).elim

#print axioms nonadjacent_separator_of_mixed_singleton_twelve_profile
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
