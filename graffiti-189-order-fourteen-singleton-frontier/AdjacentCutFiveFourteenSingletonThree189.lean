import AdjacentCutFiveSixteenSingletonGeometry189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_connected shore_disjoint from AdjacentCutFiveActual189
open private foreign_pos_even positive_cap from AdjacentCutFiveComponents189
open private key classSet prof sa sb pa key_facts from AdjacentCutFiveTopProfiles189
open private key_a_port key_b_port from AdjacentCutFiveTopFlatten189
open private mem_positive d2 from AdjacentCutFiveBound189
open private compact_graph_singleton_profile left_even_depth_two_with_one_exclusive
  right_even_depth_two_with_one_exclusive left_even_adjoins_exclusive right_even_adjoins_exclusive
  predecessor_of_positive_dist depth_at_most_three_of_singleton_profile no_both_two_of_empty_equal_even
  key_of_known_dist_two_three from AdjacentCutFiveSixteenSingletonDepth189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

open private disjoint_profile_sets restrict_unique_profile even_two_three_info even_three_two_info
  shore_port_cases cannot_fit_four_and_two_more from AdjacentCutFiveSixteenSingletonGeometry189

/-- The two unique exclusive ports cannot touch when both strict-even
classes have at least three vertices and the equal-odd class is nonempty. -/
theorem unique_exclusive_ports_nonadjacent_of_three_both
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    {C D : Cmp G a b} (cd : C≠D) {s x y : V}
    (sc : s∈Shore C) (as' : G.Adj a s) (bs' : G.Adj b s)
    (xd : x∈Shore D) (ax : G.Adj a x) (nx : ¬G.Adj b x)
    (yd : y∈Shore D) (by' : G.Adj b y) (ny : ¬G.Adj a y)
    (oa : (classSet D 3).card=1) (ob : (classSet D 4).card=1)
    (threeA : 3≤(classSet D 0).card) (threeB : 3≤(classSet D 1).card)
    (oddC : 0<(classSet D 5).card) : ¬G.Adj x y := by
  classical
  let A := classSet D 0
  let B := classSet D 1
  have notSD : s∉Shore D := fun h=>disjoint_left.mp (shore_disjoint cd) sc h
  have xB : x≠b := fun e=>(shore_off D).2 (e ▸ xd)
  have yA : y≠a := fun e=>(shore_off D).1 (e ▸ yd)
  have dxB := (mem_filter.mp (d2 hc xB.symm nx ab.symm ax)).2
  have dyA := (mem_filter.mp (d2 hc yA.symm ny ab by')).2
  have xk : key G a b x=3 := by simp [key,dist_eq_one_iff_adj.mpr ax,dxB]
  have yk : key G a b y=4 := by simp [key,dist_eq_one_iff_adj.mpr by',dyA]
  have L := restrict_unique_profile oa xd xk
  have R := restrict_unique_profile ob yd yk
  have leftEdge (u : V) (uv : u∈A) : G.Adj x u := by
    have p := even_two_three_info hc ab oa uv
    exact left_even_adjoins_exclusive hc ab L (mem_filter.mp uv).1 p.1 p.2
  have rightEdge (u : V) (uv : u∈B) : G.Adj y u := by
    have p := even_three_two_info hc ab ob uv
    exact right_even_adjoins_exclusive hc ab R (mem_filter.mp uv).1 p.1 p.2
  intro edge
  have aSee : A⊆PositiveEven G y := by
    intro u um
    have p := even_two_three_info hc ab oa um
    have y1 := dist_eq_one_iff_adj.mpr by'
    have ne : y≠u := fun e=>by rw [e,p.2] at y1; omega
    have no : ¬G.Adj y u := by
      intro h
      have t := hc.dist_triangle (u:=b) (v:=y) (w:=u)
      rw [p.2,y1,dist_eq_one_iff_adj.mpr h] at t
      omega
    have d := (mem_filter.mp (d2 hc ne no edge.symm (leftEdge u um))).2
    exact mem_positive.mpr ⟨ne.symm,by simp [d]⟩
  have bSee : B⊆PositiveEven G x := by
    intro u um
    have p := even_three_two_info hc ab ob um
    have x1 := dist_eq_one_iff_adj.mpr ax
    have ne : x≠u := fun e=>by rw [e,p.1] at x1; omega
    have no : ¬G.Adj x u := by
      intro h
      have t := hc.dist_triangle (u:=a) (v:=x) (w:=u)
      rw [p.1,x1,dist_eq_one_iff_adj.mpr h] at t
      omega
    have d := (mem_filter.mp (d2 hc ne no edge (rightEdge u um))).2
    exact mem_positive.mpr ⟨ne.symm,by simp [d]⟩
  have aPos : a∈PositiveEven G y := mem_positive.mpr ⟨yA.symm,by rw [dist_comm,dyA]; decide⟩
  have sY := foreign_pos_even hc cd.symm yd sc by' bs'
  have bPos : b∈PositiveEven G x := mem_positive.mpr ⟨xB.symm,by rw [dist_comm,dxB]; decide⟩
  have sX := foreign_pos_even hc cd.symm xd sc ax as'
  have notA {z : V} (zd : z∈Shore D) (zo : z∉A) : z∉PositiveEven G y := by
    intro zp
    have four : 4≤(insert z A).card := by rw [card_insert_of_not_mem zo]; exact Nat.succ_le_succ threeA
    have bound : insert z A⊆Shore D := insert_subset_iff.mpr ⟨zd,filter_subset _ _⟩
    exact cannot_fit_four_and_two_more even four (insert_subset_iff.mpr ⟨zp,aSee⟩)
      (fun h=>notSD (bound h)) (fun h=>(shore_off D).1 (bound h))
      (fun e=>(shore_off C).1 (e.symm ▸ sc)) sY aPos
  have notB {z : V} (zd : z∈Shore D) (zo : z∉B) : z∉PositiveEven G x := by
    intro zp
    have four : 4≤(insert z B).card := by rw [card_insert_of_not_mem zo]; exact Nat.succ_le_succ threeB
    have bound : insert z B⊆Shore D := insert_subset_iff.mpr ⟨zd,filter_subset _ _⟩
    exact cannot_fit_four_and_two_more even four (insert_subset_iff.mpr ⟨zp,bSee⟩)
      (fun h=>notSD (bound h)) (fun h=>(shore_off D).2 (bound h))
      (fun e=>(shore_off C).2 (e.symm ▸ sc)) sX bPos
  let J := G.induce (↑(Shore D) : Set V)
  let hit (u : V) := G.Adj x u ∨ G.Adj y u
  have propagate {u v : ↑(↑(Shore D) : Set V)} (p : J.Walk u v) :
      hit u.val → hit v.val := by
    induction p with
    | nil => exact id
    | @cons u w v e q ih =>
      intro h
      apply ih
      apply Classical.byContradiction
      intro hz
      have nxw : ¬G.Adj x w.val := fun f=>hz (.inl f)
      have nyw : ¬G.Adj y w.val := fun f=>hz (.inr f)
      have xw : x≠w.val := fun f=>nyw (f ▸ edge.symm)
      have yw : y≠w.val := fun f=>nxw (f ▸ edge)
      rcases h with h|h
      · have dt := (mem_filter.mp (d2 hc xw nxw h e)).2
        have wp := mem_positive.mpr ⟨xw.symm,by rw [dt]; decide⟩
        exact notB w.property (fun b=>nyw (rightEdge _ b)) wp
      · have dt := (mem_filter.mp (d2 hc yw nyw h e)).2
        have wp := mem_positive.mpr ⟨yw.symm,by rw [dt]; decide⟩
        exact notA w.property (fun a=>nxw (leftEdge _ a)) wp
  obtain ⟨z,zm⟩ := card_pos.mp oddC
  obtain ⟨zd,zk⟩ := mem_filter.mp zm
  obtain ⟨p⟩ := (shore_connected D).preconnected ⟨x,xd⟩ ⟨z,zd⟩
  have xz_yz := propagate p (.inr edge.symm)
  obtain ⟨za,zb,par⟩ := key_facts hc ab z
  rw [zk] at za zb par
  change G.dist a z=depth G a b z+0 at za
  change G.dist b z=depth G a b z+0 at zb
  change depth G a b z % 2 = 1 at par
  have d1 : depth G a b z=1 := by
    rcases xz_yz with e|e
    · have q := hc.dist_triangle (u:=a) (v:=x) (w:=z)
      rw [dist_eq_one_iff_adj.mpr ax,dist_eq_one_iff_adj.mpr e] at q
      omega
    · have q := hc.dist_triangle (u:=b) (v:=y) (w:=z)
      rw [dist_eq_one_iff_adj.mpr by',dist_eq_one_iff_adj.mpr e] at q
      omega
  have az : G.Adj a z := dist_eq_one_iff_adj.mp (by omega)
  have bz : G.Adj b z := dist_eq_one_iff_adj.mp (by omega)
  have zoA : z∉A := fun h=>by
    have zz := (mem_filter.mp h).2
    rw [zk] at zz
    exact (by decide : (5:Fin 6)≠0) zz
  have zoB : z∉B := fun h=>by
    have zz := (mem_filter.mp h).2
    rw [zk] at zz
    exact (by decide : (5:Fin 6)≠1) zz
  have xz : G.Adj x z := by
    apply Classical.byContradiction
    intro h
    have ne : x≠z := fun f=>by rw [f,zk] at xk; contradiction
    have d := (mem_filter.mp (d2 hc ne h ax.symm az)).2
    exact notB zd zoB (mem_positive.mpr ⟨ne.symm,by rw [d]; decide⟩)
  have yz : G.Adj y z := by
    apply Classical.byContradiction
    intro h
    have ne : y≠z := fun f=>by rw [f,zk] at yk; contradiction
    have d := (mem_filter.mp (d2 hc ne h by'.symm bz)).2
    exact notA zd zoA (mem_positive.mpr ⟨ne.symm,by rw [d]; decide⟩)
  have zA : A⊆PositiveEven G z := by
    intro u um
    have dst := even_two_three_info hc ab oa um
    have z1 := dist_eq_one_iff_adj.mpr bz
    have ne : z≠u := fun e=>by rw [e,dst.2] at z1; omega
    have no : ¬G.Adj z u := by
      intro h
      have t := hc.dist_triangle (u:=b) (v:=z) (w:=u)
      rw [dst.2,z1,dist_eq_one_iff_adj.mpr h] at t
      omega
    have d := (mem_filter.mp (d2 hc ne no xz.symm (leftEdge u um))).2
    exact mem_positive.mpr ⟨ne.symm,by rw [d]; decide⟩
  have zB : B⊆PositiveEven G z := by
    intro u um
    have dst := even_three_two_info hc ab ob um
    have z1 := dist_eq_one_iff_adj.mpr az
    have ne : z≠u := fun e=>by rw [e,dst.1] at z1; omega
    have no : ¬G.Adj z u := by
      intro h
      have t := hc.dist_triangle (u:=a) (v:=z) (w:=u)
      rw [dst.1,z1,dist_eq_one_iff_adj.mpr h] at t
      omega
    have d := (mem_filter.mp (d2 hc ne no yz.symm (rightEdge u um))).2
    exact mem_positive.mpr ⟨ne.symm,by rw [d]; decide⟩
  have sum := (card_le_card (union_subset zA zB)).trans (positive_cap z even)
  rw [card_union_of_disjoint (disjoint_profile_sets D (by decide : (0:Fin 6)≠1))] at sum
  omega

theorem nonadjacent_separator_of_common_other_unique_three_both
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    {C D : Cmp G a b} (cd : C≠D) {s : V} (sc : s∈Shore C)
    (as' : G.Adj a s) (bs' : G.Adj b s)
    (ea : 0<(classSet D 0).card) (eb : 0<(classSet D 1).card)
    (ec : (classSet D 2).card=0) (oa : (classSet D 3).card=1) (ob : (classSet D 4).card=1)
    (threeA : 3≤(classSet D 0).card) (threeB : 3≤(classSet D 1).card)
    (oddC : 0<(classSet D 5).card) :
    ∃ x y : V,x≠y ∧ ¬G.Adj x y ∧ ¬(G.induce {z : V | z≠x ∧ z≠y}).Connected := by
  classical
  let A := classSet D 0
  let B := classSet D 1
  have notSD : s∉Shore D := fun h=>disjoint_left.mp (shore_disjoint cd) sc h
  obtain ⟨v,va⟩ : A.Nonempty := card_pos.mp ea
  obtain ⟨w,wb⟩ : B.Nonempty := card_pos.mp eb
  have vrel := even_two_three_info hc ab oa va
  have wrel := even_three_two_info hc ab ob wb
  obtain ⟨x,xd,ax,nx⟩ := exclusive_left_port_of_strictly_nearer hc (mem_filter.mp va).1 (by omega)
  obtain ⟨y,yd,by',ny⟩ := exclusive_right_port_of_strictly_nearer hc (mem_filter.mp wb).1 (by omega)
  have xB : x≠b := fun e=>(shore_off D).2 (e ▸ xd)
  have yA : y≠a := fun e=>(shore_off D).1 (e ▸ yd)
  have dxB := (mem_filter.mp (d2 hc xB.symm nx ab.symm ax)).2
  have dyA := (mem_filter.mp (d2 hc yA.symm ny ab by')).2
  have xk : key G a b x=3 := by simp [key,dist_eq_one_iff_adj.mpr ax,dxB]
  have yk : key G a b y=4 := by simp [key,dist_eq_one_iff_adj.mpr by',dyA]
  have L := restrict_unique_profile oa xd xk
  have R := restrict_unique_profile ob yd yk
  have xy : x≠y := fun e=>ny (e ▸ ax)
  have xyNo := unique_exclusive_ports_nonadjacent_of_three_both hc ab even cd sc as' bs'
    xd ax nx yd by' ny oa ob threeA threeB oddC
  refine ⟨x,y,xy,xyNo,?_⟩
  intro conn'
  let U : Set V := {z : V | z≠x ∧ z≠y}
  have sx : s≠x := fun e=>notSD (e.symm ▸ xd)
  have sy : s≠y := fun e=>notSD (e.symm ▸ yd)
  have vx : v≠x := fun e=>by have h := (mem_filter.mp va).2; rw [e,xk] at h; exact (by decide : (3:Fin 6)≠0) h
  have vy : v≠y := fun e=>by have h := (mem_filter.mp va).2; rw [e,yk] at h; exact (by decide : (4:Fin 6)≠0) h
  have vaD := (mem_filter.mp va).1
  have av : ¬G.Adj a v := fun h=>by have e := dist_eq_one_iff_adj.mpr h; omega
  have bv : ¬G.Adj b v := fun h=>by have e := dist_eq_one_iff_adj.mpr h; omega
  have stay {u w : U} (p : (G.induce U).Walk u w) :
      (u.val∈Shore D ∧ ¬G.Adj a u.val ∧ ¬G.Adj b u.val) →
      (w.val∈Shore D ∧ ¬G.Adj a w.val ∧ ¬G.Adj b w.val) := by
    induction p with
    | nil => exact id
    | @cons u t w edge p ih =>
      intro ⟨ud,au,bu⟩
      apply ih
      have e : G.Adj u.val t.val := edge
      rcases shore_closed D _ ud _ e with ha|hb|td
      · exact (au (by simpa only [ha] using e.symm)).elim
      · exact (bu (by simpa only [hb] using e.symm)).elim
      refine ⟨td,?_⟩
      have no (port : G.Adj a t.val ∨ G.Adj b t.val) : False := by
        rcases shore_port_cases hc ab td L R port with eq|eq|mode
        · exact t.property.1 eq
        · exact t.property.2 eq
        have ua : u.val≠a := fun f=>(shore_off D).1 (Eq.mp (congrArg (fun h : V => h∈Shore D) f) ud)
        have ub : u.val≠b := fun f=>(shore_off D).2 (Eq.mp (congrArg (fun h : V => h∈Shore D) f) ud)
        have dA := (mem_filter.mp (d2 hc ua.symm au mode.1 e.symm)).2
        have dB := (mem_filter.mp (d2 hc ub.symm bu mode.2.1 e.symm)).2
        exact no_both_two_of_empty_equal_even ec ud dA dB
      exact ⟨fun h=>no (.inl h),fun h=>no (.inr h)⟩
  obtain ⟨p⟩ := conn'.preconnected (⟨v,⟨vx,vy⟩⟩ : U) ⟨s,⟨sx,sy⟩⟩
  exact notSD (stay p ⟨vaD,av,bv⟩).1


#print axioms unique_exclusive_ports_nonadjacent_of_three_both
#print axioms nonadjacent_separator_of_common_other_unique_three_both
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
