import AdjacentCutFiveFifteenSingletonMixed189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint from AdjacentCutFiveActual189
open private key classSet key_facts from AdjacentCutFiveTopProfiles189
open private cannot_fit_four_and_two_more from AdjacentCutFiveSixteenSingletonGeometry189
open private d2 mem_positive from AdjacentCutFiveBound189
open private positive_cap foreign_pos_even from AdjacentCutFiveComponents189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem dist_two_positive_even
    (hc : G.Connected) {q r t : V} (ne : q≠t) (no : ¬G.Adj q t)
    (qr : G.Adj q r) (rt : G.Adj r t) : t∈PositiveEven G q :=
  mem_positive.mpr ⟨ne.symm,by rw [(mem_filter.mp (d2 hc ne no qr rt)).2]; decide⟩

private theorem adj_forbidden_by_dist
    (hc : G.Connected) {r x w : V} (h : G.dist r x+1<G.dist r w) : ¬G.Adj x w := by
  intro e
  have tri := hc.dist_triangle (u:=r) (v:=x) (w:=w)
  rw [dist_eq_one_iff_adj.mpr e] at tri
  omega

private theorem dist_two_from_b_exclusive
    (hc : G.Connected) (ab : G.Adj a b) {D : Cmp G a b}
    {y : V} (yd : y∈Shore D) (by' : G.Adj b y) (ny : ¬G.Adj a y) :
    G.dist a y=2 := by
  have ya : y≠a := fun e=>(shore_off D).1 (e ▸ yd)
  exact (mem_filter.mp (d2 hc ya.symm ny ab by')).2

private theorem not_both_b_ports_adjacent_common
    (hc : G.Connected) (_ab : G.Adj a b) (even : ∀ w,(EvenFrom G w).card≤6)
    {C D : Cmp G a b} (CD : C≠D) {s : V} (sc : s∈Shore C) (as' : G.Adj a s)
    {c x y z : V} (cd : c∈Shore D) (xd : x∈Shore D)
    (ac : G.Adj a c) (bc : G.Adj b c) (ax : G.Adj a x) (nx : ¬G.Adj b x)
    (three : (classSet D 0).card=3) (four : (classSet D 1).card=4)
    (dA : ∀ w∈classSet D 0,G.dist a w=2 ∧ G.dist b w=3)
    (dB : ∀ w∈classSet D 1,G.dist a w=3 ∧ G.dist b w=2)
    (xAll : ∀ w∈classSet D 0,G.Adj x w)
    (yzCover : ∀ w∈classSet D 1,G.Adj y w ∨ G.Adj z w)
    (cy : G.Adj c y) (cz : G.Adj c z) : False := by
  classical
  let B := classSet D 1
  have ac1 := dist_eq_one_iff_adj.mpr ac
  have bc1 := dist_eq_one_iff_adj.mpr bc
  have path : B⊆PositiveEven G c := by
    intro w wm
    have d := (dB w wm).1
    have ne : c≠w := fun h=>by rw [h,d] at ac1; omega
    have no : ¬G.Adj c w := adj_forbidden_by_dist hc (show G.dist a c+1<G.dist a w by omega)
    exact (yzCover w wm).elim (dist_two_positive_even hc ne no cy) (dist_two_positive_even hc ne no cz)
  have sPos := foreign_pos_even hc CD.symm cd sc ac as'
  have sNot : s∉B := fun m=>disjoint_left.mp (shore_disjoint CD) sc (mem_filter.mp m).1
  by_cases cx : G.Adj c x
  · obtain ⟨w,wm⟩ := card_pos.mp (show 0<(classSet D 0).card by omega)
    have wNot : w∉B := by
      intro m
      have k := (mem_filter.mp m).2
      rw [(mem_filter.mp wm).2] at k
      exact (by decide : (0:Fin 6)≠1) k
    have ws : w≠s := fun e=>disjoint_left.mp (shore_disjoint CD) sc (e ▸ (mem_filter.mp wm).1)
    have d := (dA w wm).2
    have ne : c≠w := fun h=>by rw [h,d] at bc1; omega
    have no := adj_forbidden_by_dist hc (show G.dist b c+1<G.dist b w by omega)
    exact cannot_fit_four_and_two_more even four.ge path sNot wNot ws sPos
      (dist_two_positive_even hc ne no cx (xAll w wm))
  · have xNot : x∉B := by
      intro m
      have h := (dB x m).1
      rw [dist_eq_one_iff_adj.mpr ax] at h
      omega
    have xs : x≠s := fun e=>disjoint_left.mp (shore_disjoint CD) sc (e ▸ xd)
    have ne : c≠x := fun h=>nx (h ▸ bc)
    exact cannot_fit_four_and_two_more even four.ge path sNot xNot xs sPos
      (dist_two_positive_even hc ne cx ac.symm ax)

#print axioms not_both_b_ports_adjacent_common

private theorem b_port_selected_by_common_misses_b_even
    (hc : G.Connected) (even : ∀ w,(EvenFrom G w).card≤6)
    {C D : Cmp G a b} (CD : C≠D) {s : V} (sc : s∈Shore C) (as' : G.Adj a s)
    {c x y z : V} (cd : c∈Shore D) (zd : z∈Shore D)
    (ac : G.Adj a c) (bc : G.Adj b c) (bz : G.Adj b z) (nz : ¬G.Adj a z)
    (three : (classSet D 0).card=3)
    (dA : ∀ w∈classSet D 0,G.dist a w=2 ∧ G.dist b w=3)
    (dB : ∀ w∈classSet D 1,G.dist a w=3 ∧ G.dist b w=2)
    (xAll : ∀ w∈classSet D 0,G.Adj x w)
    (cx : G.Adj c x) (cy : G.Adj c y) (cz : ¬G.Adj c z) :
    ∀ w∈classSet D 1,¬G.Adj y w := by
  classical
  intro w wm yw
  let A := classSet D 0
  have ac1 := dist_eq_one_iff_adj.mpr ac
  have bc1 := dist_eq_one_iff_adj.mpr bc
  have z1 := dist_eq_one_iff_adj.mpr bz
  have cNz : c≠z := fun e=>nz (e ▸ ac)
  have zNot : z∉A := by
    intro m
    have h := (dA z m).2
    omega
  have path : insert z A⊆PositiveEven G c := by
    intro v vm
    rcases mem_insert.mp vm with rfl|m
    · exact dist_two_positive_even hc cNz cz bc.symm bz
    · have vd := (dA v m).2
      have ne : c≠v := fun h=>by rw [h,vd] at bc1; omega
      have no := adj_forbidden_by_dist hc (show G.dist b c+1<G.dist b v by omega)
      exact dist_two_positive_even hc ne no cx (xAll v m)
  have four : 4≤(insert z A).card := by rw [card_insert_of_not_mem zNot,three]
  have sPos := foreign_pos_even hc CD.symm cd sc ac as'
  have sNot : s∉insert z A := by
    intro m
    rcases mem_insert.mp m with rfl|m
    · exact disjoint_left.mp (shore_disjoint CD) sc zd
    · exact disjoint_left.mp (shore_disjoint CD) sc (mem_filter.mp m).1
  have wNot : w∉insert z A := by
    intro m
    rcases mem_insert.mp m with rfl|m
    · have h := (dB w wm).2
      omega
    · have k := (mem_filter.mp m).2
      rw [(mem_filter.mp wm).2] at k
      exact (by decide : (1:Fin 6)≠0) k
  have ws : w≠s := fun e=>disjoint_left.mp (shore_disjoint CD) sc (e ▸ (mem_filter.mp wm).1)
  have wd := (dB w wm).1
  have ne : c≠w := fun h=>by rw [h,wd] at ac1; omega
  have no := adj_forbidden_by_dist hc (show G.dist a c+1<G.dist a w by omega)
  exact cannot_fit_four_and_two_more even four path sNot wNot ws sPos
    (dist_two_positive_even hc ne no cy yw)

private theorem b_ports_no_edge_of_four_even_exhausted
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ w,(EvenFrom G w).card≤6)
    {C D : Cmp G a b} (CD : C≠D) {s : V} (sc : s∈Shore C) (bs' : G.Adj b s)
    {y z : V} (yd : y∈Shore D) (by' : G.Adj b y) (na : ¬G.Adj a y)
    (four : (classSet D 1).card=4)
    (dB : ∀ w∈classSet D 1,G.dist b w=2)
    (yMiss : ∀ w∈classSet D 1,¬G.Adj y w)
    (zAll : ∀ w∈classSet D 1,G.Adj z w) : ¬G.Adj y z := by
  intro yz
  let B := classSet D 1
  have y1 := dist_eq_one_iff_adj.mpr by'
  have path : B⊆PositiveEven G y := by
    intro w wm
    have dw := dB w wm
    have ne : y≠w := fun h=>by rw [h,dw] at y1; omega
    exact dist_two_positive_even hc ne (yMiss w wm) yz (zAll w wm)
  have yA : y≠a := fun e=>(shore_off D).1 (e ▸ yd)
  have d := dist_two_from_b_exclusive hc ab yd by' na
  have aPos : a∈PositiveEven G y := mem_positive.mpr ⟨yA.symm,by rw [dist_comm,d]; decide⟩
  have sPos := foreign_pos_even hc CD.symm yd sc by' bs'
  exact cannot_fit_four_and_two_more even four.ge path
    (fun m=>disjoint_left.mp (shore_disjoint CD) sc (mem_filter.mp m).1)
    (fun m=>(shore_off D).1 (mem_filter.mp m).1)
    (fun e=>(shore_off C).1 (e.symm ▸ sc)) sPos aPos

#print axioms b_port_selected_by_common_misses_b_even
#print axioms b_ports_no_edge_of_four_even_exhausted
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
