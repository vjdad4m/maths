import DistanceTwoCut189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 foreign_subset reaches_all_left from CrossSaturation189
open private left_boundary right_boundary from AdjacentCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

/-- Symmetric presentation of a separating pair, exchanging the two sides. -/
def switch (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ u∈S.R,G.Adj a u) (rightB : ∃ u∈S.R,G.Adj b u) :
    Graffiti189LongestPath.CrossSaturation.Split G a b :=
  ⟨S.R,S.L,S.dis.symm,S.rightOff,S.leftOff,rightConnected,
    (fun u ur v vl uv=>S.cross _ vl _ ur uv.symm),rightA,rightB,
    fun v=>by simpa only [or_comm (a:=v∈S.L) (b:=v∈S.R)] using S.cover v⟩

private theorem far_across (hc : G.Connected) (far : 4≤G.dist a b)
    {x z : V} (xl : x∈S.L) (zr : z∈S.R) (ax : G.Adj a x) (bz : G.Adj b z) :
    4≤G.dist x z := by
  have zo : z∉S.L := fun h=>disjoint_left.mp S.dis h zr
  have mk := cross_metric S.L hc xl zo (left_boundary S)
  have u := hc.dist_triangle (u:=a) (v:=x) (w:=b)
  have v := hc.dist_triangle (u:=a) (v:=z) (w:=b)
  have ax1 := dist_eq_one_iff_adj.mpr ax
  have xa1 := dist_eq_one_iff_adj.mpr ax.symm
  have bz1 := dist_eq_one_iff_adj.mpr bz
  have zb1 := dist_eq_one_iff_adj.mpr bz.symm
  omega

private theorem saturation_impossible (hc : G.Connected) (far : 4≤G.dist a b)
    {x : V} (xl : x∈S.L) (ax : G.Adj a x) (sat : DistanceTwo G x = S.foreignA) : False := by
  obtain ⟨y,yl,by'⟩ := S.leftB
  have l := reaches_all_left S hc xl sat yl
  have up := hc.dist_triangle (u:=a) (v:=x) (w:=b)
  have a1 := dist_eq_one_iff_adj.mpr ax
  rcases l with rfl|xy
  · have b1 := dist_eq_one_iff_adj.mpr by'.symm
    omega
  · have q := G.dist_le (Walk.cons xy (Walk.cons by'.symm .nil))
    simp at q
    omega

private theorem distance_two_cap_from_far (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤6) (far : 4≤G.dist a b)
    (rightB : ∃ z∈S.R,G.Adj b z)
    {x : V} (xl : x∈S.L) (ax : G.Adj a x) : (DistanceTwo G x).card≤4 := by
  obtain ⟨z,zr,bz⟩ := rightB
  have h := distanceTwo_add_two_le_even_of_far hc (far_across S hc far xl zr ax bz)
  have cap := even x
  omega

private theorem foreign_a_le_three (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤6) (far : 4≤G.dist a b)
    (rightB : ∃ z∈S.R,G.Adj b z) : S.foreignA.card≤3 := by
  obtain ⟨x,xl,ax⟩ := S.leftA
  have sub := foreign_subset S hc xl ax
  have cnt := card_le_card sub
  have d2cap := distance_two_cap_from_far S hc even far rightB xl ax
  by_contra bad
  exact saturation_impossible S hc far xl ax (eq_of_subset_of_card_le sub (by omega)).symm

private theorem foreign_b_le_one_of_three_a (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤6) (far : 4≤G.dist a b)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (rightB : ∃ z∈S.R,G.Adj b z) (three : S.foreignA.card=3) :
    (S.R.filter (G.Adj b)).card≤1 := by
  obtain ⟨x,xl,ax⟩ := S.leftA
  have d2cap := distance_two_cap_from_far S hc even far rightB xl ax
  have sub := foreign_subset S hc xl ax
  have cnt := card_le_card sub
  have d24 : (DistanceTwo G x).card=4 := by
    by_contra e
    exact saturation_impossible S hc far xl ax (eq_of_subset_of_card_le sub (by omega)).symm
  have niche (y : V) : G.dist x y≤4 := by
    by_contra big
    have h : 5≤G.dist x y := by omega
    have n := twoEvenLayers_of_radius_five hc 2 conn h
    have cap := even x
    omega
  have bound : (Shell G x 4).card≤1 := by
    have n := shell_two_four_le_of_even (d:=5) (even x)
    rw [shell_two] at n
    omega
  have incl : S.R.filter (G.Adj b) ⊆ Shell G x 4 := by
    intro z hz
    obtain ⟨zr,bz⟩ := mem_filter.mp hz
    have lo := far_across S hc far xl zr ax bz
    have hi := niche z
    exact mem_shell.mpr (by omega)
  exact (card_le_card incl).trans bound

private theorem left_four_at_dist_two (hc : G.Connected) (far : 4≤G.dist a b)
    (high : ∀ z∈S.L, 5≤G.degree z)
    (only : (S.L.filter (G.Adj b)).card≤1) :
    4≤(S.L ∩ DistanceTwo G b).card := by
  classical
  obtain ⟨x,xl,bx⟩ := S.leftB
  have xport : x∈S.L.filter (G.Adj b) := mem_filter.mpr ⟨xl,bx⟩
  have single (y : V) (yl : y∈S.L) (by' : G.Adj b y) : y=x := by
    have hh : S.L.filter (G.Adj b)={x} :=
      (eq_of_subset_of_card_le (singleton_subset_iff.mpr xport) (by simpa using only)).symm
    have hy : y∈S.L.filter (G.Adj b) := mem_filter.mpr ⟨yl,by'⟩
    simpa [hh] using hy
  have ax : ¬G.Adj a x := by
    intro ax
    have c := G.dist_le (Walk.cons ax (Walk.cons bx.symm .nil))
    simp at c
    omega
  have sub : G.neighborFinset x ⊆ insert b (S.L ∩ DistanceTwo G b) := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases left_boundary S x xl y xy with rfl|rfl|yl
    · exact (ax xy.symm).elim
    · simp
    have yb : ¬G.Adj b y := fun h=>xy.ne (single y yl h).symm
    have bne : b≠y := fun e=>S.leftOff.2 (e.symm ▸ yl)
    exact mem_insert_of_mem (mem_inter.mpr ⟨yl,d2 hc bne yb bx xy⟩)
  have n := card_le_card sub
  rw [card_neighborFinset_eq_degree] at n
  have m := card_insert_le b (S.L ∩ DistanceTwo G b)
  have h := high x xl
  omega


private theorem left_at_least_one_at_dist_two (hc : G.Connected) (far : 4≤G.dist a b) :
    1≤(S.L ∩ DistanceTwo G b).card := by
  classical
  obtain ⟨x,xl,bx⟩ := S.leftB
  obtain ⟨y,yl,ay⟩ := S.leftA
  by_contra bad
  let W : Set V := ↑S.L
  obtain ⟨p⟩ := S.leftConnected.preconnected (⟨x,xl⟩ : W) (⟨y,yl⟩ : W)
  have prop {u v : W} (q : (G.induce W).Walk u v) : G.Adj b u.val → G.Adj b v.val := by
    induction q with
    | nil => exact id
    | @cons u w v uw q ih =>
      intro bu
      apply ih
      apply Classical.byContradiction
      intro no
      have wh : w.val∈S.L := w.property
      have nb : b≠w.val := fun e=>S.leftOff.2 ((congrArg (fun v=>v∈S.L) e.symm).mp wh)
      have wd := d2 hc nb no bu (show G.Adj u.val w.val from uw)
      have cnt : 0<(S.L ∩ DistanceTwo G b).card := card_pos.mpr ⟨_,mem_inter.mpr ⟨wh,wd⟩⟩
      omega
  have by' := prop p bx
  have hh := G.dist_le (Walk.cons ay (Walk.cons by'.symm .nil))
  simp at hh
  omega

private theorem impossible_far_cut_three_on_right (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤6) (far : 4≤G.dist a b)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ u∈S.R,G.Adj a u) (rightB : ∃ u∈S.R,G.Adj b u)
    (three : S.foreignA.card=3) : False := by
  classical
  let T := switch S rightConnected rightA rightB
  have far' : 4≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have B_right := foreign_b_le_one_of_three_a S hc even far conn rightB three
  have B_left := foreign_a_le_three T.flip hc even far' S.leftA
  change (S.L.filter (G.Adj b)).card≤3 at B_left
  have an : ¬G.Adj a b := by
    intro e
    have h := dist_eq_one_iff_adj.mpr e
    omega
  have countB : G.degree b ≤ 4 := by
    have incl : G.neighborFinset b ⊆ S.L.filter (G.Adj b) ∪ S.R.filter (G.Adj b) := by
      intro v hv
      have bv := (mem_neighborFinset G b v).mp hv
      rcases S.cover v with rfl|rfl|vl|vr
      · exact (an bv.symm).elim
      · exact (G.loopless _ bv).elim
      · exact mem_union_left _ (mem_filter.mpr ⟨vl,bv⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨vr,bv⟩)
    have m := (card_le_card incl).trans (card_union_le _ _)
    rw [card_neighborFinset_eq_degree] at m
    omega
  have Rhigh (u : V) (ur : u∈T.L) : 5≤G.degree u :=
    (degree u b (fun h=>S.rightOff.2 (h ▸ ur))).resolve_right (by omega)
  have left := left_at_least_one_at_dist_two S hc far
  have right := left_four_at_dist_two T hc far Rhigh B_right
  change 4≤(S.R ∩ DistanceTwo G b).card at right
  have dis : Disjoint (S.L ∩ DistanceTwo G b) (S.R ∩ DistanceTwo G b) :=
    S.dis.mono inter_subset_left inter_subset_left
  have m := card_le_card (union_subset
    (inter_subset_right : S.L ∩ DistanceTwo G b ⊆ DistanceTwo G b)
    (inter_subset_right : S.R ∩ DistanceTwo G b ⊆ DistanceTwo G b))
  rw [card_union_of_disjoint dis] at m
  have e := distanceTwo_add_two_le_even_of_far hc far'
  have cap := even b
  omega

private theorem impossible_far_cut_high_first (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤6) (far : 4≤G.dist a b)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (highA : 5≤G.degree a)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ u∈S.R,G.Adj a u) (rightB : ∃ u∈S.R,G.Adj b u) : False := by
  classical
  let T := switch S rightConnected rightA rightB
  have A_right := foreign_a_le_three S hc even far rightB
  have A_left := foreign_a_le_three T hc even far S.leftB
  change S.localA.card≤3 at A_left
  have an : ¬G.Adj a b := by
    intro e
    have h := dist_eq_one_iff_adj.mpr e
    omega
  have countA : G.degree a ≤ S.localA.card+S.foreignA.card := by
    have incl : G.neighborFinset a ⊆ S.localA ∪ S.foreignA := by
      intro v hv
      have av := (mem_neighborFinset G a v).mp hv
      rcases S.cover v with rfl|rfl|vl|vr
      · exact (G.loopless _ av).elim
      · exact (an av).elim
      · exact mem_union_left _ (mem_filter.mpr ⟨vl,av⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨vr,av⟩)
    have n := (card_le_card incl).trans (card_union_le _ _)
    simpa only [card_neighborFinset_eq_degree] using n

  by_cases three : S.foreignA.card=3
  · exact impossible_far_cut_three_on_right S hc even far conn degree rightConnected rightA rightB three
  have other : T.foreignA.card=3 := by
    change S.localA.card=3
    omega
  exact impossible_far_cut_three_on_right T hc even far conn degree S.leftConnected S.leftA S.leftB other

/-- Under the degree-five premise, the vertices of a separating pair
leaving two connected sides cannot be at distance at least four. -/
theorem cut_distance_le_three_at_five (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤6)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected) :
    G.dist a b≤3 := by
  by_contra big
  have far : 4≤G.dist a b := by omega
  have ab : a≠b := by
    intro h
    rw [h,SimpleGraph.dist_self] at far
    omega
  obtain ⟨q⟩ := rightConnected.nonempty
  have nonempty : S.R.Nonempty := ⟨q.val,q.property⟩
  have rightA := side_hits_first_after_deleting_second ab S.R nonempty S.rightOff.1 S.rightOff.2
    (right_boundary S) (conn {b} (by simp))
  have rightB := side_hits_first_after_deleting_second ab.symm S.R nonempty S.rightOff.2 S.rightOff.1
    (fun u hu v e=>by simpa only [or_left_comm] using right_boundary S u hu v e)
    (conn {a} (by simp))
  rcases degree a b ab with ha|hb
  · exact impossible_far_cut_high_first S hc even far conn degree ha rightConnected rightA rightB
  have far' : 4≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  exact impossible_far_cut_high_first S.flip hc even far' conn degree hb rightConnected rightB rightA

#print axioms cut_distance_le_three_at_five
end Graffiti189LongestPath.CrossSaturation.Split.Five
