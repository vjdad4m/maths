import DegreeFiveActualCut189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 foreign_subset from CrossSaturation189
open private left_boundary from AdjacentCut189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

noncomputable def secondA (G : SimpleGraph V) (A : Finset V) (a : V) : Finset V := A ∩ DistanceTwo G a

/-- An internal edge between an a-porter and a b-porter. -/
def portBridge : Prop :=
  ∃ x∈S.L,∃ y∈S.L,G.Adj a x ∧ G.Adj x y ∧ G.Adj b y

private theorem cut_not_adj (far : 3≤G.dist a b) : ¬G.Adj a b := by
  intro e
  have h := dist_eq_one_iff_adj.mpr e
  omega

private theorem not_common (far : 3≤G.dist a b) {x : V} (ax : G.Adj a x) : ¬G.Adj b x := by
  intro bx
  have t := G.dist_le (Walk.cons ax (Walk.cons bx.symm .nil))
  simp at t
  omega

private theorem side_universal_if_no_local_d2 (hc : G.Connected)
    {x : V} (xl : x∈S.L) (no : ∀ z∈S.L,z∉DistanceTwo G x) :
    ∀ z∈S.L,z=x ∨ G.Adj x z := by
  classical
  intro z zl
  let W : Set V := ↑S.L
  obtain ⟨p⟩ := S.leftConnected.preconnected (⟨x,xl⟩ : W) (⟨z,zl⟩ : W)
  have step {u v : W} (q : (G.induce W).Walk u v) :
      (u.val=x ∨ G.Adj x u.val) → (v.val=x ∨ G.Adj x v.val) := by
    induction q with
    | nil => exact id
    | @cons u v w uv q ih =>
      intro hu
      apply ih
      by_cases vx : v.val=x
      · exact .inl vx
      by_cases xv : G.Adj x v.val
      · exact .inr xv
      change G.Adj u.val v.val at uv
      rcases hu with ux|xu
      · exact (xv (ux ▸ uv)).elim
      exact (no _ v.property (d2 hc (Ne.symm vx) xv xu uv)).elim
  exact step p (.inl rfl)

private theorem extra_local_or_cut (hc : G.Connected) (far : 3≤G.dist a b)
    {x : V} (xl : x∈S.L) (ax : G.Adj a x) :
    ∃ z, z∈DistanceTwo G x ∧ (z=b ∨ z∈S.L) := by
  classical
  by_cases localSide : ∃ z∈S.L,z∈DistanceTwo G x
  · obtain ⟨z,zl,z2⟩ := localSide
    exact ⟨z,z2,.inr zl⟩
  obtain ⟨w,wl,bw⟩ := S.leftB
  have h := side_universal_if_no_local_d2 S hc xl (fun z zl z2=>localSide ⟨z,zl,z2⟩) w wl
  rcases h with rfl|xw
  · exact ((not_common far ax) bw).elim
  have xb : x≠b := fun e=>S.leftOff.2 (e ▸ xl)
  exact ⟨b,d2 hc xb (fun e=>not_common far ax e.symm) xw bw.symm,.inl rfl⟩

theorem foreign_a_ports_le_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) : S.foreignA.card≤4 := by
  classical
  obtain ⟨x,xl,ax⟩ := S.leftA
  obtain ⟨z,z2,zown⟩ := extra_local_or_cut S hc far xl ax
  have nz : z∉S.foreignA := by
    intro za
    have zr := (mem_filter.mp za).1
    rcases zown with rfl|zl
    · exact S.rightOff.2 zr
    exact disjoint_left.mp S.dis zl zr
  have sub : insert z S.foreignA ⊆ DistanceTwo G x := by
    intro w ww
    rcases mem_insert.mp ww with rfl|h
    · exact z2
    exact foreign_subset S hc xl ax h
  have m := card_le_card sub
  rw [card_insert_of_not_mem nz] at m
  have d := distanceTwo_le_of_even 5 x (even x)
  omega

theorem saturated_at_opposite_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (four : S.foreignA.card=4)
    {x : V} (xl : x∈S.L) (ax : G.Adj a x) :
    (DistanceTwo G x).card=5 ∧ ∀ z,G.dist x z≤3 := by
  classical
  obtain ⟨z,z2,zown⟩ := extra_local_or_cut S hc far xl ax
  have nz : z∉S.foreignA := by
    intro za
    have zr := (mem_filter.mp za).1
    rcases zown with rfl|zl
    · exact S.rightOff.2 zr
    exact disjoint_left.mp S.dis zl zr
  have sub : insert z S.foreignA ⊆ DistanceTwo G x := by
    intro w ww
    rcases mem_insert.mp ww with rfl|h
    · exact z2
    exact foreign_subset S hc xl ax h
  have m := card_le_card sub
  rw [card_insert_of_not_mem nz,four] at m
  have d := distanceTwo_le_of_even 5 x (even x)
  have eq : (DistanceTwo G x).card=5 := by omega
  refine ⟨eq,?_⟩
  intro w
  apply Classical.byContradiction
  intro bad
  have far' : 4≤G.dist x w := by omega
  have l := distanceTwo_add_two_le_even_of_far hc far'
  have cap := even x
  omega

private theorem secondA_right_and_left_le_five (even : ∀ x,(EvenFrom G x).card≤6) :
    (secondA G S.L a).card+(secondA G S.R a).card≤5 := by
  have dl : Disjoint (secondA G S.L a) (secondA G S.R a) :=
    S.dis.mono inter_subset_left inter_subset_left
  have s : secondA G S.L a ∪ secondA G S.R a ⊆ DistanceTwo G a :=
    union_subset inter_subset_right inter_subset_right
  have c := card_le_card s
  rw [card_union_of_disjoint dl] at c
  exact c.trans (distanceTwo_le_of_even 5 a (even a))

private theorem left_secondA_positive (hc : G.Connected) (far : 3≤G.dist a b) :
    1≤(secondA G S.L a).card := by
  classical
  obtain ⟨x,xl,ax⟩ := S.leftA
  obtain ⟨y,yl,by'⟩ := S.leftB
  apply Classical.byContradiction
  intro bad
  let W : Set V := ↑S.L
  obtain ⟨p⟩ := S.leftConnected.preconnected (⟨x,xl⟩ : W) (⟨y,yl⟩ : W)
  have step {u v : W} (q : (G.induce W).Walk u v) : G.Adj a u.val → G.Adj a v.val := by
    induction q with
    | nil => exact id
    | @cons u w v uw q ih =>
      intro au
      apply ih
      apply Classical.byContradiction
      intro no
      have wh : w.val∈S.L := w.property
      have na : a≠w.val := fun e=>S.leftOff.1 ((congrArg (fun v=>v∈S.L) e.symm).mp wh)
      have t := d2 hc na no au (show G.Adj u.val w.val from uw)
      have m : w.val∈secondA G S.L a := mem_inter.mpr ⟨wh,t⟩
      have positive := card_pos.mpr ⟨_,m⟩
      omega
  exact not_common far (step p ax) by'

private theorem high_a_port_cost (hc : G.Connected) (far : 3≤G.dist a b)
    {x : V} (xp : x∈S.localA) (high : 5≤G.degree x) :
    5≤S.localA.card+(secondA G S.L a).card := by
  classical
  obtain ⟨xl,ax⟩ := mem_filter.mp xp
  have sub : G.neighborFinset x ⊆ insert a (S.localA.erase x ∪ secondA G S.L a) := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases left_boundary S x xl y xy with rfl|rfl|yl
    · simp
    · exact (not_common far ax xy.symm).elim
    apply mem_insert_of_mem
    by_cases ay : G.Adj a y
    · exact mem_union_left _ (mem_erase.mpr ⟨xy.ne.symm,mem_filter.mpr ⟨yl,ay⟩⟩)
    have ne : a≠y := fun e=>S.leftOff.1 (e.symm ▸ yl)
    exact mem_union_right _ (mem_inter.mpr ⟨yl,d2 hc ne ay ax xy⟩)
  have n := card_le_card sub
  rw [card_neighborFinset_eq_degree] at n
  have u := card_insert_le a (S.localA.erase x ∪ secondA G S.L a)
  have v := card_union_le (S.localA.erase x) (secondA G S.L a)
  rw [card_erase_of_mem xp] at v
  have pos := card_pos.mpr ⟨_,xp⟩
  omega

/-- If the opposite side supplies four a-ports, an internal mixed edge
forces an a-porter universal on this side. -/
theorem bridge_four_forces_universal (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (four : S.foreignA.card=4)
    {x y : V} (xl : x∈S.L) (ax : G.Adj a x) (xy : G.Adj x y) (by' : G.Adj b y) :
    ∀ z∈S.L,z=x ∨ G.Adj x z := by
  classical
  have xb : x≠b := fun e=>S.leftOff.2 (e ▸ xl)
  have b2 := d2 hc xb (fun e=>not_common far ax e.symm) xy by'.symm
  have bn : b∉S.foreignA := fun h=>S.rightOff.2 (mem_filter.mp h).1
  have sub : insert b S.foreignA ⊆ DistanceTwo G x := by
    intro z zz
    rcases mem_insert.mp zz with rfl|h
    · exact b2
    exact foreign_subset S hc xl ax h
  have cap := distanceTwo_le_of_even 5 x (even x)
  have eq := eq_of_subset_of_card_le sub (by rw [card_insert_of_not_mem bn,four]; exact cap)
  apply side_universal_if_no_local_d2 S hc xl
  intro z zl z2
  have ez := mem_insert.mp (eq.symm ▸ z2)
  rcases ez with rfl|zr
  · exact S.leftOff.2 zl
  exact disjoint_left.mp S.dis zl (mem_filter.mp zr).1

theorem bound_bridge_side_of_opposite_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (four : S.foreignA.card=4) (bridge : portBridge S) :
    S.L.card ≤ S.localA.card+4 := by
  classical
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
  have univ := bridge_four_forces_universal S hc far even four xl ax xy by'
  have sub : S.L⊆S.localA∪secondA G S.L a := by
    intro z zl
    by_cases az : G.Adj a z
    · exact mem_union_left _ (mem_filter.mpr ⟨zl,az⟩)
    have xz := (univ _ zl).resolve_left (fun e=>az (e.symm ▸ ax))
    have ne : a≠z := fun e=>S.leftOff.1 (e.symm ▸ zl)
    exact mem_union_right _ (mem_inter.mpr ⟨zl,d2 hc ne az ax xz⟩)
  have c := (card_le_card sub).trans (card_union_le _ _)
  have h := left_secondA_positive (switch S rightConnected rightA rightB) hc far
  change 1≤(secondA G S.R a).card at h
  have s := secondA_right_and_left_le_five S even
  omega

private theorem distance_to_b_ge_three_at_no_bridge (hc : G.Connected) (far : 3≤G.dist a b)
    (bridge : ¬portBridge S) {x : V} (xl : x∈S.L) (ax : G.Adj a x) :
    3≤G.dist x b := by
  have xb : x≠b := fun e=>S.leftOff.2 (e ▸ xl)
  have no : ¬G.Adj x b := fun e=>not_common far ax e.symm
  have lower := hc.one_lt_dist_of_ne_of_not_adj xb no
  apply Classical.byContradiction
  intro bad
  have eq : G.dist x b=2 := by omega
  obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x b
  obtain ⟨y,xy,yb⟩ := two_walk_middle q (ql.trans eq)
  rcases left_boundary S x xl y xy with rfl|rfl|yl
  · exact cut_not_adj far yb
  · exact no xy
  exact bridge ⟨x,xl,y,yl,ax,xy,yb.symm⟩

theorem no_bridge_four_foreign_cover (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (four : S.foreignA.card=4) (bridge : ¬portBridge S) :
    S.R⊆S.foreignA ∪ secondA G S.R a := by
  classical
  obtain ⟨x,xl,ax⟩ := S.leftA
  have low := distance_to_b_ge_three_at_no_bridge S hc far bridge xl ax
  have rad := (saturated_at_opposite_four S hc far even four xl ax).2
  intro y yr
  by_cases ay : G.Adj a y
  · exact mem_union_left _ (mem_filter.mpr ⟨yr,ay⟩)
  have yo : y∉S.L := fun h=>disjoint_left.mp S.dis h yr
  have d := cross_metric S.L hc xl yo (left_boundary S)
  have xa := dist_eq_one_iff_adj.mpr ax.symm
  have yz : b≠y := fun e=>S.rightOff.2 (e.symm ▸ yr)
  have pos : 0<G.dist b y := by
    have n : G.dist b y≠0 := fun e=>yz (hc.dist_eq_zero_iff.mp e)
    omega
  have d3 := rad y
  have ya : a≠y := fun e=>S.rightOff.1 (e.symm ▸ yr)
  have ge := hc.one_lt_dist_of_ne_of_not_adj ya ay
  exact mem_union_right _ (mem_inter.mpr ⟨yr,by simp [DistanceTwo,show G.dist a y=2 by omega]⟩)

theorem bound_no_bridge_side_of_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (four : S.foreignA.card=4)
    (bridge : ¬portBridge S) :
    S.R.card+(secondA G S.L a).card≤9 := by
  have s := (card_le_card (no_bridge_four_foreign_cover S hc far even four bridge)).trans (card_union_le _ _)
  have m := secondA_right_and_left_le_five S even
  omega

/-- If the four-port shore attains order eight without a mixed edge in
the other shore, a local a-port count below four forces a unique low
attachment of degree at most two. -/
theorem eight_no_bridge_forces_low_singleton (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (four : S.foreignA.card=4) (bridge : ¬portBridge S) (eight : S.R.card=8)
    (small : S.localA.card≤3) : ∃ x,S.localA={x} ∧ G.degree x≤2 := by
  classical
  have c := bound_no_bridge_side_of_four S hc far even four bridge
  have pos := left_secondA_positive S hc far
  obtain ⟨x,xl,ax⟩ := S.leftA
  have xp : x∈S.localA := mem_filter.mpr ⟨xl,ax⟩
  have low (y : V) (yp : y∈S.localA) : ¬5≤G.degree y := by
    intro hi
    have m := high_a_port_cost S hc far yp hi
    omega
  have single : S.localA={x} := by
    apply Subset.antisymm _ (singleton_subset_iff.mpr xp)
    intro z zp
    by_cases eq : z=x
    · simp [eq]
    exact (low _ xp ((degree z x eq).resolve_left (low _ zp))).elim
  refine ⟨x,single,?_⟩
  have sub : G.neighborFinset x ⊆ insert a (secondA G S.L a) := by
    intro y yy
    have xy := (mem_neighborFinset G x y).mp yy
    rcases left_boundary S x xl y xy with rfl|rfl|yl
    · simp
    · exact (not_common far ax xy.symm).elim
    apply mem_insert_of_mem
    have ay : ¬G.Adj a y := by
      intro ay
      have yp : y∈S.localA := mem_filter.mpr ⟨yl,ay⟩
      rw [single] at yp
      exact xy.ne (mem_singleton.mp yp).symm
    have ne : a≠y := fun e=>S.leftOff.1 (e.symm ▸ yl)
    exact mem_inter.mpr ⟨yl,d2 hc ne ay ax xy⟩
  have m := (card_le_card sub).trans (card_insert_le a _)
  rw [card_neighborFinset_eq_degree] at m
  omega

#print axioms foreign_a_ports_le_four
#print axioms bridge_four_forces_universal
#print axioms bound_bridge_side_of_opposite_four
#print axioms bound_no_bridge_side_of_four
#print axioms eight_no_bridge_forces_low_singleton
end Graffiti189LongestPath.CrossSaturation.Split.Five
