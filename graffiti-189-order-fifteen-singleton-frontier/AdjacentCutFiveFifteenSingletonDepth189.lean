import AdjacentCutFiveFifteenSingletonProfiles189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed from AdjacentCutFiveActual189
open private key classSet key_facts from AdjacentCutFiveTopProfiles189
open private restrict_unique_profile from AdjacentCutFiveSixteenSingletonGeometry189
open private d2 from AdjacentCutFiveBound189
open private predecessor_of_positive_dist left_even_depth_two_with_one_exclusive from AdjacentCutFiveSixteenSingletonDepth189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem balanced_odd_depth_le_three_of_empty_equal_even_one_left
    (hc : G.Connected) (ab : G.Adj a b) {D : Cmp G a b}
    (zero : (classSet D 2).card=0) (one : (classSet D 3).card=1)
    {z : V} (zd : z∈Shore D) (k : key G a b z=5) : G.dist a z≤3 := by
  obtain ⟨az,bz,ez⟩ := key_facts hc ab z
  rw [k] at az bz ez
  change G.dist a z=depth G a b z+0 at az
  change G.dist b z=depth G a b z+0 at bz
  change depth G a b z % 2=1 at ez
  by_contra bad
  have large : 5≤G.dist a z := by omega
  have pz : 0<G.dist z a := by rw [dist_comm]; omega
  obtain ⟨w,zw,hw⟩ := predecessor_of_positive_dist hc pz
  rw [dist_comm (G:=G) (u:=z) (v:=a),dist_comm (G:=G) (u:=w) (v:=a)] at hw
  have wd : w∈Shore D := by
    rcases shore_closed D z zd w zw with q|q|q
    · have h := dist_eq_one_iff_adj.mpr zw
      rw [q, dist_comm] at h
      omega
    · have h := dist_eq_one_iff_adj.mpr zw
      rw [q, dist_comm] at h
      omega
    · exact q
  have lower := hc.dist_triangle (u:=b) (v:=w) (w:=z)
  rw [dist_eq_one_iff_adj.mpr zw.symm] at lower
  have aw_even : Even (G.dist a w) := by rw [Nat.even_iff]; omega
  have aw_le_bw : G.dist a w≤G.dist b w := by omega
  rcases lt_or_eq_of_le aw_le_bw with lt|eq
  · have kw : key G a b w=0 := by simp [key,lt,aw_even]
    have e := left_even_depth_two_with_one_exclusive hc ab one wd kw
    omega
  · have kw : key G a b w=2 := by simp [key,eq,eq ▸ aw_even]
    have pos := Finset.card_pos.mpr (show (classSet D 2).Nonempty from ⟨w,mem_filter.mpr ⟨wd,kw⟩⟩)
    omega

#print axioms balanced_odd_depth_le_three_of_empty_equal_even_one_left

/-- With only one A-odd vertex and no balanced-even vertices, four B-even vertices
and two B-odd vertices cannot accommodate a B-even vertex at depth ≥4. -/
theorem right_even_depth_two_of_adjacent_singleton_twelve_profile
    (hc : G.Connected) (ab : G.Adj a b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) {s : V} (single : Shore C={s})
    (al : 0<(classSet D 0).card) (br : (classSet D 1).card=4)
    (zero : (classSet D 2).card=0) (one : (classSet D 3).card=1)
    (two : (classSet D 4).card=2) {z : V} (zd : z∈Shore D) (k : key G a b z=1) :
    G.dist b z=2 := by
  classical
  obtain ⟨az,bz,ez⟩ := key_facts hc ab z
  rw [k] at az bz ez
  change G.dist a z=depth G a b z+1 at az
  change G.dist b z=depth G a b z+0 at bz
  change depth G a b z % 2=0 at ez
  have zB : z≠b := fun e=>(shore_off D).2 (e ▸ zd)
  have nz := hc.pos_dist_of_ne zB.symm
  by_contra bad
  have tall : 4≤G.dist b z := by omega
  obtain ⟨v,vm⟩ := Finset.card_pos.mp al
  obtain ⟨vd,kv⟩ := mem_filter.mp vm
  obtain ⟨av,bv,_⟩ := key_facts hc ab v
  rw [kv] at av bv
  change G.dist a v=depth G a b v+0 at av
  change G.dist b v=depth G a b v+1 at bv
  obtain ⟨x,xd,ax,nx⟩ := exclusive_left_port_of_strictly_nearer hc vd (by omega)
  obtain ⟨y,yd,by',ny⟩ := exclusive_right_port_of_strictly_nearer hc zd (by omega)
  have xB : x≠b := fun e=>(shore_off D).2 (e ▸ xd)
  have yA : y≠a := fun e=>(shore_off D).1 (e ▸ yd)
  have dxB := (mem_filter.mp (d2 hc xB.symm nx ab.symm ax)).2
  have dyA := (mem_filter.mp (d2 hc yA.symm ny ab by')).2
  have xk : key G a b x=3 := by simp [key,dist_eq_one_iff_adj.mpr ax,dxB]
  have yk : key G a b y=4 := by simp [key,dist_eq_one_iff_adj.mpr by',dyA]
  have X := restrict_unique_profile one xd xk
  have sub : G.neighborFinset z⊆ (classSet D 1).erase z ∪ (classSet D 4).erase y := by
    intro w wm
    have zw := (SimpleGraph.mem_neighborFinset G z w).mp wm
    have ta := hc.dist_triangle (u:=a) (v:=w) (w:=z)
    have tb := hc.dist_triangle (u:=b) (v:=w) (w:=z)
    rw [dist_eq_one_iff_adj.mpr zw.symm] at ta tb
    have wd : w∈Shore D := by
      rcases shore_closed D z zd w zw with q|q|q
      · rw [q,dist_self] at ta; omega
      · rw [q,dist_self] at tb; omega
      · exact q
    rcases (by decide : ∀ i : Fin 6,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5) (key G a b w) with i|i|i|i|i|i
    · have dist := left_even_depth_two_with_one_exclusive hc ab one wd i
      omega
    · exact mem_union_left _ (mem_erase.mpr ⟨zw.ne.symm,mem_filter.mpr ⟨wd,i⟩⟩)
    · have pos := card_pos.mpr (show (classSet D 2).Nonempty from ⟨w,mem_filter.mpr ⟨wd,i⟩⟩)
      omega
    · have h : w∈classSet D 3 := mem_filter.mpr ⟨wd,i⟩
      have wx : w=x := by simpa [X] using h
      rw [wx,dist_eq_one_iff_adj.mpr ax] at ta
      omega
    · have wy : w≠y := by
        intro h
        rw [h,dist_eq_one_iff_adj.mpr by'] at tb
        omega
      exact mem_union_right _ (mem_erase.mpr ⟨wy,mem_filter.mpr ⟨wd,i⟩⟩)
    · have dist := balanced_odd_depth_le_three_of_empty_equal_even_one_left hc ab zero one wd i
      omega
  have bzmem : z∈classSet D 1 := mem_filter.mpr ⟨zd,k⟩
  have bymem : y∈classSet D 4 := mem_filter.mpr ⟨yd,yk⟩
  have u := (card_le_card sub).trans (card_union_le _ _)
  rw [SimpleGraph.card_neighborFinset_eq_degree,card_erase_of_mem bzmem, card_erase_of_mem bymem,br,two] at u
  have h := high_of_other_shore_singleton degree cd single zd
  omega

#print axioms right_even_depth_two_of_adjacent_singleton_twelve_profile
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
