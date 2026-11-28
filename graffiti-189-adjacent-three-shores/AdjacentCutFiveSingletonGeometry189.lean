import AdjacentCutFiveSingletonDepth189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_hit_a shore_hit_b shore_disjoint from AdjacentCutFiveActual189
open private Vis from AdjacentCutFiveComponents189
open private mem_positive positive_card from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp := (CutGraph (G:=G) a b).ConnectedComponent

noncomputable def NearTwo (C : Cmp (G:=G) (a:=a) (b:=b)) : Finset V := by
  classical exact (Shore C).filter (fun z => depth G a b z = 2)

noncomputable def OddDepth (C : Cmp (G:=G) (a:=a) (b:=b)) : Finset V := by
  classical exact (Shore C).filter (fun z => depth G a b z ≠ 2)

theorem mem_near_two {C : Cmp (G:=G) (a:=a) (b:=b)} {z : V} :
    z∈NearTwo C ↔ z∈Shore C ∧ depth G a b z = 2 := by
  classical simp [NearTwo]

theorem mem_odd_depth {C : Cmp (G:=G) (a:=a) (b:=b)} {z : V} :
    z∈OddDepth C ↔ z∈Shore C ∧ depth G a b z ≠ 2 := by
  classical simp [OddDepth]

theorem shore_partition_depth (C : Cmp (G:=G) (a:=a) (b:=b)) :
    (NearTwo C).card + (OddDepth C).card = (Shore C).card := by
  classical
  have d : Disjoint (NearTwo C) (OddDepth C) := disjoint_left.mpr
    (fun _ h k => (mem_odd_depth.mp k).2 (mem_near_two.mp h).2)
  rw [←card_union_of_disjoint d]
  congr 1
  ext z
  by_cases h : depth G a b z=2 <;> simp [mem_near_two,mem_odd_depth,h]

theorem depth_pos_of_shore (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)}
    {z : V} (zc : z∈Shore C) : 0 < depth G a b z := by
  have da := hc.pos_dist_of_ne (fun e : a=z => (shore_off C).1 (by simpa only [← e] using zc))
  have db := hc.pos_dist_of_ne (fun e : b=z => (shore_off C).2 (by simpa only [← e] using zc))
  unfold depth
  omega

theorem vis_sub_odd (hc : G.Connected) (C : Cmp (G:=G) (a:=a) (b:=b)) :
    Vis C ⊆ OddDepth C := by
  classical
  intro z hz
  obtain ⟨zc,h⟩ := mem_filter.mp hz
  have e := depth_eq_one_of_port (a:=a) (b:=b) hc (fun e=>(shore_off C).1 (by simpa only [e] using zc))
    (fun e=>(shore_off C).2 (by simpa only [e] using zc)) h
  exact mem_odd_depth.mpr ⟨zc,by omega⟩

theorem dark_neighbors_in_shore (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)}
    {z : V} (zc : z∈Shore C) (d : depth G a b z ≠ 1) :
    G.neighborFinset z ⊆ (Shore C).erase z := by
  classical
  intro w hw
  have e := (mem_neighborFinset G z w).mp hw
  have za : z≠a := fun h=>(shore_off C).1 (by simpa only [h] using zc)
  have zb : z≠b := fun h=>(shore_off C).2 (by simpa only [h] using zc)
  rcases shore_closed C z zc w e with wa | wb | wc
  · have az : G.Adj a z := by simpa only [wa] using e.symm
    exact (d (depth_eq_one_of_port hc za zb (.inl az))).elim
  · have bz : G.Adj b z := by simpa only [wb] using e.symm
    exact (d (depth_eq_one_of_port hc za zb (.inr bz))).elim
  · exact mem_erase.mpr ⟨e.ne.symm,wc⟩

theorem high_shore_six_dark_common (hc : G.Connected) (ab : G.Adj a b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    {C : Cmp (G:=G) (a:=a) (b:=b)} (size : (Shore C).card = 6)
    {z : V} (zc : z∈Shore C) (zd : depth G a b z = 2) (hi : 5 ≤ G.degree z) :
    G.dist a z = 2 ∧ G.dist b z = 2 := by
  classical
  have sub := dark_neighbors_in_shore hc zc (by omega)
  have ncard : ((Shore C).erase z).card ≤ (G.neighborFinset z).card := by
    rw [card_neighborFinset_eq_degree]
    have c := card_erase_add_one zc
    omega
  have eq := eq_of_subset_of_card_le sub ncard
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab.ne conn C
  obtain ⟨y,yc,by'⟩ := shore_hit_b ab.ne conn C
  have xn : x ≠ z := by
    intro e
    subst x
    have k := depth_eq_one_of_port (a:=a) (b:=b) hc (fun h=>(shore_off C).1 (by simpa only [h] using xc))
      (fun h=>(shore_off C).2 (by simpa only [h] using xc)) (.inl ax)
    omega
  have yn : y ≠ z := by
    intro e
    subst y
    have k := depth_eq_one_of_port (a:=a) (b:=b) hc (fun h=>(shore_off C).1 (by simpa only [h] using yc))
      (fun h=>(shore_off C).2 (by simpa only [h] using yc)) (.inr by')
    omega
  have zx := (mem_neighborFinset G z x).mp (eq.symm ▸ mem_erase.mpr ⟨xn,xc⟩)
  have zy := (mem_neighborFinset G z y).mp (eq.symm ▸ mem_erase.mpr ⟨yn,yc⟩)
  have xa := G.dist_le (Walk.cons ax (Walk.cons zx.symm .nil))
  have yb := G.dist_le (Walk.cons by' (Walk.cons zy.symm .nil))
  simp at xa yb
  unfold depth at zd
  omega

theorem common_near_two_forbids_four_foreign (hc : G.Connected) (ab : G.Adj a b)
    (cap : ∀ x, (EvenFrom G x).card ≤ 6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (ne : C≠D)
    {z : V} (zc : z∈Shore C) (commonA : G.dist a z=2) (commonB : G.dist b z=2) :
    (NearTwo D).card ≤ 3 := by
  classical
  have outA : a ∉ NearTwo D := fun e=>(shore_off D).1 (mem_near_two.mp e).1
  have outB : b ∉ NearTwo D := fun e=>(shore_off D).2 (mem_near_two.mp e).1
  have sub : insert a (insert b (NearTwo D)) ⊆ PositiveEven G z := by
    intro w wk
    rcases mem_insert.mp wk with rfl|wk
    · exact mem_positive.mpr ⟨fun e=>(shore_off C).1 (by simpa only [← e] using zc),by rw [dist_comm,commonA]; decide⟩
    rcases mem_insert.mp wk with rfl|wk
    · exact mem_positive.mpr ⟨fun e=>(shore_off C).2 (by simpa only [← e] using zc),by rw [dist_comm,commonB]; decide⟩
    obtain ⟨wd,w2⟩ := mem_near_two.mp wk
    have dn := cross_metric (Shore C) hc zc
      (fun h=>disjoint_left.mp (shore_disjoint ne) h wd) (shore_closed C)
    rw [dist_comm (G:=G) (u:=z) (v:=a), dist_comm (G:=G) (u:=z) (v:=b),
      commonA, commonB] at dn
    unfold depth at w2
    have d4 : G.dist z w = 4 := by omega
    exact mem_positive.mpr ⟨fun e=>disjoint_left.mp (shore_disjoint ne) zc (by simpa only [e] using wd),by rw [d4]; decide⟩
  have cnt := card_le_card sub
  have ac : a∉insert b (NearTwo D) := by simp [ab.ne,outA]
  rw [card_insert_of_not_mem ac,card_insert_of_not_mem outB] at cnt
  have h := positive_card (cap z)
  omega

theorem exclusive_port_of_near_two (hc : G.Connected)
    {C : Cmp (G:=G) (a:=a) (b:=b)} {z : V} (zc : z∈Shore C)
    (dep2 : depth G a b z = 2) (za : G.dist a z = 2) (zb : G.dist b z ≠ 2) :
    ∃ w∈Shore C, G.Adj a w ∧ ¬G.Adj b w := by
  classical
  have dep : depth G a b z ≠ 1 := by omega
  obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist a z
  rw [za] at ql
  cases q with
  | nil => simp at ql
  | @cons x w y aw r =>
    cases r with
    | nil => simp at ql
    | @cons w t y wt s =>
      have nils : s.Nil := by
        rw [Walk.nil_iff_length_eq]
        simp at ql
        omega
      cases s with
      | nil =>
        have wc := (mem_erase.mp (dark_neighbors_in_shore hc zc dep
          ((mem_neighborFinset G z w).mpr wt.symm))).2
        refine ⟨w,wc,aw,?_⟩
        intro bw
        have k := G.dist_le (Walk.cons bw (Walk.cons wt .nil))
        have nz : b≠z := fun h=>(shore_off C).2 (by simpa only [← h] using zc)
        have notAdj : ¬G.Adj b z := fun e=>dep (by simp [depth,za,dist_eq_one_iff_adj.mpr e])
        have ge := hc.one_lt_dist_of_ne_of_not_adj nz notAdj
        simp at k
        exact zb (by omega)
      | cons e s => simp at nils

theorem exclusive_port_of_near_two_right (hc : G.Connected)
    {C : Cmp (G:=G) (a:=a) (b:=b)} {z : V} (zc : z∈Shore C)
    (dep2 : depth G a b z = 2) (za : G.dist b z = 2) (zb : G.dist a z ≠ 2) :
    ∃ w∈Shore C, G.Adj b w ∧ ¬G.Adj a w := by
  classical
  have dep : depth G a b z ≠ 1 := by omega
  obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist b z
  rw [za] at ql
  cases q with
  | nil => simp at ql
  | @cons x w y aw r =>
    cases r with
    | nil => simp at ql
    | @cons w t y wt s =>
      have nils : s.Nil := by
        rw [Walk.nil_iff_length_eq]
        simp at ql
        omega
      cases s with
      | nil =>
        have wc := (mem_erase.mp (dark_neighbors_in_shore hc zc dep
          ((mem_neighborFinset G z w).mpr wt.symm))).2
        refine ⟨w,wc,aw,?_⟩
        intro bw
        have k := G.dist_le (Walk.cons bw (Walk.cons wt .nil))
        have nz : a≠z := fun h=>(shore_off C).1 (by simpa only [← h] using zc)
        have notAdj : ¬G.Adj a z := fun e=>dep (by simp [depth,za,dist_eq_one_iff_adj.mpr e])
        have ge := hc.one_lt_dist_of_ne_of_not_adj nz notAdj
        simp at k
        exact zb (by omega)
      | cons e s => simp at nils

end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
