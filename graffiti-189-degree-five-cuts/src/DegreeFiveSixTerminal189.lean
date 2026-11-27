import DegreeFiveRouteTemplates189
import DegreeFiveUnbalancedShape189
import ActualDistThree189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common cut_not_adj from DegreeFiveFourPort189
open private tight_high_port_target_eq from DegreeFiveUnbalancedShape189
open private two_walk_middle from DistanceTwoCut189
open private left_can_root_at_one_cut from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

private theorem shell_nonport_of_no_bridge (hc : G.Connected) (far : 3≤G.dist a b)
    (no : ¬portBridge S) : secondA G S.L a ⊆ inner G S.L a b := by
  intro z ze
  obtain ⟨zl,z2⟩ := mem_inter.mp ze
  have es := (mem_filter.mp z2).2
  have az : ¬G.Adj a z := by intro e; have h := dist_eq_one_iff_adj.mpr e; omega
  have bz : ¬G.Adj b z := by
    intro e
    obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a z
    obtain ⟨w,aw,wz⟩ := two_walk_middle p (pl.trans es)
    rcases left_boundary S z zl w wz.symm with wa|wb|wl
    · exact aw.ne wa.symm
    · exact cut_not_adj far (wb ▸ aw)
    exact no ⟨w,wl,z,zl,aw,wz,e⟩
  exact mem_filter.mpr ⟨zl,az,bz⟩

private theorem port_clique_at_tight (hc : G.Connected) (far : 3≤G.dist a b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (tight : S.localA.card+(secondA G S.L a).card=5) : CompleteOn G S.localA := by
  intro x xp y yp xy
  have use (u v : V) (up : u∈S.localA) (vp : v∈S.localA) (uv : u≠v)
      (high : 5≤G.degree u) : G.Adj u v := by
    have e := tight_high_port_target_eq S hc far up high tight
    have z : v∈G.neighborFinset u := by
      rw [e]
      exact mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨uv.symm,vp⟩))
    exact (mem_neighborFinset _ _ _).mp z
  rcases degree x y xy with h|h
  · exact use _ _ xp yp xy h
  exact (use _ _ yp xp xy.symm h).symm

private theorem port_sees_shell_at_tight (hc : G.Connected) (far : 3≤G.dist a b)
    (tight : S.localA.card+(secondA G S.L a).card=5)
    (x : V) (xp : x∈S.localA) (high : 5≤G.degree x)
    (z : V) (ze : z∈secondA G S.L a) : G.Adj x z := by
  have e := tight_high_port_target_eq S hc far xp high tight
  have z : z∈G.neighborFinset x := by rw [e]; exact mem_insert_of_mem (mem_union_right _ ze)
  exact (mem_neighborFinset _ _ _).mp z

private theorem inner_neighbors_if_not_foreign_shell (hc : G.Connected)
    {z : V} (zi : z∈inner G S.L a b) (zf : z∉secondA G S.L b) :
    G.neighborFinset z ⊆ S.localA∪(inner G S.L a b).erase z := by
  obtain ⟨zl,az,bz⟩ := mem_filter.mp zi
  intro w wn
  have zw := (mem_neighborFinset G z w).mp wn
  rcases left_boundary S z zl w zw with rfl|rfl|wl
  · exact (az zw.symm).elim
  · exact (bz zw.symm).elim
  by_cases aw : G.Adj a w
  · exact mem_union_left _ (mem_filter.mpr ⟨wl,aw⟩)
  by_cases bw : G.Adj b w
  · have ne : b≠z := fun h=>S.leftOff.2 (h.symm ▸ zl)
    exact (zf (mem_inter.mpr ⟨zl,d2 hc ne bz bw zw.symm⟩)).elim
  exact mem_union_right _ (mem_erase.mpr ⟨zw.ne.symm,mem_filter.mpr ⟨wl,aw,bw⟩⟩)

private theorem inner_neighbors_if_deep (hc : G.Connected)
    {z : V} (zi : z∈inner G S.L a b) (ze : z∉secondA G S.L a) (zf : z∉secondA G S.L b) :
    G.neighborFinset z ⊆ (inner G S.L a b).erase z := by
  intro w wn
  rcases mem_union.mp (inner_neighbors_if_not_foreign_shell S hc zi zf wn) with wa|wm
  · obtain ⟨zl,az,_⟩ := mem_filter.mp zi
    have ne : a≠z := fun h=>S.leftOff.1 (h.symm ▸ zl)
    have wz := ((mem_neighborFinset _ _ _).mp wn).symm
    exact (ze (mem_inter.mpr ⟨zl,d2 hc ne az (mem_filter.mp wa).2 wz⟩)).elim
  exact wm

/-- A tight three-plus-three shore of order at most nine has a spanning
route from an a-porter to a b-porter. Its nonporters use the two- and
three-vertex templates, without editing any ambient-graph edge. -/
theorem six_port_shore_has_terminal_route (hc : G.Connected) (far : 3≤G.dist a b)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (minimum : ∀ z : V,2≤G.degree z)
    (a3 : S.localA.card=3) (b3 : (S.L.filter (G.Adj b)).card=3)
    (ta : S.localA.card+(secondA G S.L a).card=5)
    (tb : (S.L.filter (G.Adj b)).card+(secondA G S.L b).card=5)
    (small : S.L.card≤9) :
    RouteOn G (insert a (insert b S.L)) a b := by
  classical
  let T := S.flip
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let I := inner G S.L a b
  let E := secondA G S.L a
  let F := secondA G S.L b
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have no := no_mixed_three_three S hc far degree a3 b3 ta tb
  have no' : ¬portBridge T := by
    rintro ⟨x,xl,y,yl,bx,xy,ay⟩
    exact no ⟨y,yl,x,xl,ay,xy.symm,bx⟩
  have eI : E⊆I := shell_nonport_of_no_bridge S hc far no
  have fI : F⊆I := by
    intro z zf
    have sub := shell_nonport_of_no_bridge T hc far' no' zf
    obtain ⟨zl,bz,az⟩ := mem_filter.mp sub
    exact mem_filter.mpr ⟨zl,az,bz⟩
  have e2 : E.card=2 := by
    change A.card+E.card=5 at ta
    change A.card=3 at a3
    omega
  have f2 : F.card=2 := by
    change B.card+F.card=5 at tb
    change B.card=3 at b3
    omega
  have ac : CompleteOn G A := port_clique_at_tight S hc far degree ta
  have bc : CompleteOn G B := port_clique_at_tight T hc far' degree tb
  have aN : ∀ x∈A,5≤G.degree x → ∀ z∈E,G.Adj x z := port_sees_shell_at_tight S hc far ta
  have bN : ∀ x∈B,5≤G.degree x → ∀ z∈F,G.Adj x z := port_sees_shell_at_tight T hc far' tb
  have ab : Disjoint A B := by
    apply disjoint_left.mpr
    intro z az bz
    exact not_common far (mem_filter.mp az).2 (mem_filter.mp bz).2
  have ai : Disjoint A I := by
    apply disjoint_left.mpr
    intro z az zi
    exact (mem_filter.mp zi).2.1 (mem_filter.mp az).2
  have bi : Disjoint B I := by
    apply disjoint_left.mpr
    intro z bz zi
    exact (mem_filter.mp zi).2.2 (mem_filter.mp bz).2
  have covered : (A∪I)∪B=S.L := by
    ext v
    constructor
    · intro h
      rcases mem_union.mp h with h|h
      · rcases mem_union.mp h with h|h
        · exact (mem_filter.mp h).1
        exact (mem_filter.mp h).1
      exact (mem_filter.mp h).1
    intro h
    by_cases av : G.Adj a v
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨h,av⟩))
    by_cases bv : G.Adj b v
    · exact mem_union_right _ (mem_filter.mpr ⟨h,bv⟩)
    exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨h,av,bv⟩))
  have count := congrArg Finset.card covered
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨ab,bi.symm⟩),
    card_union_of_disjoint ai] at count
  change A.card=3 at a3
  change B.card=3 at b3
  have i3 : I.card≤3 := by omega
  have i2 : 2≤I.card := by have h := card_le_card eI; omega
  have route : ∃ l∈A,∃ r∈B,RouteOn G ((A∪I)∪B) l r := by
    by_cases iTwo : I.card=2
    · have ei' := eq_of_subset_of_card_le eI (by omega)
      have fi' := eq_of_subset_of_card_le fI (by omega)
      exact six_port_two_inner_route A B I a3 b3 iTwo ac bc ab ai bi degree
        (by simpa only [ei'] using aN) (by simpa only [fi'] using bN)
    have iThree : I.card=3 := by omega
    apply six_port_three_inner_route A B I E F a3 b3 iThree e2 f2 eI fI ac bc ab ai bi degree
      (fun z _=>minimum z) aN bN
    · exact fun z zi ze zf=>inner_neighbors_if_deep S hc zi ze zf
    · exact fun z ze zf=>inner_neighbors_if_not_foreign_shell S hc (eI ze) zf
    intro z zf ze
    have zi : z∈inner G T.L b a := by
      obtain ⟨zl,az,bz⟩ := mem_filter.mp (fI zf)
      exact mem_filter.mpr ⟨zl,bz,az⟩
    have m := inner_neighbors_if_not_foreign_shell T hc zi ze
    have eqI : inner G T.L b a=I := by
      change inner G S.L b a = inner G S.L a b
      ext v
      simp [inner,and_comm]
    rw [eqI] at m
    exact m
  obtain ⟨l,lm,r,rm,path⟩ := route
  rw [covered] at path
  have al := (mem_filter.mp lm).2
  have rb := (mem_filter.mp rm).2.symm
  have cb : b∉insert a S.L := by
    intro h
    rcases mem_insert.mp h with h|h
    · rw [h,SimpleGraph.dist_self] at far; omega
    exact S.leftOff.2 h
  have q := (path.prefix al S.leftOff.1).suffix rb cb
  simpa only [insert_comm] using q

#print axioms six_port_shore_has_terminal_route
end Graffiti189LongestPath.CrossSaturation.Split.Five
