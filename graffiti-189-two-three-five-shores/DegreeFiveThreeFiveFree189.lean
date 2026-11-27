import DegreeFiveThreeFiveShapes189
import RootedOreMissingPair189
import WingSignature189
import DegreeFiveBothFiveResidual189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private inside_high_at_least_four_if_exclusive inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff from DegreeFiveBothFiveResidual189
open private shore_connected from DegreeFiveActualCut189
open private lift_side_path from DegreeFiveSmallSides189
open ArticulationPair
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem poor_degree_has_far_low
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C3 : (cutPorts C).card=3)
    (big : 7≤(Shore D).card) (small : (Shore D).card≤8)
    {u : V} (ud : u∈Shore D) (high : 5≤G.degree u) (deg : (inside G (Shore D) u).card=3) :
    ∃ z∈Shore D,3≤G.dist u z ∧ G.degree z+5≤(Shore D).card ∧
      G.neighborFinset z⊆((Shore D).erase u \ inside G (Shore D) u).erase z := by
  classical
  have shared : G.Adj a u ∧ G.Adj b u := by
    apply Classical.byContradiction
    intro h
    have t := inside_high_at_least_four_if_exclusive ud high h
    omega
  let W := (Shore D).erase u \ inside G (Shore D) u
  have insideSub : inside G (Shore D) u⊆(Shore D).erase u := by
    intro z hz
    obtain ⟨zd,uz⟩ := mem_filter.mp hz
    exact mem_erase.mpr ⟨uz.ne.symm,zd⟩
  have count : W.card+4=(Shore D).card := by
    have p : W.card+(inside G (Shore D) u).card=((Shore D).erase u).card :=
      card_sdiff_add_card_eq_card insideSub
    rw [card_erase_of_mem ud,deg] at p
    omega
  have cross {w : V} (wc : w∈Shore C) : ¬G.Adj u w := by
    intro e
    rcases shore_closed D u ud w e with rfl|rfl|wd
    · exact (shore_off C).1 wc
    · exact (shore_off C).2 wc
    exact disjoint_left.mp (shore_disjoint cd) wc wd
  have extSub : cutPorts C⊆DistanceTwo G u := by
    intro w wp
    obtain ⟨wc,h⟩ := mem_filter.mp wp
    have uw : u≠w := fun e=>disjoint_left.mp (shore_disjoint cd) wc (e ▸ ud)
    exact h.elim (fun e=>d2 hc uw (cross wc) shared.1.symm e)
      (fun e=>d2 hc uw (cross wc) shared.2.symm e)
  have wD : W⊆Shore D := fun _ h=>mem_of_mem_erase (mem_sdiff.mp h).1
  have noAdj {w : V} (ww : w∈W) : ¬G.Adj u w := fun e=>
    (mem_sdiff.mp ww).2 (mem_filter.mpr ⟨wD ww,e⟩)
  have wNe {w : V} (ww : w∈W) : w≠u := (mem_erase.mp (mem_sdiff.mp ww).1).1
  have far : ∃ z∈W,3≤G.dist u z := by
    apply Classical.byContradiction
    intro h
    have localSub : W⊆DistanceTwo G u := by
      intro w ww
      have lo := hc.one_lt_dist_of_ne_of_not_adj (wNe ww).symm (noAdj ww)
      have notfar : ¬3≤G.dist u w := fun e=>h ⟨w,ww,e⟩
      have eq : G.dist u w=2 := by omega
      simp [DistanceTwo,eq]
    have dis := (shore_disjoint cd).mono (show cutPorts C⊆Shore C from filter_subset _ _) wD
    have cap := (card_le_card (union_subset extSub localSub)).trans
      (distanceTwo_le_of_even 5 u (even u))
    rw [card_union_of_disjoint dis,C3] at cap
    omega
  obtain ⟨z,zw,z3⟩ := far
  have zd := wD zw
  have notport : ¬G.Adj a z ∧ ¬G.Adj b z := by
    constructor
    · intro az
      have inz := d2 hc (wNe zw).symm (noAdj zw) shared.1.symm az
      have e : G.dist u z=2 := by simpa [DistanceTwo] using inz
      omega
    intro bz
    have inz := d2 hc (wNe zw).symm (noAdj zw) shared.2.symm bz
    have e : G.dist u z=2 := by simpa [DistanceTwo] using inz
    omega
  have nz : G.neighborFinset z⊆W.erase z := by
    intro w h
    have adj := (mem_neighborFinset G z w).mp h
    have wd : w∈Shore D := by
      rcases shore_closed D z zd w adj with rfl|rfl|wd
      · exact (notport.1 adj.symm).elim
      · exact (notport.2 adj.symm).elim
      exact wd
    have wu : w≠u := fun e=>noAdj zw (e ▸ adj.symm)
    have notAdj : ¬G.Adj u w := by
      intro uw
      have d := G.dist_le (SimpleGraph.Walk.cons uw adj.symm.toWalk)
      simp at d
      omega
    exact mem_erase.mpr ⟨adj.ne.symm,mem_sdiff.mpr ⟨mem_erase.mpr ⟨wu,wd⟩,
      fun m=>notAdj (mem_filter.mp m).2⟩⟩
  have bounds := card_le_card nz
  rw [card_neighborFinset_eq_degree,card_erase_of_mem zw] at bounds
  have pos : 0<W.card := card_pos.mpr ⟨z,zw⟩
  exact ⟨z,zd,z3,by omega,nz⟩

private theorem bound_missing_pair_on_small_five_shore
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (min2 : ∀ u : V,2≤G.degree u)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C3 : (cutPorts C).card=3)
    (small : (Shore D).card≤7 ∨ ((Shore D).card≤8 ∧ ∀ w∈Shore D,5≤G.degree w))
    {u v : V} (ud : u∈Shore D) (vd : v∈Shore D)
    (uh : 5≤G.degree u) (vh : 5≤G.degree v) (uv : u≠v) (no : ¬G.Adj u v) :
    (Shore D).card≤(inside G (Shore D) u).card+(inside G (Shore D) v).card := by
  classical
  have u3 := inside_high_at_least_three ud uh
  have v3 := inside_high_at_least_three vd vh
  have big8 : (Shore D).card≤8 := small.elim (fun h=>by omega) And.left
  apply Classical.byContradiction
  intro fail
  have big7 : 7≤(Shore D).card := by omega
  rcases small with s7|⟨s8,high⟩
  · have a3 : (inside G (Shore D) u).card=3 := by omega
    have b3 : (inside G (Shore D) v).card=3 := by omega
    obtain ⟨z,zd,uz,zLow,zSub⟩ := poor_degree_has_far_low hc even cd C3 big7 big8 ud uh a3
    obtain ⟨w,wd,vw,wLow,wSub⟩ := poor_degree_has_far_low hc even cd C3 big7 big8 vd vh b3
    have eq : z=w := by
      apply Classical.byContradiction
      intro h
      exact (degree z w h).elim (fun h=>by omega) (fun h=>by omega)
    subst w
    let M := (Shore D).erase u \ inside G (Shore D) u
    have count : M.card=3 := by
      have sub : inside G (Shore D) u⊆(Shore D).erase u := by
        intro t ht
        obtain ⟨td,ut⟩ := mem_filter.mp ht
        exact mem_erase.mpr ⟨ut.ne.symm,td⟩
      have p : M.card+(inside G (Shore D) u).card=((Shore D).erase u).card :=
        card_sdiff_add_card_eq_card sub
      rw [card_erase_of_mem ud,a3] at p
      omega
    have zM : z∈M := by
      refine mem_sdiff.mpr ⟨mem_erase.mpr ⟨?_,zd⟩,?_⟩
      · intro h; rw [h,dist_self] at uz; omega
      intro h
      have d := dist_eq_one_iff_adj.mpr (mem_filter.mp h).2
      omega
    have vM : v∈M := mem_sdiff.mpr ⟨mem_erase.mpr ⟨uv.symm,vd⟩,
      fun h=>no (mem_filter.mp h).2⟩
    have vz : v≠z := by
      intro h; rw [h,dist_self] at vw; omega
    have vNo : v∉G.neighborFinset z := by
      intro h
      have d := dist_eq_one_iff_adj.mpr ((mem_neighborFinset G z v).mp h).symm
      omega
    have zNo : z∉G.neighborFinset z := by simp
    have sub : insert v (insert z (G.neighborFinset z))⊆M := by
      intro t ht
      rcases mem_insert.mp ht with rfl|ht
      · exact vM
      rcases mem_insert.mp ht with rfl|ht
      · exact zM
      exact mem_of_mem_erase (zSub ht)
    have n := card_le_card sub
    rw [card_insert_of_not_mem (show v∉insert z (G.neighborFinset z) by simp [vz,vNo]),
      card_insert_of_not_mem zNo,card_neighborFinset_eq_degree,count] at n
    have zz := min2 z
    omega
  have short : (inside G (Shore D) u).card=3 ∨ (inside G (Shore D) v).card=3 := by omega
  rcases short with h|h
  · obtain ⟨z,zd,_,hz,_⟩ := poor_degree_has_far_low hc even cd C3 big7 big8 ud uh h
    have q := high z zd
    omega
  obtain ⟨z,zd,_,hz,_⟩ := poor_degree_has_far_low hc even cd C3 big7 big8 vd vh h
  have q := high z zd
  omega

theorem free_route_on_five_port_side_opposite_three
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (min2 : ∀ u : V,2≤G.degree u)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C3 : (cutPorts C).card=3) (D5 : (cutPorts D).card=5)
    (small : (Shore D).card≤7 ∨ ((Shore D).card≤8 ∧ ∀ w∈Shore D,5≤G.degree w)) :
    WingRealizes G a b (Shore D) .aFree ∨ WingRealizes G a b (Shore D) .bFree := by
  classical
  let S := Shore D
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let A : Finset U := univ.filter (fun u=>u.val∈cutPorts D)
  let high (u : U) := 5≤G.degree u.val
  have inA (u : U) : u∈A ↔ u.val∈cutPorts D := by simp [A]
  have size : A.card=5 := by
    rw [←D5]
    apply card_bij (fun u _=>u.val)
    · intro u h
      exact (inA u).mp h
    · intro u _ v _ e
      exact Subtype.ext e
    intro v vp
    exact ⟨⟨v,(cut_mem_iff.mp vp).1⟩,(inA _).mpr vp,rfl⟩
  have pair (u v : U) (uv : u≠v) : high u ∨ high v :=
    degree u.val v.val (fun e=>uv (Subtype.ext e))
  have cap (u v : U) (hu : high u) (hv : high v) (uv : u≠v)
      (_ : ¬(u∈(∅ : Finset U) ∧ v∈(∅ : Finset U))) (no : ¬J.Adj u v) :
      Fintype.card U≤J.degree u+J.degree v := by
    have h := bound_missing_pair_on_small_five_shore hc even degree min2 cd C3 small
      u.property v.property hu hv (fun e=>uv (Subtype.ext e)) no
    have n : Fintype.card U=S.card := Fintype.card_coe S
    rw [n]
    change S.card≤(G.induce (↑S : Set V)).degree u+(G.induce (↑S : Set V)).degree v
    rw [←inside_card_eq_degree_induce (G:=G) S u,←inside_card_eq_degree_induce (G:=G) S v]
    exact h
  obtain ⟨r,ra,t,p,pp,ps⟩ := rooted_Ore_missing_except_pair (shore_connected D) A ∅
    (by omega) (by simp) (.inl (by simp)) high pair cap
  have route : RouteOn G S r.val t.val := lift_side_path S p pp ps
  rcases (cut_mem_iff.mp ((inA r).mp ra)).2 with ar|br
  · exact .inl ⟨r.val,t.val,ar,route⟩
  exact .inr ⟨r.val,t.val,br,route⟩

#print axioms free_route_on_five_port_side_opposite_three
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
