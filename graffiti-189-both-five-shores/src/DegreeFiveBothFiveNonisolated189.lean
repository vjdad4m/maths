import DegreeFiveBothFiveAll189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset ArticulationPair
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private residue residue_count from DegreeFiveBothFiveResidual189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- A residual vertex cannot be isolated after removing the unique
common porter in a saturated shore, if the other shore has a common
porter of its own. The bound is on distances in the original graph. -/
theorem one_common_residue_nonisolated_at_five
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C5 : (cutPorts C).card=5)
    (single : (sharedPortSet C).card=1)
    {x y : V} (xK : x∈sharedPortSet C)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y)
    (univ : ∀ w∈Shore C,x≠w → G.Adj x w) :
    ∀ z∈residue C,∃ w∈residue C,G.Adj z w := by
  classical
  let S := Shore C
  let K := sharedPortSet C
  let R := residue C
  have c5 : 5≤S.card := by rw [←C5]; exact card_le_card (filter_subset _ _)
  have k1 : K.card=1 := single
  have xk : x∈K := xK
  have keq : K={x} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr xk)
    (by simp [k1])).symm
  have count : R.card+K.card=S.card := residue_count C
  obtain ⟨xs',ax,bx⟩ := mem_filter.mp xK
  have xs : x∈S := xs'
  intro z zr
  apply Classical.byContradiction
  intro no
  have iso (w : V) (wr : w∈R) : ¬G.Adj z w := fun e=>no ⟨w,wr,e⟩
  obtain ⟨zs,zk⟩ := mem_sdiff.mp zr
  have zx : z≠x := fun e=>zk (e.symm ▸ xK)
  have xz : G.Adj x z := univ z zs zx.symm
  by_cases n : S.card=5
  · have rc : R.card=4 := by omega
    have pos : 2≤(R.erase z).card := by
      rw [card_erase_of_mem (show z∈R from zr),rc]
      decide
    obtain ⟨u,ur,v,vr,uv⟩ := one_lt_card.mp (show 1<(R.erase z).card by omega)
    obtain ⟨w,wr,hi⟩ : ∃ w∈R.erase z,5≤G.degree w := by
      rcases degree u v uv with h|h
      · exact ⟨u,ur,h⟩
      exact ⟨v,vr,h⟩
    obtain ⟨wz,wm⟩ := mem_erase.mp wr
    obtain ⟨ws',wk⟩ := mem_sdiff.mp wm
    have ws : w∈S := ws'
    have non : ¬(G.Adj a w ∧ G.Adj b w) := fun p=>wk (mem_filter.mpr ⟨ws,p⟩)
    have d : 4≤(inside G S w).card := inside_high_at_least_four_if_exclusive ws hi non
    have sub : inside G S w⊆S.erase w := by
      intro v vm
      obtain ⟨vs,wv⟩ := mem_filter.mp vm
      exact mem_erase.mpr ⟨wv.ne.symm,vs⟩
    have eq : inside G S w=S.erase w :=
      eq_of_subset_of_card_le sub (by rw [card_erase_of_mem ws]; omega)
    have zw : G.Adj w z := (mem_filter.mp (show z∈inside G S w by
      rw [eq]; exact mem_erase.mpr ⟨wz.symm,zs⟩)).2
    exact iso w wm zw.symm
  have s6 : 6≤S.card := by omega
  let W := (S.erase x).erase z
  have wout : W⊆S := (erase_subset _ _).trans (erase_subset _ _)
  have wD : W⊆DistanceTwo G z := by
    intro w wm
    obtain ⟨wz,wm'⟩ := mem_erase.mp wm
    obtain ⟨wx,ws⟩ := mem_erase.mp wm'
    have wr : w∈R := by
      apply mem_sdiff.mpr
      refine ⟨ws,?_⟩
      change w∉K
      rw [keq]
      exact fun h=>wx (mem_singleton.mp h)
    exact d2 hc wz.symm (iso w wr) xz.symm (univ w ws wx.symm)
  have cap (p q : V) (pq : p≠q) (po : p∉S) (qo : q∉S)
      (pd : p∈DistanceTwo G z) (qd : q∈DistanceTwo G z) : False := by
    have incl : insert p (insert q W)⊆DistanceTwo G z := by
      intro w wm
      rcases mem_insert.mp wm with rfl|wm
      · exact pd
      rcases mem_insert.mp wm with rfl|wm
      · exact qd
      exact wD wm
    have hp : p∉insert q W := fun h=>(mem_insert.mp h).elim pq (fun h=>po (wout h))
    have hq : q∉W := fun h=>qo (wout h)
    have k := (card_le_card incl).trans (distanceTwo_le_of_even 5 z (even z))
    have zS : z∈S.erase x := mem_erase.mpr ⟨zx,zs⟩
    have sizeW : W.card=S.card-2 := by
      change ((S.erase x).erase z).card=S.card-2
      rw [card_erase_of_mem zS,card_erase_of_mem xs]
      omega
    rw [card_insert_of_not_mem hp,card_insert_of_not_mem hq,sizeW] at k
    omega
  have ab : a≠b := by intro h; rw [h,SimpleGraph.dist_self] at two; omega
  have zy : z≠y := fun h=>disjoint_left.mp (shore_disjoint cd) zs (h.symm ▸ yd)
  have ny : ¬G.Adj z y := by
    intro e
    rcases shore_closed C z zs y e with rfl|rfl|yc
    · exact (shore_off D).1 yd
    · exact (shore_off D).2 yd
    exact disjoint_left.mp (shore_disjoint cd) yc yd
  have za : z≠a := fun h=>(shore_off C).1 (h ▸ zs)
  have zb : z≠b := fun h=>(shore_off C).2 (h ▸ zs)
  have yS : y∉S := fun h=>disjoint_left.mp (shore_disjoint cd) h yd
  have nba : ¬(G.Adj a z ∧ G.Adj b z) := fun p=>zk (mem_filter.mpr ⟨zs,p⟩)
  by_cases az : G.Adj a z
  · have bz : ¬G.Adj z b := fun e=>nba ⟨az,e.symm⟩
    exact cap b y (fun e=>(shore_off D).2 (e.symm ▸ yd)) (shore_off C).2 yS
      (d2 hc zb bz xz.symm bx.symm) (d2 hc zy ny az.symm ay)
  by_cases bz : G.Adj b z
  · exact cap a y (fun e=>(shore_off D).1 (e.symm ▸ yd)) (shore_off C).1 yS
      (d2 hc za (fun e=>az e.symm) xz.symm ax.symm) (d2 hc zy ny bz.symm by')
  exact cap a b ab (shore_off C).1 (shore_off C).2
    (d2 hc za (fun e=>az e.symm) xz.symm ax.symm)
    (d2 hc zb (fun e=>bz e.symm) xz.symm bx.symm)

#print axioms one_common_residue_nonisolated_at_five
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
