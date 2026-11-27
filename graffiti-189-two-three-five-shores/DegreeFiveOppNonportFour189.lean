import DegreeFiveThreeFiveDom189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private d2 from CrossSaturation189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private graph_order_le_shores_add_two from DegreeFiveBothNonsaturated189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Nonporters on different sides of a two-cut are at distance at least
four, even when the two cut vertices are adjacent. -/
theorem opposite_nonporters_dist_at_least_four
    (hc : G.Connected) {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {z w : V} (zc : z∈Shore C) (wd : w∈Shore D)
    (zn : z∉cutPorts C) (wn : w∉cutPorts D) :
    4≤G.dist z w := by
  classical
  have left {u : V} (zu : G.Adj z u) : u∈Shore C := by
    rcases shore_closed C z zc u zu with rfl|rfl|h
    · exact (zn (mem_filter.mpr ⟨zc,.inl zu.symm⟩)).elim
    · exact (zn (mem_filter.mpr ⟨zc,.inr zu.symm⟩)).elim
    exact h
  have right {v : V} (wv : G.Adj w v) : v∈Shore D := by
    rcases shore_closed D w wd v wv with rfl|rfl|h
    · exact (wn (mem_filter.mpr ⟨wd,.inl wv.symm⟩)).elim
    · exact (wn (mem_filter.mpr ⟨wd,.inr wv.symm⟩)).elim
    exact h
  have cross {u v : V} (uc : u∈Shore C) (vd : v∈Shore D) : ¬G.Adj u v := by
    intro h
    rcases shore_closed C u uc v h with rfl|rfl|vc
    · exact (shore_off D).1 vd
    · exact (shore_off D).2 vd
    exact disjoint_left.mp (shore_disjoint cd) vc vd
  have notShort {s t : V} (p : G.Walk s t) (sd : s=z) (td : t=w) : 4≤p.length := by
    by_contra! small
    cases p with
    | nil =>
      have zw := sd.symm.trans td
      exact disjoint_left.mp (shore_disjoint cd) zc (zw.symm ▸ wd)
    | @cons s u t e p =>
      subst s
      have uc := left e
      simp only [length_cons] at small
      cases p with
      | nil => exact cross zc (td.symm ▸ wd) e
      | @cons u v t f p =>
        simp only [length_cons] at small
        cases p with
        | nil =>
          have edge : G.Adj w u := td ▸ f.symm
          exact disjoint_left.mp (shore_disjoint cd) uc (right edge)
        | @cons v q t g p =>
          simp only [length_cons] at small
          cases p with
          | nil =>
            have edge := g.symm
            rw [td] at edge
            exact cross uc (right edge) f
          | cons h p =>
            simp only [length_cons] at small
            omega
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist z w
  exact hp ▸ notShort p rfl rfl

#print axioms opposite_nonporters_dist_at_least_four
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
