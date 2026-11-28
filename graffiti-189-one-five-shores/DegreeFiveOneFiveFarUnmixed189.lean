import DegreeFiveOneFiveFarRoutesBase189
import SmallDenseRoute189
import SixSpecialRoute189
import DegreeFiveOneFiveFarGlue189
import LowProtectedRoot189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open ArticulationPair
open private inside_high_at_least_three inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

namespace OneFiveFarProfile
variable {D : Cmp (G:=G) (a:=a) (b:=b)} (S : OneFiveFarProfile D)
open private F LS shore_split from DegreeFiveOneFiveFarRoutesBase189
open private lift_side_path from DegreeFiveSmallSides189

private theorem shared_lim 
    (satA : S.L.card+S.M.card=4) (satB : S.R.card+S.M.card=4)
    {z : V} (zt : z∈S.T) :
    inside G (Shore D) z⊆(S.T.erase z)∪S.M := by
  intro w wm
  obtain ⟨wd,zw⟩ := mem_filter.mp wm
  obtain ⟨zd,za,zb⟩ := S.both_of_mem_T zt
  rcases S.shore_split wd with we|wf|wt|wl|wr|wm
  · exact (S.e_excluded satB z (mem_filter.mpr ⟨zd,zb⟩) (we ▸ zw.symm)).elim
  · exact (S.f_excluded satA z (mem_filter.mpr ⟨zd,za⟩) (wf ▸ zw.symm)).elim
  · exact mem_union_left _ (mem_erase.mpr ⟨zw.ne.symm,wt⟩)
  · exact (S.no_shared_to_single zt (mem_union_left _ wl) zw).elim
  · exact (S.no_shared_to_single zt (mem_union_right _ wr) zw).elim
  exact mem_union_right _ wm

private theorem shared_route_if_six
    (high : ∀ v∈Shore D,5≤G.degree v)
    (mode : S.M.card=0 ∨ (S.M.card=2 ∧ S.L.card=2 ∧ S.R.card=2)) :
    ∃ x∈S.T,∃ y∈S.T,RouteOn G S.T x y := by
  classical
  apply three_finset_spanning_path S.T S.T_card
  intro z zt
  obtain ⟨zd,za,zb⟩ := S.both_of_mem_T zt
  have lo := inside_high_at_least_three zd (high z zd)
  apply Classical.byContradiction
  intro no
  rcases mode with empty|⟨m2,l2,r2⟩
  · have M0 : S.M=∅ := card_eq_zero.mp empty
    have sub : inside G (Shore D) z⊆({S.e,S.f} : Finset V) := by
      intro w h
      obtain ⟨wd,zw⟩ := mem_filter.mp h
      rcases S.shore_split wd with h|h|h|h|h|h
      · simp [h]
      · simp [h]
      · exact (no ⟨w,h,zw⟩).elim
      · exact (S.no_shared_to_single zt (mem_union_left _ h) zw).elim
      · exact (S.no_shared_to_single zt (mem_union_right _ h) zw).elim
      rw [M0] at h
      exact (not_mem_empty _ h).elim
    have cap := card_le_card sub
    have lim := card_insert_le S.e ({S.f} : Finset V)
    rw [card_singleton] at lim
    omega
  have sub : inside G (Shore D) z⊆S.M := by
    intro w h
    have ws := S.shared_lim (by omega) (by omega) zt h
    exact (mem_union.mp ws).resolve_left (fun n=>no ⟨w,mem_of_mem_erase n,(mem_filter.mp h).2⟩)
  have cap := card_le_card sub
  omega

theorem traceable_at_six_nonports_unmixed
    {C : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D) (ab : a≠b)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {r : V} (ce : Shore C={r}) (ar : G.Adj a r) (br : G.Adj b r)
    (high : ∀ v∈Shore D,5≤G.degree v)
    (l3 : S.L.card=3) (r3 : S.R.card=3) (m0 : S.M.card=0) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have empty : S.M=∅ := card_eq_zero.mp m0
  have fs : S.LS=S.F := by simpa [empty] using S.F_cover
  have six : S.F.card=6 := by
    rw [←fs]
    change (S.L∪S.R).card=6
    rw [card_union_of_disjoint S.LR_disjoint,l3,r3]
  obtain ⟨x,xl⟩ := card_pos.mp (show 0<S.L.card by omega)
  obtain ⟨y,yr⟩ := card_pos.mp (show 0<S.R.card by omega)
  have xy : x≠y := fun h=>disjoint_left.mp S.LR_disjoint xl (h.symm ▸ yr)
  have dense (u : V) (uf : u∈S.F) : S.F.card+1≤2*(S.F.filter (G.Adj u)).card := by
    have h := S.singles_dense_in_nonport high (fs.symm ▸ uf)
    omega
  have p := terminal_route_of_dense_finset S.F (S.gL xl) (S.gR yr) xy dense
  obtain ⟨u,ut,v,vt,q⟩ := S.shared_route_if_six high (.inl m0)
  have fS : S.F⊆Shore D := sdiff_subset
  have tS : S.T⊆Shore D := fun z zt=>(S.both_of_mem_T zt).1
  have ep : S.e∉S.F := fun h=>(mem_sdiff.mp h).2 S.e_port
  have fp : S.f∉S.F := fun h=>(mem_sdiff.mp h).2 S.f_port
  have et : S.e∉S.T := fun h=>S.T_e h rfl
  have ft : S.f∉S.T := fun h=>S.T_f h rfl
  have dis : Disjoint S.F S.T := disjoint_left.mpr fun z zf zt=>(mem_sdiff.mp zf).2 (S.T_sub zt)
  exact S.finish_with_two_exclusives cd ab cover ce ar br fS tS ep fp et ft dis (union_comm _ _)
    p q (((S.left_only x xl _ S.e_port).mpr rfl).symm)
    (((S.right_only y yr _ S.f_port).mpr rfl).symm) ut

end OneFiveFarProfile

#print axioms OneFiveFarProfile.traceable_at_six_nonports_unmixed
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
