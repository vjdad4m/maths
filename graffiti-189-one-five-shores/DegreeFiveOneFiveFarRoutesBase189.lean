import DegreeFiveOneFiveFarCounts189


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

private noncomputable def F (_S : OneFiveFarProfile D) : Finset V := Shore D\cutPorts D
private noncomputable def LS : Finset V := S.L∪S.R

theorem T_sub : S.T⊆cutPorts D := by
  intro z zt
  obtain ⟨zd,za,zb⟩ := S.both_of_mem_T zt
  exact mem_filter.mpr ⟨zd,.inl za⟩

theorem T_e {z : V} (zt : z∈S.T) : z≠S.e := fun e=>S.e_not_b (e ▸ (S.both_of_mem_T zt).2.2)
theorem T_f {z : V} (zt : z∈S.T) : z≠S.f := fun e=>S.f_not_a (e ▸ (S.both_of_mem_T zt).2.1)

theorem F_cover : S.LS∪S.M=S.F := S.F_eq

private theorem shore_split {z : V} (zd : z∈Shore D) :
    z=S.e ∨ z=S.f ∨ z∈S.T ∨ z∈S.L ∨ z∈S.R ∨ z∈S.M := by
  by_cases zp : z∈cutPorts D
  · rw [S.all_ports] at zp
    simpa [or_assoc] using (show z∈insert S.e (insert S.f S.T) ∨ z∈S.L ∨ z∈S.R ∨ z∈S.M from .inl zp)
  have h : z∈S.LS∪S.M := S.F_cover.symm ▸ mem_sdiff.mpr ⟨zd,zp⟩
  rcases mem_union.mp h with h|h
  · exact .inr (.inr (.inr ((mem_union.mp h).imp id Or.inl)))
  exact .inr (.inr (.inr (.inr (.inr h))))

theorem LS_sub_F : S.LS⊆S.F := by
  intro z m
  exact S.F_cover ▸ mem_union_left _ m

theorem M_sub_F : S.M⊆S.F := by
  intro z m
  exact S.F_cover ▸ mem_union_right _ m

theorem gL {z : V} (zl : z∈S.L) : z∈S.F := S.LS_sub_F (mem_union_left _ zl)
theorem gR {z : V} (zr : z∈S.R) : z∈S.F := S.LS_sub_F (mem_union_right _ zr)

theorem no_shared_to_single {x z : V} (xT : x∈S.T) (zS : z∈S.LS) : ¬G.Adj x z := by
  intro e
  rcases mem_union.mp zS with zl|zr
  · exact S.T_e xT ((S.left_only z zl x (S.T_sub xT)).mp e.symm)
  exact S.T_f xT ((S.right_only z zr x (S.T_sub xT)).mp e.symm)

theorem inside_exclusive_both_full
    (satA : S.L.card+S.M.card=4) (satB : S.R.card+S.M.card=4)
    (high : ∀ v∈Shore D,5≤G.degree v) :
    inside G (Shore D) S.e=S.L∪S.M ∧ inside G (Shore D) S.f=S.R∪S.M := by
  classical
  have ee : S.e∈Shore D := (mem_filter.mp S.e_port).1
  have ff : S.f∈Shore D := (mem_filter.mp S.f_port).1
  have e4 : 4≤(inside G (Shore D) S.e).card :=
    inside_high_at_least_four_if_exclusive ee (high _ ee) (fun h=>S.e_not_b h.2)
  have f4 : 4≤(inside G (Shore D) S.f).card :=
    inside_high_at_least_four_if_exclusive ff (high _ ff) (fun h=>S.f_not_a h.1)
  constructor
  · apply eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨zd,ez⟩ := mem_filter.mp hz
      rcases S.shore_split zd with he|hf|ht|hl|hr|hm
      · exact (ez.ne.symm he).elim
      · exact (S.e_excluded satB S.f (by rw [S.B_eq]; simp) (hf ▸ ez)).elim
      · exact (S.e_excluded satB z (by rw [S.B_eq]; exact mem_insert_of_mem ht) ez).elim
      · exact mem_union_left _ hl
      · exact (S.e_ne_f ((S.right_only z hr _ S.e_port).mp ez.symm)).elim
      exact mem_union_right _ hm
    exact (card_union_le _ _).trans (satA.le.trans e4)
  apply eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨zd,fz⟩ := mem_filter.mp hz
    rcases S.shore_split zd with he|hf|ht|hl|hr|hm
    · exact (S.f_excluded satA S.e (by rw [S.A_eq]; simp) (he ▸ fz)).elim
    · exact (fz.ne.symm hf).elim
    · exact (S.f_excluded satA z (by rw [S.A_eq]; exact mem_insert_of_mem ht) fz).elim
    · exact (S.e_ne_f ((S.left_only z hl _ S.f_port).mp fz.symm).symm).elim
    · exact mem_union_left _ hr
    exact mem_union_right _ hm
  exact (card_union_le _ _).trans (satB.le.trans f4)

theorem singles_dense_in_nonport
    (high : ∀ v∈Shore D,5≤G.degree v)
    {z : V} (zs : z∈S.LS) :
    4≤(S.F.filter (G.Adj z)).card := by
  classical
  have zf := S.LS_sub_F zs
  obtain ⟨zd,zp⟩ := mem_sdiff.mp zf
  obtain h|h := mem_union.mp zs
  · have cap : G.neighborFinset z⊆insert S.e (S.F.filter (G.Adj z)) := by
      intro w wn
      have wz := (nonport_neighbors_subset zd zp) wn
      have wd := mem_of_mem_erase wz
      have zw := (mem_neighborFinset G z w).mp wn
      by_cases wp : w∈cutPorts D
      · exact mem_insert.mpr (.inl ((S.left_only z h w wp).mp zw))
      exact mem_insert_of_mem (mem_filter.mpr ⟨mem_sdiff.mpr ⟨wd,wp⟩,zw⟩)
    have tally := (card_le_card cap).trans (card_insert_le _ _)
    rw [card_neighborFinset_eq_degree] at tally
    have hh := high z zd
    omega
  have cap : G.neighborFinset z⊆insert S.f (S.F.filter (G.Adj z)) := by
    intro w wn
    have wz := (nonport_neighbors_subset zd zp) wn
    have wd := mem_of_mem_erase wz
    have zw := (mem_neighborFinset G z w).mp wn
    by_cases wp : w∈cutPorts D
    · exact mem_insert.mpr (.inl ((S.right_only z h w wp).mp zw))
    exact mem_insert_of_mem (mem_filter.mpr ⟨mem_sdiff.mpr ⟨wd,wp⟩,zw⟩)
  have tally := (card_le_card cap).trans (card_insert_le _ _)
  rw [card_neighborFinset_eq_degree] at tally
  have hh := high z zd
  omega

theorem two_missed_impossible_of_six_nonports
    (six : S.F.card=6) (high : ∀ v∈Shore D,5≤G.degree v)
    {z : V} (zs : z∈S.LS)
    {u v : V} (uf : u∈S.F) (vf : v∈S.F) (zu : z≠u) (zv : z≠v)
    (noU : ¬G.Adj z u) (noV : ¬G.Adj z v) : u=v := by
  classical
  apply Classical.byContradiction
  intro ne
  have zf := S.LS_sub_F zs
  have sub : S.F.filter (G.Adj z)⊆(((S.F.erase z).erase u).erase v) := by
    intro w wm
    obtain ⟨wf,zw⟩ := mem_filter.mp wm
    exact mem_erase.mpr ⟨fun e=>noV (e ▸ zw),mem_erase.mpr
      ⟨fun e=>noU (e ▸ zw),mem_erase.mpr ⟨zw.ne.symm,wf⟩⟩⟩
  have v' : v∈(S.F.erase z).erase u :=
    mem_erase.mpr ⟨(fun e=>ne e.symm),mem_erase.mpr ⟨zv.symm,vf⟩⟩
  have cap := card_le_card sub
  rw [card_erase_of_mem v',card_erase_of_mem (mem_erase.mpr ⟨zu.symm,uf⟩),
    card_erase_of_mem zf,six] at cap
  have lo := S.singles_dense_in_nonport high zs
  omega

end OneFiveFarProfile

#print axioms OneFiveFarProfile.inside_exclusive_both_full
#print axioms OneFiveFarProfile.two_missed_impossible_of_six_nonports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
