import DegreeFiveOneFiveFarProfile189


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

theorem e_ne_f : S.e≠S.f := by
  intro h
  have e := (mem_filter.mp S.e_port).2
  have f := (mem_filter.mp S.f_port).2
  exact e.elim (fun ha=>S.f_not_a (h ▸ ha)) S.e_not_b

theorem all_ports : cutPorts D=insert S.e (insert S.f S.T) := by
  ext z
  change z∈(Shore D).filter (fun w=>G.Adj a w ∨ G.Adj b w) ↔ _
  rw [mem_filter]
  have split : (z∈Shore D ∧ (G.Adj a z ∨ G.Adj b z)) ↔
      z∈portColor D a ∪ portColor D b := by simp [and_or_left]
  rw [split,S.A_eq,S.B_eq]
  simp [or_assoc,or_left_comm]
  
theorem both_of_mem_T {z : V} (zT : z∈S.T) :
    z∈Shore D ∧ G.Adj a z ∧ G.Adj b z := by
  rw [S.T_eq] at zT
  obtain ⟨ha,hb⟩ := mem_inter.mp zT
  exact ⟨(mem_filter.mp ha).1,(mem_filter.mp ha).2,(mem_filter.mp hb).2⟩

theorem eA : G.Adj a S.e := ((mem_filter.mp S.e_port).2).resolve_right S.e_not_b
theorem fB : G.Adj b S.f := ((mem_filter.mp S.f_port).2).resolve_left S.f_not_a

theorem simultaneous_saturation
    (high : ∀ v∈Shore D,5≤G.degree v) :
    (S.L.card+S.M.card=4 ↔ S.R.card+S.M.card=4) := by
  classical
  constructor
  · intro full
    have fd := (mem_filter.mp S.f_port).1
    have narrow : 4≤(inside G (Shore D) S.f).card := inside_high_at_least_four_if_exclusive fd
      (high _ fd) (fun h=>S.f_not_a h.1)
    have sub : inside G (Shore D) S.f⊆S.R∪S.M := by
      intro z m
      obtain ⟨zd,fz⟩ := mem_filter.mp m
      by_cases zP : z∈cutPorts D
      · rw [S.all_ports] at zP
        simp only [mem_insert] at zP
        rcases zP with h|h|h
        · exact (S.f_excluded full _ (by rw [S.A_eq]; simp [h]) fz).elim
        · exact (fz.ne.symm h).elim
        exact (S.f_excluded full _ (by rw [S.A_eq]; exact mem_insert_of_mem h) fz).elim
      have zF : z∈S.L∪S.R∪S.M := S.F_eq.symm ▸ mem_sdiff.mpr ⟨zd,zP⟩
      rcases mem_union.mp zF with h|h
      · rcases mem_union.mp h with h|h
        · exact (S.e_ne_f ((S.left_only _ h _ S.f_port).mp fz.symm).symm).elim
        exact mem_union_left _ h
      exact mem_union_right _ h
    have c := (card_le_card sub).trans (card_union_le S.R S.M)
    have p := S.b_cap
    omega
  intro full
  have ed := (mem_filter.mp S.e_port).1
  have narrow : 4≤(inside G (Shore D) S.e).card := inside_high_at_least_four_if_exclusive ed
    (high _ ed) (fun h=>S.e_not_b h.2)
  have sub : inside G (Shore D) S.e⊆S.L∪S.M := by
    intro z m
    obtain ⟨zd,ez⟩ := mem_filter.mp m
    by_cases zP : z∈cutPorts D
    · rw [S.all_ports] at zP
      simp only [mem_insert] at zP
      rcases zP with h|h|h
      · exact (ez.ne.symm h).elim
      · exact (S.e_excluded full _ (by rw [S.B_eq]; simp [h]) ez).elim
      exact (S.e_excluded full _ (by rw [S.B_eq]; exact mem_insert_of_mem h) ez).elim
    have zF : z∈S.L∪S.R∪S.M := S.F_eq.symm ▸ mem_sdiff.mpr ⟨zd,zP⟩
    rcases mem_union.mp zF with h|h
    · rcases mem_union.mp h with h|h
      · exact mem_union_left _ h
      exact (S.e_ne_f ((S.right_only _ h _ S.e_port).mp ez.symm)).elim
    exact mem_union_right _ h
  have c := (card_le_card sub).trans (card_union_le S.L S.M)
  have p := S.a_cap
  omega

include S in
theorem no_order_thirteen (high : ∀ v∈Shore D,5≤G.degree v) :
    (Shore D).card≠13 := by
  classical
  intro size
  have count := S.count
  have aa := S.a_cap
  have bb := S.b_cap
  have satA : S.L.card+S.M.card=4 := by omega
  have satB : S.R.card+S.M.card=4 := by omega
  have M0 : S.M=∅ := card_eq_zero.mp (by omega)
  have pos : S.T.Nonempty := card_pos.mp (by rw [S.T_card]; decide)
  obtain ⟨z,zt⟩ := pos
  obtain ⟨zd,za,zb⟩ := S.both_of_mem_T zt
  have zne : z≠S.e ∧ z≠S.f :=
    ⟨fun h=>S.e_not_b (h ▸ zb),fun h=>S.f_not_a (h ▸ za)⟩
  have zP : z∈cutPorts D := mem_filter.mpr ⟨zd,.inl za⟩
  have sub : inside G (Shore D) z⊆S.T.erase z := by
    intro w wm
    obtain ⟨wd,zw⟩ := mem_filter.mp wm
    by_cases wp : w∈cutPorts D
    · have h := wp
      rw [S.all_ports] at h
      simp only [mem_insert] at h
      rcases h with h|h|h
      · have zB : z∈portColor D b := mem_filter.mpr ⟨zd,zb⟩
        exact (S.e_excluded satB z zB (h ▸ zw.symm)).elim
      · have zA : z∈portColor D a := mem_filter.mpr ⟨zd,za⟩
        exact (S.f_excluded satA z zA (h ▸ zw.symm)).elim
      exact mem_erase.mpr ⟨zw.ne.symm,h⟩
    have wF : w∈S.L∪S.R∪S.M := S.F_eq.symm ▸ mem_sdiff.mpr ⟨wd,wp⟩
    rw [M0,union_empty] at wF
    rcases mem_union.mp wF with wl|wr
    · exact (zne.1 ((S.left_only w wl z zP).mp zw.symm)).elim
    exact (zne.2 ((S.right_only w wr z zP).mp zw.symm)).elim
  have tally := card_le_card sub
  rw [card_erase_of_mem zt,S.T_card] at tally
  have lo := inside_high_at_least_three zd (high z zd)
  omega

theorem six_seven (high : ∀ v∈Shore D,5≤G.degree v)
    (highOrder : 11≤(Shore D).card) (small : (Shore D).card≤13) :
    (S.L.card=3 ∧ S.R.card=3 ∧ S.M.card=0) ∨
      (S.L.card=2 ∧ S.R.card=2 ∧ S.M.card=2) ∨
      (S.L.card=3 ∧ S.R.card=3 ∧ S.M.card=1) := by
  have no := S.no_order_thirteen high
  have count := S.count
  have a := S.a_cap
  have b := S.b_cap
  have sat := S.simultaneous_saturation high
  omega

end OneFiveFarProfile

#print axioms OneFiveFarProfile.simultaneous_saturation
#print axioms OneFiveFarProfile.six_seven
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
