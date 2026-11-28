import DegreeFiveOneFiveFarMixed189
import DegreeFiveOneFiveNear189
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
open private shared_lim from DegreeFiveOneFiveFarUnmixed189
open private shore_partition from DegreeFiveOneFiveFarGlue189
open private lift_side_path from DegreeFiveSmallSides189

theorem traceable_at_seven_nonports
    {C : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D) (ab : a≠b)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {r : V} (ce : Shore C={r}) (ar : G.Adj a r) (br : G.Adj b r)
    (high : ∀ v∈Shore D,5≤G.degree v)
    (l3 : S.L.card=3) (r3 : S.R.card=3) (m1 : S.M.card=1) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨z,zm⟩ := card_pos.mp (show 0<S.M.card by omega)
  have zOnly : S.M={z} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr zm) (by simp [m1])).symm
  have fz := S.M_sub_F zm
  have zd := (mem_sdiff.mp fz).1
  have zP : z∉cutPorts D := (mem_sdiff.mp fz).2
  let Q := Shore D\S.T
  have zQ : z∈Q := mem_sdiff.mpr ⟨zd,fun h=>zP (S.T_sub h)⟩
  have eQ : S.e∈Q := mem_sdiff.mpr ⟨(mem_filter.mp S.e_port).1,fun h=>S.T_e h rfl⟩
  have fQ : S.f∈Q := mem_sdiff.mpr ⟨(mem_filter.mp S.f_port).1,fun h=>S.T_f h rfl⟩
  have Q9 : Q.card=9 := by
    have t : S.T⊆Shore D := fun w wt=>(S.both_of_mem_T wt).1
    have tt : Q.card+S.T.card=(Shore D).card := card_sdiff_add_card_eq_card t
    have p := S.count
    have d3 := S.T_card
    omega
  have tAdj (u : V) (ut : u∈S.T) :
      ∀ w∈(S.T.erase u)∪S.M,G.Adj u w := by
    have ed := (S.both_of_mem_T ut).1
    have lo := inside_high_at_least_three ed (high u ed)
    have sub := S.shared_lim (by omega) (by omega) ut
    have comp : (S.T.erase u)∪S.M=inside G (Shore D) u := by
      have upper := card_union_le (S.T.erase u) S.M
      rw [card_erase_of_mem ut,S.T_card,m1] at upper
      exact (eq_of_subset_of_card_le sub (by omega)).symm
    intro w hw
    exact (mem_filter.mp (comp ▸ hw)).2
  have cl : CompleteOn G S.T := by
    intro u ut w wt uw
    exact tAdj u ut w (mem_union_left _ (mem_erase.mpr ⟨uw.symm,wt⟩))
  have allz (u : V) (ut : u∈S.T) : G.Adj u z := tAdj u ut z (mem_union_right _ zm)
  have ⟨es,fs⟩ := S.inside_exclusive_both_full (by omega) (by omega) high
  have ze : G.Adj z S.e := ((mem_filter.mp (es.symm ▸ mem_union_right _ zm)).2).symm
  let U := ↑(↑Q : Set V)
  let J := G.induce (↑Q : Set V)
  let zz : U := ⟨z,zQ⟩
  let ee : U := ⟨S.e,eQ⟩
  let ff : U := ⟨S.f,fQ⟩
  have n : Fintype.card U=9 := (Fintype.card_coe Q).trans Q9
  have eLow : 4≤J.degree ee := by
    change 4≤(G.induce (↑Q : Set V)).degree ee
    rw [←inside_card_eq_degree_induce (G:=G) Q ee]
    have eq : Q.filter (G.Adj S.e)=inside G (Shore D) S.e := by
      ext w
      constructor
      · intro h
        obtain ⟨wq,e⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨(mem_sdiff.mp wq).1,e⟩
      intro h
      obtain ⟨wd,ew⟩ := mem_filter.mp h
      have not : w∉S.T := fun wt=>S.e_excluded (by omega) w
        (by rw [S.B_eq]; exact mem_insert_of_mem wt) ew
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨wd,not⟩,ew⟩
    change 4≤(Q.filter (G.Adj S.e)).card
    rw [eq,es,card_union_of_disjoint S.LM_disjoint,l3,m1]
  have fLow : 4≤J.degree ff := by
    change 4≤(G.induce (↑Q : Set V)).degree ff
    rw [←inside_card_eq_degree_induce (G:=G) Q ff]
    have eq : Q.filter (G.Adj S.f)=inside G (Shore D) S.f := by
      ext w
      constructor
      · intro h
        obtain ⟨wq,e⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨(mem_sdiff.mp wq).1,e⟩
      intro h
      obtain ⟨wd,fw⟩ := mem_filter.mp h
      have not : w∉S.T := fun wt=>S.f_excluded (by omega) w
        (by rw [S.A_eq]; exact mem_insert_of_mem wt) fw
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨wd,not⟩,fw⟩
    change 4≤(Q.filter (G.Adj S.f)).card
    rw [eq,fs,card_union_of_disjoint S.RM_disjoint,r3,m1]
  have inS (w : U) (wS : w.val∈S.LS) : 5≤J.degree w := by
    have wf := S.LS_sub_F wS
    obtain ⟨wd,wp⟩ := mem_sdiff.mp wf
    have sub : G.neighborFinset w.val⊆Q.filter (G.Adj w.val) := by
      intro v vn
      have vd := mem_of_mem_erase (nonport_neighbors_subset wd wp vn)
      have wv := (mem_neighborFinset G w.val v).mp vn
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨vd,fun ht=>S.no_shared_to_single ht wS wv.symm⟩,wv⟩
    have b := card_le_card sub
    rw [card_neighborFinset_eq_degree] at b
    change G.degree w.val≤(inside G Q w.val).card at b
    rw [inside_card_eq_degree_induce (G:=G) Q w] at b
    exact (high _ wd).trans b
  have clss (w : U) (wz : w≠zz) : w=ee ∨ w=ff ∨ w.val∈S.LS := by
    obtain ⟨wd,wt⟩ := mem_sdiff.mp w.property
    rcases S.shore_split wd with e|e|e|e|e|e
    · exact .inl (Subtype.ext e)
    · exact .inr (.inl (Subtype.ext e))
    · exact (wt e).elim
    · exact .inr (.inr (mem_union_left _ e))
    · exact .inr (.inr (mem_union_right _ e))
    exact (wz (Subtype.ext (mem_singleton.mp (zOnly ▸ e)))).elim
  have lo (w : U) (wz : w≠zz) : 4≤J.degree w :=
    (clss w wz).elim (fun h=>h.symm ▸ eLow) (fun h=>h.elim
      (fun e=>e.symm ▸ fLow) (fun e=>(show 4≤5 by decide).trans (inS w e)))
  have band (u v : U) (uv : u≠v) (uz : u≠zz) (vz : v≠zz)
      (ok : ¬((u=ee ∧ v=ff) ∨ (u=ff ∧ v=ee))) (_ : ¬J.Adj u v) :
      Fintype.card U≤J.degree u+J.degree v := by
    have some : u.val∈S.LS ∨ v.val∈S.LS := by
      have h := clss u uz
      have k := clss v vz
      rcases h with eu|fu|su
      · rcases k with ev|fv|sv
        · exact (uv (eu.trans ev.symm)).elim
        · exact (ok (.inl ⟨eu,fv⟩)).elim
        exact .inr sv
      · rcases k with ev|fv|sv
        · exact (ok (.inr ⟨fu,ev⟩)).elim
        · exact (uv (fu.trans fv.symm)).elim
        exact .inr sv
      exact .inl su
    rcases some with h|h
    · have u5 := inS u h
      have v4 := lo v vz
      omega
    have v5 := inS v h
    have u4 := lo u uz
    omega
  have neEF : ee≠ff := fun h=>S.e_ne_f (congrArg Subtype.val h)
  have neEZ : ee≠zz := fun h=>zP ((show S.e=z from congrArg Subtype.val h) ▸ S.e_port)
  have neFZ : ff≠zz := fun h=>zP ((show S.f=z from congrArg Subtype.val h) ▸ S.f_port)
  obtain ⟨t,p,pp,ps⟩ := low_root_route_of_one_protected_pair zz ee ff neEF neEZ neFZ (by omega) ze band
  have p' : RouteOn G Q z t.val := lift_side_path Q p pp ps
  obtain ⟨u,ut⟩ := card_pos.mp (show 0<S.T.card by rw [S.T_card]; decide)
  obtain ⟨v,k,kp,ks⟩ := rooted_path_in_clique S.T cl ut
  have vt : v∈S.T := (ks _).mp k.end_mem_support
  have edge : G.Adj v z := allz v vt
  have dis' : Disjoint S.T Q := disjoint_sdiff_self_right
  have union : S.T∪Q=Shore D := union_sdiff_of_subset (fun w wt=>(S.both_of_mem_T wt).1)
  have full : RouteOn G (Shore D) u t.val := union ▸
    (show RouteOn G S.T u v from ⟨k,kp,ks⟩).join p' dis' edge
  have mid : WingRealizes G a b (Shore C) .terminal := by
    rw [ce]
    exact ⟨r,r,ar,br,RouteOn.singleton⟩
  have dst : WingRealizes G a b (Shore D) .aFree := ⟨u,t.val,(S.both_of_mem_T ut).2.1,full⟩
  exact traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
    (shore_off D).1 (shore_off D).2 cover (.inl ⟨mid,.inl dst⟩)

end OneFiveFarProfile

theorem traceable_of_actual_five_one_five_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (one : (cutPorts C).card=1) (five : (cutPorts D).card=5) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_cases small : (Shore D).card≤10
  · exact traceable_of_actual_five_one_five_ports_small hc two even conn degree cd cover one five small
  obtain ⟨S⟩ := one_five_far_profile hc two even conn degree cd cover one five (by omega)
  obtain ⟨r,ce,ar,br,high,_⟩ := one_five_shore_shape two conn degree cd cover one five
  have ab : a≠b := by intro h; rw [h,dist_self] at two; omega
  have hi := (one_five_opposite_order_bound hc two even conn degree cd cover one five).1
  rcases S.six_seven high (by omega) hi with ⟨l,r',m⟩|⟨l,r',m⟩|⟨l,r',m⟩
  · exact S.traceable_at_six_nonports_unmixed cd ab cover ce ar br high l r' m
  · exact S.traceable_at_six_nonports_mixed cd ab cover ce ar br high l r' m
  exact S.traceable_at_seven_nonports cd ab cover ce ar br high l r' m

#print axioms OneFiveFarProfile.traceable_at_seven_nonports
#print axioms traceable_of_actual_five_one_five_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
