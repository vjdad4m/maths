import DegreeFiveOneFiveFarUnmixed189
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
open private shared_route_if_six from DegreeFiveOneFiveFarUnmixed189

theorem traceable_at_six_nonports_mixed
    {C : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D) (ab : a≠b)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    {r : V} (ce : Shore C={r}) (ar : G.Adj a r) (br : G.Adj b r)
    (high : ∀ v∈Shore D,5≤G.degree v)
    (l2 : S.L.card=2) (r2 : S.R.card=2) (m2 : S.M.card=2) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have dis : Disjoint S.LS S.M := disjoint_union_left.mpr ⟨S.LM_disjoint,S.RM_disjoint⟩
  have four : S.LS.card=4 := by
    change (S.L∪S.R).card=4
    rw [card_union_of_disjoint S.LR_disjoint,l2,r2]
  have six : S.F.card=6 := by rw [←S.F_cover,card_union_of_disjoint dis,four,m2]
  have ⟨eEq,fEq⟩ := S.inside_exclusive_both_full (by omega) (by omega) high
  have eM (x : V) (xM : x∈S.M) : G.Adj S.e x := by
    have p : x∈inside G (Shore D) S.e := eEq.symm ▸ mem_union_right _ xM
    exact (mem_filter.mp p).2
  have fM (x : V) (xM : x∈S.M) : G.Adj S.f x := by
    have p : x∈inside G (Shore D) S.f := fEq.symm ▸ mem_union_right _ xM
    exact (mem_filter.mp p).2
  have fS : S.F⊆Shore D := sdiff_subset
  have tS : S.T⊆Shore D := fun z zt=>(S.both_of_mem_T zt).1
  have ep : S.e∉S.F := fun h=>(mem_sdiff.mp h).2 S.e_port
  have fp : S.f∉S.F := fun h=>(mem_sdiff.mp h).2 S.f_port
  have et : S.e∉S.T := fun h=>S.T_e h rfl
  have ft : S.f∉S.T := fun h=>S.T_f h rfl
  have apart : Disjoint S.F S.T := disjoint_left.mpr fun z zf zt=>(mem_sdiff.mp zf).2 (S.T_sub zt)
  obtain ⟨u,ut,v,vt,q⟩ := S.shared_route_if_six high (.inr ⟨m2,l2,r2⟩)
  have uv : u≠v := by
    intro eq
    subst v
    obtain ⟨p,h,hs⟩ := q
    have nil := (isPath_iff_eq_nil p).mp h
    have sub : S.T⊆{u} := by
      intro w wt
      have p' := (hs _).mpr wt
      rw [nil] at p'
      simpa using p'
    have t := card_le_card sub
    rw [S.T_card,card_singleton] at t
    omega
  by_cases good : ∀ x∈S.M,∃ y∈S.LS,G.Adj x y
  · obtain ⟨x,y,xy,eq⟩ := card_eq_two.mp m2
    have xM : x∈S.M := by simp [eq]
    have yM : y∈S.M := by simp [eq]
    have xN : x∉S.LS := fun h=>disjoint_left.mp dis h xM
    have yN : y∉S.LS := fun h=>disjoint_left.mp dis h yM
    have sh : insert x (insert y S.LS)=S.F := by
      rw [←S.F_cover,eq]
      ext z
      simp [or_comm,or_left_comm,or_assoc]
    have dense (z : V) (zS : z∈S.LS) (w : V) (wS : w∈insert x (insert y S.LS))
        (t : V) (tS : t∈insert x (insert y S.LS)) (zw : z≠w) (zt : z≠t)
        (nw : ¬G.Adj z w) (nt : ¬G.Adj z t) : w=t :=
      S.two_missed_impossible_of_six_nonports six high zS (sh ▸ wS) (sh ▸ tS) zw zt nw nt
    have path := six_route_with_two_special_terminals S.LS four xy xN yN dense (good x xM) (good y yM)
    exact S.finish_with_two_exclusives cd ab cover ce ar br fS tS ep fp et ft apart (union_comm _ _)
      (sh ▸ path) q (eM _ xM) (fM _ yM) ut
  push_neg at good
  obtain ⟨m,mM,no⟩ := good
  have mf := S.M_sub_F mM
  have md := fS mf
  let A := S.F.erase m
  let B := insert m S.T
  have A5 : A.card=5 := by change (S.F.erase m).card=5; rw [card_erase_of_mem mf,six]
  have mT : m∉S.T := fun h=>disjoint_left.mp apart mf h
  have am (z : V) (zS : z∈S.LS) : ¬G.Adj z m := fun h=>no z zS h.symm
  have av (z : V) (zS : z∈S.LS) (w : V) (wa : w∈A) (zw : z≠w) : G.Adj z w := by
    apply Classical.byContradiction
    intro neg
    have mz : z≠m := fun e=>disjoint_left.mp dis (e ▸ zS) mM
    exact (mem_erase.mp wa).1
      (S.two_missed_impossible_of_six_nonports six high zS (mem_of_mem_erase wa) mf zw mz neg (am z zS))
  have AS : S.LS⊆A := by
    intro w ws
    exact mem_erase.mpr ⟨fun e=>disjoint_left.mp dis (e ▸ ws) mM,S.LS_sub_F ws⟩
  have clique : CompleteOn G A := by
    intro x xa y ya xy
    by_cases xS : x∈S.LS
    · exact av x xS y ya xy
    by_cases yS : y∈S.LS
    · exact (av y yS x xa xy.symm).symm
    have sub : {x,y,m}⊆S.M := by
      have mx : x∈S.M := (mem_union.mp (S.F_cover.symm ▸ mem_of_mem_erase xa)).resolve_left xS
      have my : y∈S.M := (mem_union.mp (S.F_cover.symm ▸ mem_of_mem_erase ya)).resolve_left yS
      exact insert_subset_iff.mpr ⟨mx,insert_subset_iff.mpr ⟨my,singleton_subset_iff.mpr mM⟩⟩
    have n := card_le_card sub
    have ne1 := (mem_erase.mp xa).1
    have ne2 := (mem_erase.mp ya).1
    simp [xy,ne1,ne2,m2] at n
  obtain ⟨x,xl⟩ := card_pos.mp (show 0<S.L.card by omega)
  obtain ⟨y,yr⟩ := card_pos.mp (show 0<S.R.card by omega)
  have xy : x≠y := fun h=>disjoint_left.mp S.LR_disjoint xl (h.symm ▸ yr)
  obtain ⟨p,pp,ps⟩ := path_between_in_clique A clique (AS (mem_union_left _ xl)) (AS (mem_union_right _ yr)) xy
  have path : RouteOn G A x y := ⟨p,pp,ps⟩
  have mTwo : G.Adj m u ∨ G.Adj m v := by
    apply Classical.byContradiction
    intro n
    have sub : G.neighborFinset m⊆insert S.e (insert S.f ((S.M.erase m)∪((S.T.erase u).erase v))) := by
      intro z zn
      have mz := (mem_neighborFinset G m z).mp zn
      have zd := mem_of_mem_erase (nonport_neighbors_subset md (mem_sdiff.mp mf).2 zn)
      rcases S.shore_split zd with he|hf|ht|hl|hr|hm
      · simp [he]
      · simp [hf]
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _
          (mem_erase.mpr ⟨fun h=>n (.inr (h ▸ mz)),mem_erase.mpr ⟨fun h=>n (.inl (h ▸ mz)),ht⟩⟩)))
      · exact (no z (mem_union_left _ hl) mz).elim
      · exact (no z (mem_union_right _ hr) mz).elim
      exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _
        (mem_erase.mpr ⟨mz.ne.symm,hm⟩)))
    have cap := card_le_card sub
    rw [card_neighborFinset_eq_degree] at cap
    have c := card_insert_le S.e (insert S.f ((S.M.erase m)∪((S.T.erase u).erase v)))
    have d := card_insert_le S.f ((S.M.erase m)∪((S.T.erase u).erase v))
    have k := card_union_le (S.M.erase m) ((S.T.erase u).erase v)
    rw [card_erase_of_mem mM,m2,card_erase_of_mem (mem_erase.mpr ⟨uv.symm,vt⟩),
      card_erase_of_mem ut,S.T_card] at k
    have deg := high m md
    omega
  have asub : A⊆Shore D := fun _ h=>fS (mem_of_mem_erase h)
  have bsub : B⊆Shore D := insert_subset_iff.mpr ⟨md,tS⟩
  have ep' : S.e∉A := fun h=>ep (mem_of_mem_erase h)
  have fp' : S.f∉A := fun h=>fp (mem_of_mem_erase h)
  have eB : S.e∉B := by
    have em : S.e≠m := fun e=>ep (e.symm ▸ mf)
    simp [B,em,et]
  have fB : S.f∉B := by
    have fm : S.f≠m := fun e=>fp (e.symm ▸ mf)
    simp [B,fm,ft]
  have aB : Disjoint A B := by
    apply disjoint_left.mpr
    intro z za zb
    rcases mem_insert.mp zb with h|h
    · exact (mem_erase.mp za).1 h
    exact disjoint_left.mp apart (mem_of_mem_erase za) h
  have total : A∪B=S.T∪S.F := by
    change (S.F.erase m)∪insert m S.T=S.T∪S.F
    rw [union_insert,←insert_union,insert_erase mf,union_comm]
  have finish {i j : V} (p' : RouteOn G B i j) (iT : i∈S.T) :
      ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support :=
    S.finish_with_two_exclusives cd ab cover ce ar br asub bsub ep' fp' eB fB aB total path p'
      (((S.left_only x xl _ S.e_port).mpr rfl).symm)
      (((S.right_only y yr _ S.f_port).mpr rfl).symm) iT
  rcases mTwo with mu|mv
  · exact finish (q.reverse.suffix mu.symm mT) vt
  exact finish (q.suffix mv.symm mT) ut

end OneFiveFarProfile

#print axioms OneFiveFarProfile.traceable_at_six_nonports_mixed
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
