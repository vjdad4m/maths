import DenseEndpointLayout189
import DenseOwnerNine189
import MarkedWingPathNine189
import CloseFive17R_189
import CloseFive18_189
import SixWingFrontier189
import WideWing189
import DenseOwnerRoute189
import MarkedWingPath189
import Interior189
import GapStrong189
open private Graffiti189LongestPath.WideWing.inside_deg Graffiti189LongestPath.WideWing.two_per_block from WideWing189
open SimpleGraph SimpleGraph.Walk Finset Graffiti189LongestPath
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.GapTwin
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.GapStrong Graffiti189LongestPath.WideWing
open Graffiti189LongestPath.Interior Graffiti189LongestPath.HighDichotomy
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints
  Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos
  Graffiti189LongestPath.Rigidity.LeftMarks Graffiti189LongestPath.Rigidity.RightMarks
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
namespace Graffiti189LongestPath.SixFourOrderTwentyFour
open Graffiti189LongestPath.FiveCheapBudget
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exact order-24 elimination at threshold six and connectivity at least four. -/
theorem traceable_order_twenty_four_aux (hc : G.Connected) (k : Nat) (hk : k = 4)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V, u ≠ v → k+2 ≤ G.degree u ∨ k+2 ≤ G.degree v)
    (fail : ¬∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support)
    (bound : Fintype.card V≤24) : False := by
  classical
  obtain ⟨a₀,b₀,p₀,h₀⟩ := exists_edgeMinAvoid hc (k+2) deg
  obtain ⟨w,hw⟩ : ∃ w, w ∉ p₀.support :=
    not_forall.mp (fun h => fail ⟨a₀,b₀,p₀,h₀.1.1.1,h⟩)
  obtain ⟨a,b,p,hp,same,da,db⟩ :=
    OneSlack.MultiRotation.rotate_to_two_high_endpoints_general hc k (by omega) (k+2)
      conn deg h₀.1.1 hw
  have hset : p.support.toFinset = p₀.support.toFinset := by
    ext v
    simpa only [List.mem_toFinset] using (same v).symm
  have hMin : EdgeMinAvoid (k+2) p := by
    refine ⟨⟨hp,?_⟩,?_⟩
    · intro u v q hq
      rw [hset]
      exact h₀.1.2 u v q hq
    · intro u v q hq x dx hx hx'
      exact h₀.2 u v q hq x dx hx ((same x).mpr hx')
  have nspan : ∃ x, x∉p.support := ⟨w,fun h => hw ((same w).mpr h)⟩
  obtain ⟨x,hx,dx,i,hi⟩ := has_high_active hc k (by omega) cap conn deg hp nspan
  obtain ⟨H,hxH,hN,hO,hC,hJ⟩ := exists_omitted_component hx
  let C : OmittedComponent p := ⟨H,hN,hO,hC,hJ⟩
  have xhi := (normalized_high_omission hc (k+2) k (by omega) le_rfl
    cap conn hMin hx dx i hi).1
  have ex := (Graffiti189LongestPath.pin_data hi).2
  obtain ⟨y,ey,yo⟩ := omitted_has_omitted_neighbor hc hp hx dx ⟨_,ex⟩
    (distanceTwo_le_of_even (k+2) x (cap x))
  have hyH : y ∈ H := by
    by_contra hn
    exact yo (hC x hxH y hn ey)
  have someOff (z : V) (hz : z ∈ H) : ∃ t ∉ p.support, G.Adj z t := by
    by_cases eq : z=x
    · exact ⟨y,yo,eq.symm ▸ ey⟩
    obtain ⟨q,_,hh⟩ := hJ z hz x hxH
    cases q with
    | nil => exact (eq rfl).elim
    | @cons _ u _ e q => exact ⟨u,hO u (hh _ (by simp)),e⟩
  have Hsize : k+1 ≤ H.card := by
    have sub : G.neighborFinset x ⊆ (PinVertices p x) ∪ H.erase x := by
      intro u hu
      have e := (G.mem_neighborFinset x u).mp hu
      by_cases h : u ∈ H
      · exact mem_union.mpr (Or.inr (mem_erase.mpr ⟨e.ne.symm,h⟩))
      · obtain ⟨j,hj,he⟩ :=
          Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx (hC x hxH u h e) e
        exact mem_union.mpr (Or.inl (mem_image.mpr ⟨j,hj,he⟩))
    have n := card_le_card sub
    have n' := card_union_le (PinVertices p x) (H.erase x)
    rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,card_erase_of_mem hxH] at n'
    rw [G.card_neighborFinset_eq_degree] at n
    omega
  let I := (range p.length).filter (fun j => ∃ z∈H, (4≤k ∨ k+2≤G.degree z) ∧ j∈Pins p z)
  have Idata {j : ℕ} (hj : j ∈ I) : ∃ z∈H, (4≤k ∨ k+2≤G.degree z) ∧ j∈Pins p z :=
    (mem_filter.mp hj).2
  have atLeast : k ≤ I.card+(if 4≤k then 0 else 2) := by
    have ck := componentPins_card hp C k conn
    have base {u : V} (hu : u ∈ componentPins C) :
        ∃ z∈H, ∃ j∈Pins p z, p.getVert j=u := by
      obtain ⟨hu,z,hz,ez⟩ := mem_filter.mp hu
      obtain ⟨j,hj,he⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp
        (hO z hz) (List.mem_toFinset.mp hu) ez
      exact ⟨z,hz,j,hj,he⟩
    by_cases k4 : 4≤k
    · have sub : componentPins C ⊆ I.image p.getVert := by
        intro u hu
        obtain ⟨z,hz,j,hj,he⟩ := base hu
        exact mem_image.mpr ⟨j,mem_filter.mpr ⟨(mem_filter.mp hj).1,z,hz,Or.inl k4,hj⟩,he⟩
      have c1 := card_le_card sub
      have c2 := card_image_le (s:=I) (f:=p.getVert)
      simp only [if_pos k4,Nat.add_zero]
      omega
    simp only [if_neg k4]
    by_cases low : ∃ z ∈ H, G.degree z < k+2
    · obtain ⟨v,hv,dk⟩ := low
      have cc : (Pins p v).card≤2 := by
        obtain ⟨t,ht,et⟩ := someOff v hv
        exact at_most_two_pins_with_omitted_neighbor hc k hp (hO v hv)
          (distanceTwo_le_of_even (k+2) v (cap v)) conn ht et
      have sub : componentPins C ⊆ I.image p.getVert ∪ PinVertices p v := by
        intro u hu
        obtain ⟨z,hz,j,hj,he⟩ := base hu
        by_cases eq : z=v
        · exact mem_union.mpr (Or.inr (mem_image.mpr ⟨j,eq ▸ hj,he⟩))
        · have dh : k+2≤G.degree z := (deg z v eq).resolve_right (by omega)
          exact mem_union.mpr (Or.inl (mem_image.mpr ⟨j,mem_filter.mpr
            ⟨(mem_filter.mp hj).1,z,hz,Or.inr dh,hj⟩,he⟩))
      have c1 := card_le_card sub
      have c2 := card_union_le (I.image p.getVert) (PinVertices p v)
      have c3 := card_image_le (s:=I) (f:=p.getVert)
      rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp] at c2
      omega
    · have sub : componentPins C ⊆ I.image p.getVert := by
        intro u hu
        obtain ⟨z,hz,j,hj,he⟩ := base hu
        have dh : k+2≤G.degree z := by
          apply Classical.byContradiction
          intro hn
          exact low ⟨z,hz,Nat.lt_of_not_ge hn⟩
        exact mem_image.mpr ⟨j,mem_filter.mpr ⟨(mem_filter.mp hj).1,z,hz,Or.inr dh,hj⟩,he⟩
      have c1 := card_le_card sub
      have c2 := card_image_le (s:=I) (f:=p.getVert)
      omega
  have sep {i j : Nat} (hi : i∈I) (hj : j∈I) (e : i<j) : i+2≤j := by
    obtain ⟨u,hu,du,hi⟩ := Idata hi
    obtain ⟨v,hv,dv,hj⟩ := Idata hj
    by_cases eq : u=v
    · subst v
      apply Classical.byContradiction
      intro nLe
      have eLt : j < i+2 := Nat.lt_of_not_ge nLe
      have ij : i+1=j := by omega
      have fl : p.getVert j ∈ FlankVertices p u := mem_image.mpr
        ⟨j,mem_union.mpr (Or.inr (mem_image.mpr ⟨i,hi,ij⟩)),rfl⟩
      have pB := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary (hO u hu)
        (mem_image.mpr ⟨j,hj,rfl⟩)
      exact (mem_sdiff.mp (flanks_outside_boundary hc hp (hO u hu) fl)).2 pB
    · obtain ⟨q,hq,hS⟩ := hJ u hu v hv
      have pos : 0 < q.length := by
        cases q with
        | nil => exact (eq rfl).elim
        | cons e q => simp
      have hd := gap_three_of_linked_pins hp hi hj e q hq pos (fun z hz => hO z (hS z hz))
      omega
  let J := (I.erase 1).erase (p.length-1)
  have Jsize : I.card ≤ J.card+2 := by
    have add (S : Finset Nat) (i : Nat) : S.card ≤ (S.erase i).card+1 := by
      by_cases h : i ∈ S
      · rw [card_erase_add_one h]
      · rw [erase_eq_of_not_mem h]
        omega
    have c1 := add I 1
    have c2 := add (I.erase 1) (p.length-1)
    change (I.erase 1).card ≤ J.card+1 at c2
    omega
  let f (j : Nat) := if G.Adj b (p.getVert j) then j-1 else j
  let U := J.image f
  have bounds (j : Nat) (hj : j ∈ J) : 2≤j ∧ j+2≤p.length ∧ j∈I := by
    obtain ⟨h1,h2,h3⟩ := mem_erase.mp hj |>.imp_right mem_erase.mp
    obtain ⟨z,hz,dz,jz⟩ := Idata h3
    have ip := Graffiti189LongestPath.Rigidity.pin_pos hp (hO z hz) jz
    have il := (Graffiti189LongestPath.pin_data jz).1
    exact ⟨by omega,by omega,h3⟩
  have uj : U.card = J.card := by
    apply card_image_iff.mpr
    intro i hi j hj ef
    have hi' := (bounds i hi).2.2
    have hj' := (bounds j hj).2.2
    rcases lt_trichotomy i j with h|h|h
    · have ell := sep hi' hj' h
      simp only [f] at ef
      split at ef <;> split at ef <;> omega
    · exact h
    · have ell := sep hj' hi' h
      simp only [f] at ef
      split at ef <;> split at ef <;> omega
  have um {t : Nat} (ht : t ∈ U) : t < p.length ∧ t∉Graffiti189LongestPath.Rigidity.LeftMarks p ∧ t∉Graffiti189LongestPath.Rigidity.RightMarks p := by
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ht
    have hb := bounds j hj
    obtain ⟨z,hz,dz,jz⟩ := Idata hb.2.2
    have zo := hO z hz
    have few : (Pins p z).card≤2 := by
      obtain ⟨t,ht,et⟩ := someOff z hz
      exact at_most_two_pins_with_omitted_neighbor hc k hp zo
        (distanceTwo_le_of_even (k+2) z (cap z)) conn ht et
    have noGap {m : Nat} (hm : m∈Pins p z) : m+2∉Pins p z := by
      intro hq
      by_cases zh : k+2≤G.degree z
      · exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hMin zo zh m hm).2 hq
      have k4 : 4≤k := dz.resolve_right zh
      have zD : k≤G.degree z := by
        rw [← G.card_neighborFinset_eq_degree]
        apply Graffiti189LongestPath.boundary_card_of_connectivity k conn (A:={z}) (x:=z) (a:=a)
        · exact mem_singleton_self _
        · exact fun e => zo ((mem_singleton.mp e) ▸ p.start_mem_support)
        · exact fun e => (Graffiti189LongestPath.no_endpoints hp zo).1 ((G.mem_neighborFinset z a).mp e)
        · exact Finset.disjoint_left.mpr (by
            intro v hv ev
            have hh := (G.mem_neighborFinset z v).mp ev
            exact hh.ne (mem_singleton.mp hv).symm)
        · intro v hv w _ e
          exact (G.mem_neighborFinset z w).mpr ((mem_singleton.mp hv) ▸ e)
      have psub : ({m,m+2}:Finset Nat) ⊆ Pins p z := by
        intro t ht
        simp only [mem_insert,mem_singleton] at ht
        exact ht.elim (fun e => e.symm ▸ hm) (fun e => e.symm ▸ hq)
      have pcard : ({m,m+2}:Finset Nat).card=2 := by simp
      have eq : Pins p z = {m,m+2} := (eq_of_subset_of_card_le psub (by omega)).symm
      have zz : z ≠ p.getVert (m+1) := fun e => zo (e.symm ▸ p.getVert_mem_support (m+1))
      have md := (deg z (p.getVert (m+1)) zz).resolve_left zh
      have hs := (sum_degree_gap_exchange hc (k+2) cap hMin.1 zo m eq).2 (by omega)
      omega
    have hpair : PairedPins p z = ∅ := eq_empty_iff_forall_not_mem.mpr (by
      intro m hm
      obtain ⟨hm,q,hq,e|e⟩ := mem_filter.mp hm
      · exact noGap hq (e.symm ▸ hm)
      · exact noGap hm (e.symm ▸ hq))
    have hnot := not_both_end_chords hc k cap conn hp zo few hpair jz ⟨hb.1,hb.2.1⟩
    by_cases eh : G.Adj b (p.getVert j)
    · have ff : f j = j-1 := if_pos eh
      rw [ff]
      refine ⟨by omega,fun h => ?_,fun h => ?_⟩
      · have ep := (mem_filter.mp h).2
        have e : j-1+1=j := by omega
        rw [e] at ep
        exact hnot ⟨ep,eh⟩
      · exact end_not_adj_pin_predecessor hp zo jz (mem_filter.mp h).2
    · have ff : f j = j := if_neg eh
      rw [ff]
      exact ⟨by omega,fun h => start_not_adj_pin_successor hp zo jz (mem_filter.mp h).2,
        fun h => eh (mem_filter.mp h).2⟩
  have dis : Disjoint (Graffiti189LongestPath.Rigidity.LeftMarks p) (Graffiti189LongestPath.Rigidity.RightMarks p) :=
    disjoint_left.mpr (by
      intro v hl hr
      exact not_adj_both_end_marks hp hx (p.getVert_mem_support i) ex
        (mem_range.mp (mem_filter.mp hl).1) (mem_filter.mp hl).2 (mem_filter.mp hr).2)
  have uh : Disjoint (Graffiti189LongestPath.Rigidity.LeftMarks p ∪ Graffiti189LongestPath.Rigidity.RightMarks p) U :=
    disjoint_left.mpr (fun u hu hu' => (mem_union.mp hu).elim (um hu').2.1 (um hu').2.2)
  have pLen : G.degree a + G.degree b + J.card ≤ p.length := by
    have sub : (Graffiti189LongestPath.Rigidity.LeftMarks p ∪ Graffiti189LongestPath.Rigidity.RightMarks p) ∪ U ⊆ range p.length :=
      union_subset (union_subset (filter_subset _ _) (filter_subset _ _))
        (fun _ h => mem_range.mpr (um h).1)
    have cs := card_le_card sub
    rwa [card_union_of_disjoint uh,card_union_of_disjoint dis,uj,
      Graffiti189LongestPath.Rigidity.card_leftMarks hp,
      Graffiti189LongestPath.Rigidity.card_rightMarks hp,card_range] at cs
  have dH : Disjoint H p.support.toFinset :=
    disjoint_left.mpr (fun w hh hh' => hO w hh (List.mem_toFinset.mp hh'))
  have cs := card_le_univ (H ∪ p.support.toFinset)
  rw [card_union_of_disjoint dH, List.toFinset_card_of_nodup hp.1.support_nodup,
    length_support] at cs
  have h4k : 4≤k := by omega
  simp only [if_pos h4k,Nat.add_zero] at atLeast
  have few (z : V) (hz : z∈H) : (Pins p z).card≤2 := by
    obtain ⟨t,ht,et⟩ := someOff z hz
    exact at_most_two_pins_with_omitted_neighbor hc k hp (hO z hz)
      (distanceTwo_le_of_even (k+2) z (cap z)) conn ht et
  have low (z : V) (hz : z∈H) : k+2-2≤G.degree z := by
    simp only [Nat.add_sub_cancel]
    rw [← G.card_neighborFinset_eq_degree]
    apply Graffiti189LongestPath.boundary_card_of_connectivity k conn (A:={z}) (x:=z) (a:=a)
    · exact mem_singleton_self _
    · exact fun e => hO z hz ((mem_singleton.mp e) ▸ p.start_mem_support)
    · exact fun e => (Graffiti189LongestPath.no_endpoints hp (hO z hz)).1 ((G.mem_neighborFinset z a).mp e)
    · exact Finset.disjoint_left.mpr (by
        intro v hv ev
        have hh := (G.mem_neighborFinset z v).mp ev
        exact hh.ne (mem_singleton.mp hv).symm)
    · intro v hv w _ e
      exact (G.mem_neighborFinset z w).mpr ((mem_singleton.mp hv) ▸ e)
  by_cases spine : 17≤p.length
  · by_cases plen : p.length=17
    · by_cases h5 : H.card=5
      · exact CloseFive17R.no_five hc k hk cap conn deg hp hMin C h5 plen da db few low
      · exact SixWingFrontier.no_six hc k hk cap conn deg hp hMin C (by change H.card=6; omega) plen few low
    · have plen' : p.length=18 := by omega
      have h5 : H.card=5 := by omega
      exact CloseFive18.no_five hc k hk cap conn deg hp hMin C h5 plen' da db few low
  let Q := G.induce (H:Set V)
  have qcard : Fintype.card ↥(H:Set V) = H.card := Fintype.card_coe H
  have inner (v : ↥(H:Set V)) :
      G.degree v.val ≤ (Pins p v.val).card+Q.degree v := by
    exact Graffiti189LongestPath.WideWing.inside_deg hp C v
  have lo2 (v : ↥(H:Set V)) : 2≤Q.degree v := by
    have e := inner v
    have f := few v.val v.property
    have g := low v.val v.property
    omega
  have hh4 (v : ↥(H:Set V)) (vv : k+2≤G.degree v.val) : 4≤Q.degree v := by
    have e := inner v
    have f := few v.val v.property
    omega
  have hihi (u v : ↥(H:Set V)) (ne : u≠v) : 4≤Q.degree u ∨ 4≤Q.degree v :=
    (deg u.val v.val (fun e => ne (Subtype.ext e))).imp (hh4 u) (hh4 v)
  have allI {v : V} (hv : v∈H) {m : Nat} (hm : m∈Pins p v) : m∈I :=
    mem_filter.mpr ⟨(mem_filter.mp hm).1,v,hv,Or.inl (by omega),hm⟩
  have coreGap {u v : V} (hu : u∈H) (hv : v∈H) (ne : u≠v)
      {m n : Nat} (hm : m∈Pins p u) (hn : n∈Pins p v) (hh : m<n) : m+6≤n := by
    by_cases h : H.card≤5
    · have z := wide_gap_of_small_wing hp C (k+2) low deg few (by
        change H.card+7≤2*(k+2); omega) hu hv ne hm hn hh
      change m+H.card+1≤n at z
      omega
    · let u' : ↥(H:Set V) := ⟨u,hu⟩
      let v' : ↥(H:Set V) := ⟨v,hv⟩
      obtain ⟨q,qp,ql⟩ := MarkedWingPathNine.long_marked_path (D:=Q)
        (show 6≤Fintype.card ↥(H:Set V) ∧ Fintype.card ↥(H:Set V)≤9 by omega)
        lo2 hihi (show u'≠v' from fun e => ne (congrArg Subtype.val e))
      let f : Q→g G := ⟨Subtype.val,fun e => e⟩
      have t := terminal_length_le_gap hp hm hn hh (q.map f)
        (map_isPath_of_injective Subtype.val_injective qp) (by
          intro w ww
          rw [support_map] at ww
          obtain ⟨v,_,rfl⟩ := List.mem_map.mp ww
          exact hO _ v.property)
      rw [length_map] at t
      omega
  have cheap {m n : Nat} (hm : m∈I) (hn : n∈I) (mn : m<n) (short : n<m+6) :
      ∃ u∈H, m∈Pins p u ∧ n∈Pins p u ∧ ∀ v∈H, (m∈Pins p v ∨ n∈Pins p v) → v=u := by
    obtain ⟨u,hu,_,hmu⟩ := Idata hm
    obtain ⟨v,hv,_,hnv⟩ := Idata hn
    have e : u=v := Classical.byContradiction (fun h => (Nat.not_le_of_lt short) (coreGap hu hv h hmu hnv mn))
    subst v
    exact ⟨u,hu,hmu,hnv,fun v hv h => Classical.byContradiction (fun ne => (Nat.not_le_of_lt short)
      (h.elim (fun h => coreGap hv hu ne h hnv mn) (fun h => coreGap hu hv (Ne.symm ne) hmu h mn)))⟩
  have dist {m n : Nat} (hm : m∈I) (hn : n∈I) (mn : m<n) : m+3≤n := by
    have h2 := sep hm hn mn
    apply Nat.le_of_not_gt
    intro ns
    obtain ⟨v,hv,hmv,hnv,_⟩ := cheap hm hn mn (by omega)
    have eq : Pins p v = {m,m+2} := by
      have sub : ({m,m+2}:Finset Nat) ⊆ Pins p v := by
        intro r h
        simp only [mem_insert,mem_singleton] at h
        rcases h with rfl|rfl
        · exact hmv
        · rwa [show m+2=n by omega]
      have ff := few v hv
      exact (eq_of_subset_of_card_le sub (by simpa using ff)).symm
    have vd := low v hv
    have vo := hO v hv
    have ne : v ≠ p.getVert (m+1) := fun e => vo (e.symm ▸ p.getVert_mem_support _)
    have dd := deg v (p.getVert (m+1)) ne
    have se := sum_degree_gap_exchange hc (k+2) cap hMin.1 vo m eq
    by_cases dh : k+2≤G.degree v
    · have bb := (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hMin vo dh m hmv).2
      exact bb (by rwa [show m+2=n by omega])
    · have ss := se.2 (by omega)
      omega
  have bounds {m : Nat} (hm : m∈I) : 1≤m ∧ m+1≤p.length := by
    obtain ⟨v,hv,_,hh⟩ := Idata hm
    have h := (Graffiti189LongestPath.pin_data hh).1
    have hh₁ := Graffiti189LongestPath.Rigidity.pin_pos hp (hO v hv) hh
    omega
  have sorted : ∃ a' b' c' d' : Nat,
      a'∈I ∧ b'∈I ∧ c'∈I ∧ d'∈I ∧ a'<b' ∧ b'<c' ∧ c'<d' := by
    have cn : 4≤I.card := by omega
    let a' := I.min' (by apply card_pos.mp; omega)
    have aI : a'∈I := min'_mem _ _
    let I₁ := I.erase a'
    have c₁ : I₁.card+1=I.card := card_erase_add_one aI
    let b' := I₁.min' (by apply card_pos.mp; omega)
    have bI : b'∈I₁ := min'_mem _ _
    let I₂ := I₁.erase b'
    have c₂ : I₂.card+1=I₁.card := card_erase_add_one bI
    let c' := I₂.min' (by apply card_pos.mp; omega)
    have dI : c'∈I₂ := min'_mem _ _
    let I₃ := I₂.erase c'
    have c₃ : I₃.card+1=I₂.card := card_erase_add_one dI
    let d' := I₃.min' (by apply card_pos.mp; omega)
    have eI : d'∈I₃ := min'_mem _ _
    have h₁ := min'_le I b' (mem_erase.mp bI).2
    have h₂ := min'_le I₁ c' (mem_erase.mp dI).2
    have h₃ := min'_le I₂ d' (mem_erase.mp eI).2
    have ne₁ := (mem_erase.mp bI).1
    have ne₂ := (mem_erase.mp dI).1
    have ne₃ := (mem_erase.mp eI).1
    exact ⟨a',b',c',d',aI,(mem_erase.mp bI).2,
      (mem_erase.mp (mem_erase.mp dI).2).2,(mem_erase.mp (mem_erase.mp (mem_erase.mp eI).2).2).2,
      by omega,by omega,by omega⟩
  obtain ⟨r,s,t,u,hr,hs,ht,hu,rs,st,tu⟩ := sorted
  have no_double {a' b' c' : Nat} (ha : a'∈I) (hb : b'∈I) (hc' : c'∈I)
      (ab : a'<b') (bc : b'<c') (s1 : b'<a'+6) (s2 : c'<b'+6) : False := by
    obtain ⟨x₁,hx₁,ha',hb',unique₁⟩ := cheap ha hb ab s1
    obtain ⟨x₂,hx₂,hb'',hc'',_⟩ := cheap hb hc' bc s2
    have eq := unique₁ x₂ hx₂ (Or.inr hb'')
    subst x₂
    have sub : ({a',b',c'}:Finset Nat) ⊆ Pins p x₁ := by
      intro m hm
      simp only [mem_insert,mem_singleton] at hm
      rcases hm with rfl|rfl|rfl
      · exact ha'
      · exact hb'
      · exact hc''
    have cnt := card_le_card sub
    have e : ({a',b',c'}:Finset Nat).card=3 := by
      simp [show a'≠b' by omega,show a'≠c' by omega,show b'≠c' by omega]
    have f := few x₁ hx₁
    omega
  have dr := dist hr hs rs
  have ds := dist hs ht st
  have dt := dist ht hu tu
  have br := (bounds hr).1
  have bu := (bounds hu).2
  have totalI : I.card≤4 := by
    have q := Graffiti189LongestPath.WideWing.two_per_block I 9 2 (by decide)
      (by intro i ii; have q := (bounds ii).2; omega)
      (by intro i ii j jj l ll ij jl
          have t := dist ii jj ij
          have s := dist jj ll jl
          by_contra! e
          exact no_double ii jj ll ij jl (by omega) (by omega))
    omega
  have middle : s+6≤t := by
    apply Nat.le_of_not_gt
    intro m
    have l : r+6≤s := Nat.le_of_not_gt (fun h => no_double hr hs ht rs st h m)
    have rr : t+6≤u := Nat.le_of_not_gt (fun h => no_double hs ht hu st tu m h)
    omega
  obtain ⟨u₁,hu₁,pr₁,ps₁,only₁⟩ := cheap hr hs rs (by omega)
  obtain ⟨u₂,hu₂,pt₂,pu₂,only₂⟩ := cheap ht hu tu (by omega)
  have ne : u₁≠u₂ := by
    intro e
    have tc := Finset.two_lt_card.mpr ⟨r,pr₁,s,ps₁,t,e.symm ▸ pt₂,by omega,by omega,by omega⟩
    have ft := few u₁ hu₁
    omega
  have all : I={r,s,t,u} := by
    apply (eq_of_subset_of_card_le _ _).symm
    · intro m hm
      simp only [mem_insert,mem_singleton] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> assumption
    · rw [show ({r,s,t,u}:Finset Nat).card=4 by
        simp [show r≠s by omega,show r≠t by omega,show r≠u by omega,
          show s≠t by omega,show s≠u by omega,show t≠u by omega]]
      exact totalI
  have noPin (v : V) (hv : v∈H) (v₁ : v≠u₁) (v₂ : v≠u₂) : Pins p v=∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro m hm
    have mi := allI hv hm
    rw [all] at mi
    simp only [mem_insert,mem_singleton] at mi
    rcases mi with rfl|rfl|rfl|rfl
    · exact v₁ (only₁ v hv (Or.inl hm))
    · exact v₁ (only₁ v hv (Or.inr hm))
    · exact v₂ (only₂ v hv (Or.inl hm))
    · exact v₂ (only₂ v hv (Or.inr hm))
  obtain ⟨z,zHigh⟩ : ∃ z : ↥(H:Set V),∀ v : ↥(H:Set V),v≠z → k+2≤G.degree v.val := by
    by_cases h : ∃ z : ↥(H:Set V),G.degree z.val<k+2
    · obtain ⟨z,l⟩ := h
      exact ⟨z,fun v ne => (deg v.val z.val (fun e => ne (Subtype.ext e))).resolve_right (by omega)⟩
    · exact ⟨⟨u₁,hu₁⟩,fun v _ => Nat.le_of_not_gt (fun e => h ⟨v,e⟩)⟩
  let X : ↥(H:Set V) := ⟨u₁,hu₁⟩
  let Y : ↥(H:Set V) := ⟨u₂,hu₂⟩
  have XY : X≠Y := fun e => ne (congrArg Subtype.val e)
  have dense (v : ↥(H:Set V)) (hX : v≠X) (hY : v≠Y) (hz : v≠z) : 6≤Q.degree v := by
    have p := noPin v.val v.property (fun e => hX (Subtype.ext e)) (fun e => hY (Subtype.ext e))
    have q := inner v
    have h := zHigh v hz
    rw [p,card_empty,Nat.zero_add] at q
    omega
  have narrow : H.card≤9 := by omega
  by_cases h6 : H.card≤6
  · have h := (card_le_univ (s:=({X,Y,z}:Finset ↥(H:Set V))))
    have three : ({X,Y,z}:Finset ↥(H:Set V)).card≤3 := by
      have p := card_insert_le X ({Y,z}:Finset ↥(H:Set V))
      have q := card_insert_le Y ({z}:Finset ↥(H:Set V))
      rw [card_singleton] at q
      omega
    have out : ∃ v : ↥(H:Set V),v≠X ∧ v≠Y ∧ v≠z := by
      apply Classical.byContradiction
      intro no
      have incl : (univ:Finset ↥(H:Set V))⊆{X,Y,z} := by
        intro v _
        by_cases e : v=X
        · simp [e]
        by_cases f : v=Y
        · simp [f]
        by_cases g : v=z
        · simp [g]
        exact (no ⟨v,e,f,g⟩).elim
      have h := card_le_card incl
      rw [card_univ,qcard] at h
      omega
    obtain ⟨v,vX,vY,vZ⟩ := out
    have d := dense v vX vY vZ
    have e := Q.degree_lt_card_verts v
    omega
  have bigRoute : ∃ q : Q.Walk X Y,q.IsPath ∧ (if H.card=7 then 8 else 7)≤q.length+2 := by
    by_cases seven : H.card=7
    · obtain ⟨q,pp,pl⟩ := DenseOwnerRoute.route_seven (D:=Q) (qcard.trans seven) X Y z XY lo2
        (fun v vz => hh4 v (zHigh v vz)) dense
      exact ⟨q,pp,by simp [seven]; omega⟩
    · by_cases eight : H.card=8
      · obtain ⟨q,pp,pl⟩ := DenseOwnerRoute.route_eight (D:=Q) (qcard.trans eight) X Y z XY lo2
          (fun v vz => hh4 v (zHigh v vz)) dense
        exact ⟨q,pp,by simp [seven]; omega⟩
      · obtain ⟨q,pp,pl⟩ := DenseOwnerRouteNine.route_nine (D:=Q) (qcard.trans (by omega)) X Y z XY lo2
          (fun v vz => hh4 v (zHigh v vz)) dense
        exact ⟨q,pp,by simp [seven]; omega⟩
  obtain ⟨q,pp,pl⟩ := bigRoute
  let f : Q→g G := ⟨Subtype.val,fun e => e⟩
  have g := terminal_length_le_gap hp ps₁ pt₂ st (q.map f)
    (map_isPath_of_injective Subtype.val_injective pp) (by
      intro w ww
      rw [support_map] at ww
      obtain ⟨vv,_,rfl⟩ := List.mem_map.mp ww
      exact hO _ vv.property)
  rw [length_map] at g
  have extreme :
      (H.card=7 ∧ p.length=16 ∧ r=1 ∧ s=4 ∧ t=12 ∧ u=15) ∨
      (H.card=8 ∧ p.length=15 ∧ r=1 ∧ s=4 ∧ t=11 ∧ u=14) := by
    by_cases seven : H.card=7
    · simp [seven] at pl
      exact Or.inl ⟨seven,by omega,by omega,by omega,by omega,by omega⟩
    · simp [seven] at pl
      exact Or.inr ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
  have hh : H.card=7 ∨ H.card=8 := extreme.imp And.left And.left
  have cardinal (v : ↥(H:Set V)) : (DenseInsideCharges.inner G H v.val).card=Q.degree v := by
    rw [←Q.card_neighborFinset_eq_degree]
    refine card_bij' (s:=H.filter (G.Adj v.val)) (t:=Q.neighborFinset v)
      (fun w ww => (⟨w,(mem_filter.mp ww).1⟩ : ↥(H:Set V)))
      (fun w _ => w.val) ?_ ?_ ?_ ?_
    · intro w ww
      exact (Q.mem_neighborFinset _ _).mpr (mem_filter.mp ww).2
    · intro w ww
      exact mem_filter.mpr ⟨w.property,(Q.mem_neighborFinset _ _).mp ww⟩
    · intro w _
      rfl
    · intro w _
      exact Subtype.ext rfl
  have d4 (v : V) (hv : v∈H) (vz : v≠z.val) : 4≤(DenseInsideCharges.inner G H v).card := by
    let v' : ↥(H:Set V) := ⟨v,hv⟩
    rw [show (DenseInsideCharges.inner G H v).card=Q.degree v' from cardinal v']
    exact hh4 v' (zHigh v' (fun e => vz (congrArg Subtype.val e)))
  have d6 (v : V) (hv : v∈H) (vx : v≠u₁) (vy : v≠u₂) (vz : v≠z.val) :
      6≤(DenseInsideCharges.inner G H v).card := by
    let v' : ↥(H:Set V) := ⟨v,hv⟩
    rw [show (DenseInsideCharges.inner G H v).card=Q.degree v' from cardinal v']
    exact dense v' (fun e => vx (congrArg Subtype.val e))
      (fun e => vy (congrArg Subtype.val e)) (fun e => vz (congrArg Subtype.val e))
  have pinsPair (v : V) (hv : v∈H) (m n : ℕ) (ne : m≠n)
      (mm : m∈Pins p v) (nn : n∈Pins p v) : Pins p v={m,n} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro a ha
      simp only [mem_insert,mem_singleton] at ha
      exact ha.elim (fun e => e.symm ▸ mm) (fun e => e.symm ▸ nn)
    · rw [show ({m,n}:Finset ℕ).card=2 by simp [ne]]
      exact few v hv
  have c6 : ∀ v,(DistanceTwo G v).card≤6 := fun v =>
    (distanceTwo_le_of_even (k+2) v (cap v)).trans (by omega)
  rcases deg u₁ u₂ ne with l|rr
  · have ni : 4≤(DenseInsideCharges.inner G H u₁).card := by
      rw [show (DenseInsideCharges.inner G H u₁).card=Q.degree X from cardinal X]
      exact hh4 X l
    have budget := DenseInsideCharges.inside hc H u₁ u₂ z.val hu₁ hh ni d4 d6
    have pins := pinsPair u₁ hu₁ r s (by omega) pr₁ ps₁
    have only := fun v hv pin => only₁ v hv (Or.inl pin)
    rcases extreme with ⟨_,ll,lr,ls,_,_⟩|⟨_,ll,lr,ls,_,_⟩
    · rw [lr,ls] at pins
      have d := DenseEndpointLayout.left16 hc hp hO hu₁ c6 budget ll pins
        (fun v hv pin => only v hv (lr.symm ▸ pin))
      omega
    · rw [lr,ls] at pins
      have d := DenseEndpointLayout.left15 hc hp hO hu₁ c6 budget ll pins
        (fun v hv pin => only v hv (lr.symm ▸ pin))
      omega
  · have ni : 4≤(DenseInsideCharges.inner G H u₂).card := by
      rw [show (DenseInsideCharges.inner G H u₂).card=Q.degree Y from cardinal Y]
      exact hh4 Y rr
    have budget := DenseInsideCharges.inside hc H u₂ u₁ z.val hu₂ hh ni d4
      (fun v hv vx vy vz => d6 v hv vy vx vz)
    have pins := pinsPair u₂ hu₂ u t (by omega) pu₂ pt₂
    have only := fun v hv pin => only₂ v hv (Or.inr pin)
    rcases extreme with ⟨_,ll,_,_,lt,lu⟩|⟨_,ll,_,_,lt,lu⟩
    · rw [lt,lu] at pins
      have d := DenseEndpointLayout.right16 hc hp hO hu₂ c6 budget ll pins
        (fun v hv pin => only v hv (lu.symm ▸ pin))
      omega
    · rw [lt,lu] at pins
      have d := DenseEndpointLayout.right15 hc hp hO hu₂ c6 budget ll pins
        (fun v hv pin => only v hv (lu.symm ▸ pin))
      omega

theorem traceable_order_twenty_four (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<4 → (G.induce ((↑S:Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (bound : Fintype.card V≤24) :
    ∃ (a b : V) (p : G.Walk a b),p.IsPath ∧ ∀ v,v∈p.support := by
  classical
  by_contra fail
  exact traceable_order_twenty_four_aux hc 4 rfl cap conn degree fail bound

#print axioms traceable_order_twenty_four
end Graffiti189LongestPath.SixFourOrderTwentyFour
