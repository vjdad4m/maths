import BorderWing189
import Interior189
import GapStrong189
open private Graffiti189LongestPath.WideWing.two_per_block from WideWing189
open Graffiti189LongestPath.BorderWing
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
set_option maxHeartbeats 1500000
namespace Graffiti189LongestPath.UltraOrder
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For d=k+2≥7 and connectivity at least k, a nontraceable graph under
the exact even-distance cap has order at least 5d−8. -/
theorem order_lower_wings_sharp (hc : G.Connected) (k : Nat) (hk : 5 ≤ k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V, u ≠ v → k+2 ≤ G.degree u ∨ k+2 ≤ G.degree v)
    (fail : ¬∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support) :
    5*k+2 ≤ Fintype.card V := by
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
  by_cases big : 2*k-1 ≤ H.card
  · omega
  have border : H.card+6≤2*(k+2) := by omega
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
  have spaced (z : V) (hz : z∈H) (t : V) (ht : t∈H)
      (r : Nat) (hr : r∈Pins p z) (s : Nat) (hs : s∈Pins p t) (rs : r<s) :
      r+3≤s := by
    by_cases ne : z≠t
    · obtain ⟨q,hq,hS⟩ := hJ z hz t ht
      have pos : 0<q.length := by
        cases q with
        | nil => exact (ne rfl).elim
        | cons e q => simp
      exact gap_three_of_linked_pins hp hr hs rs q hq pos (fun v hv => hO v (hS v hv))
    obtain rfl : z=t := Classical.byContradiction ne
    have ir := (Graffiti189LongestPath.pin_data hr).1
    have is := (Graffiti189LongestPath.pin_data hs).1
    have zoff := hO z hz
    by_contra! failure
    have h : s=r+1 ∨ s=r+2 := by omega
    rcases h with h|h
    · have fl : p.getVert s ∈ FlankVertices p z := mem_image.mpr
        ⟨s,mem_union.mpr (Or.inr (mem_image.mpr ⟨r,hr,h.symm⟩)),rfl⟩
      have pB := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary zoff
        (mem_image.mpr ⟨s,hs,rfl⟩)
      exact (mem_sdiff.mp (flanks_outside_boundary hc hp zoff fl)).2 pB
    · have hq : r+2∈Pins p z := h ▸ hs
      by_cases zh : k+2≤G.degree z
      · exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hMin zoff zh r hr).2 hq
      have psub : ({r,r+2}:Finset Nat) ⊆ Pins p z := by
        intro u hh
        simp only [mem_insert,mem_singleton] at hh
        exact hh.elim (fun e => e.symm ▸ hr) (fun e => e.symm ▸ hq)
      have pcard : ({r,r+2}:Finset Nat).card=2 := by simp
      have ff := few z hz
      have eq : Pins p z = {r,r+2} := (eq_of_subset_of_card_le psub (by omega)).symm
      have zz : z ≠ p.getVert (r+1) := fun e => zoff (e.symm ▸ p.getVert_mem_support (r+1))
      have md := (deg z (p.getVert (r+1)) zz).resolve_left zh
      have hs := (sum_degree_gap_exchange hc (k+2) cap hMin.1 zoff r eq).2 (by omega)
      have kl := low z hz
      omega
  have count (g m : Nat) (short : p.length ≤ m*(g+3)+1)
      (gap : ∀ x∈H,∀ y∈H, x≠y → ∀ i∈Pins p x,∀ j∈Pins p y,i<j → i+g≤j) :
      I.card ≤ 2*m := by
    let I' := I.image (fun i => i-1)
    have position (i : Nat) (hi : i∈I) : 1≤i ∧ i<p.length := by
      obtain ⟨v,hv,_,hm⟩ := Idata hi
      exact ⟨Graffiti189LongestPath.Rigidity.pin_pos hp (hO v hv) hm,(Graffiti189LongestPath.pin_data hm).1⟩
    have shifted : I'.card = I.card := by
      apply card_image_of_injOn
      intro i hi j hj h
      have h₁ := (position i hi).1
      have h₂ := (position j hj).1
      dsimp only at h
      omega
    rw [← shifted]
    apply Graffiti189LongestPath.WideWing.two_per_block I' (g+3) m (by omega)
    · intro i hi
      obtain ⟨j,hj,e⟩ := mem_image.mp hi
      have pos := position j hj
      omega
    · intro r hr s hs t ht rs st
      obtain ⟨i,hi,e₁⟩ := mem_image.mp hr
      obtain ⟨j,hj,e₂⟩ := mem_image.mp hs
      obtain ⟨l,hl,e₃⟩ := mem_image.mp ht
      have hi₁ := (position i hi).1
      have hj₁ := (position j hj).1
      have hl₁ := (position l hl).1
      have ij : i<j := by omega
      have jl : j<l := by omega
      obtain ⟨x,hx,_,ix⟩ := Idata hi
      obtain ⟨y,hy,_,jy⟩ := Idata hj
      obtain ⟨z,hz,_,lz⟩ := Idata hl
      by_cases xy : x=y
      · subst y
        have yz : x≠z := by
          intro e
          subst z
          have ct := Finset.two_lt_card.mpr ⟨i,ix,j,jy,l,lz,by omega,by omega,by omega⟩
          have sm := few x hx
          omega
        have w := gap x hx z hz yz j jy l lz jl
        have v := spaced x hx x hx i ix j jy ij
        omega
      · have w := gap x hx y hy xy i ix j jy ij
        have v := spaced y hy z hz j jy l lz jl
        omega
  by_cases tight : 2*k-2 ≤ H.card
  · apply Classical.byContradiction
    intro no
    have pshort : p.length≤2*(H.card+3)+1 := by omega
    have c := count H.card 2 pshort (by
      intro x hx y hy ne i hi j hj le
      have g := near_border_gap hp C (k+2) (by omega) low deg few border hx hy ne hi hj le
      exact g)
    omega
  have small : H.card+7≤2*(k+2) := by omega
  have bigP (m : Nat) (km : 2*m<k) : m*(H.card+4)+1<p.length := by
    apply Classical.byContradiction
    intro hs
    have ss : p.length≤m*(H.card+1+3)+1 := by
      have ee : H.card+1+3=H.card+4 := by omega
      rw [ee]
      exact Nat.le_of_not_gt hs
    have r := count (H.card+1) m ss (by
      intro x hx y hy ne i hi j hj le
      have g := wide_gap_of_small_wing hp C (k+2) low deg few small hx hy ne hi hj le
      change i+H.card+1≤j at g
      omega)
    omega
  by_cases h7 : k≤6
  · have h := bigP 2 (by omega)
    omega
  by_cases h9 : k≤8
  · have h := bigP 3 (by omega)
    omega
  · have h := bigP 4 (by omega)
    omega
#print axioms order_lower_wings_sharp
end Graffiti189LongestPath.UltraOrder
