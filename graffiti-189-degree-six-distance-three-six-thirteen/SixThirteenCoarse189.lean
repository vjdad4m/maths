import SixThirteenClassify189
import SixThirteenFromGraph189
import SixTwelveClosed189
namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair
open scoped BigOperators
open private Shore shore_disjoint shore_off shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far shore_inside_five from SixDistanceThreeShort189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open private neighbor_subset_of_dark from SixTenRegular189
open private degree_two_from_one_deletion from AdjacentCutFiveTwinThreeGeom189
open FiveAdjacent (shore_swapCut)
open Graffiti189LongestPath.SixThirteenSat (shapeData classify_shape)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000000
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {C D : Cmp G a b}

theorem classified_six_thirteen_shape
    (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ v,(EvenFrom G v).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (six : (Shore C).card=6) (thirteen : (Shore D).card=13)
    (norm : (cutPorts G (Shore C) a).card≤(cutPorts G (Shore C) b).card) :
    ∃ i : Fin 60, ∃ l : ℕ,
      shapeData[i.val]! =
        [(cutPorts G (Shore C) a).card,(cutPorts G (Shore C) b).card,
         (sixBucket G a b (Shore D) 0).card,(sixBucket G a b (Shore D) 1).card,(sixBucket G a b (Shore D) 2).card,(sixBucket G a b (Shore D) 3).card,(sixBucket G a b (Shore D) 4).card,(sixBucket G a b (Shore D) 5).card,(sixBucket G a b (Shore D) 6).card,(sixBucket G a b (Shore D) 7).card,l] ∧
      ∀ z∈Shore D,G.degree z<6 → l=(sixClass G a b z).val+1 := by
  classical
  let pa := cutPorts G (Shore C) a
  let pb := cutPorts G (Shore C) b
  let qa := cutPorts G (Shore D) a
  let qb := cutPorts G (Shore D) b
  let low := (Shore D).filter (fun u=>G.degree u<6)
  let high := (Shore D).filter (fun u=>6≤G.degree u)
  let N := sixBucket G a b (Shore D)
  let E := sixBucket G a b low
  let H := sixBucket G a b high
  have far' : 3≤G.dist b a := by rwa [dist_comm]
  have cd' : swapCut C≠swapCut D := fun e=>cd (swapCut.injective e)
  have cv' : ∀ {z : V},z≠b → z≠a → z∈Shore (swapCut C) ∨ z∈Shore (swapCut D) :=
    fun zb za=>by simpa only [shore_swapCut] using cover za zb
  have six' : (Shore (swapCut C)).card=6 := by rwa [shore_swapCut]
  have thirteen' : (Shore (swapCut D)).card=13 := by rwa [shore_swapCut]
  have ta : 0<pa.card ∧ (cutSeen G (Shore D) a).card≤pa.card ∧ qa.card≤5 ∧ 6≤pa.card+qa.card :=
    cut_shore_six_terminal_data hc far ab conn even degree cd six cover
  have tb : 0<pb.card ∧ (cutSeen G (Shore D) b).card≤pb.card ∧ qb.card≤5 ∧ 6≤pb.card+qb.card := by
    simpa only [shore_swapCut] using
      (cut_shore_six_terminal_data hc far' ab.symm conn even degree cd' six' cv')
  have no (u : V) : ¬(G.Adj a u ∧ G.Adj b u) := no_common_far far
  have pdis : Disjoint pa pb := disjoint_left.mpr (fun u ha hb=>
    no u ⟨(mem_filter.mp ha).2,(mem_filter.mp hb).2⟩)
  have qdis : Disjoint qa qb := disjoint_left.mpr (fun u ha hb=>
    no u ⟨(mem_filter.mp ha).2,(mem_filter.mp hb).2⟩)
  let Sdark := Shore C \ (pa∪pb)
  have spanP : pa∪pb⊆Shore C := union_subset (filter_subset _ _) (filter_subset _ _)
  have spanQ : qa∪qb⊆Shore D := union_subset (filter_subset _ _) (filter_subset _ _)
  have small := card_le_card spanP
  rw [card_union_of_disjoint pdis,six] at small
  have darkCard : Sdark.card+pa.card+pb.card=6 := by
    have h := card_sdiff_add_card_eq_card spanP
    rw [card_union_of_disjoint pdis,six] at h
    change Sdark.card+(pa.card+pb.card)=6 at h
    omega
  let allLow := (univ:Finset V).filter (fun v=>G.degree v<6)
  have capLow : allLow.card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra uv
    rcases degree u v uv with du|dv
    · exact (Nat.not_lt_of_ge du) (mem_filter.mp hu).2
    · exact (Nat.not_lt_of_ge dv) (mem_filter.mp hv).2
  have lm : Sdark∪low⊆allLow := by
    intro v vv
    rcases mem_union.mp vv with ss|dd
    · obtain ⟨vc,none⟩ := mem_sdiff.mp ss
      have va : ¬G.Adj a v := fun h=>none (mem_union_left _ (mem_filter.mpr ⟨vc,h⟩))
      have vb : ¬G.Adj b v := fun h=>none (mem_union_right _ (mem_filter.mpr ⟨vc,h⟩))
      have d := cut_dark_degree C vc va vb
      exact mem_filter.mpr ⟨mem_univ _,by omega⟩
    · exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp dd).2⟩
  have dl : Disjoint Sdark low := (shore_disjoint cd).mono sdiff_subset (filter_subset _ _)
  have lowSize := (card_le_card lm).trans capLow
  rw [card_union_of_disjoint dl] at lowSize
  have eSum : (E 0).card+(E 1).card+(E 2).card+(E 3).card+
      (E 4).card+(E 5).card+(E 6).card+(E 7).card=low.card := sixBuckets_card (G:=G) a b low
  have nSum : (N 0).card+(N 1).card+(N 2).card+(N 3).card+
      (N 4).card+(N 5).card+(N 6).card+(N 7).card=13 := (sixBuckets_card (G:=G) a b (Shore D)).trans thirteen
  have hE (i : Fin 8) : (H i).card+(E i).card=(N i).card :=
    sixBucket_filter_split a b (Shore D) i
  have dat (i : Fin 8) {v : V} (vm : v∈N i) : v∈Shore D ∧ sixClassSpec G a b v i :=
    (mem_sixBucket (no v) i).mp vm
  have highdat (i : Fin 8) {v : V} (vm : v∈H i) :
      v∈Shore D ∧ 6≤G.degree v ∧ sixClassSpec G a b v i := by
    have h := (mem_sixBucket (no v) i).mp vm
    exact ⟨(mem_filter.mp h.1).1,(mem_filter.mp h.1).2,h.2⟩
  have chooseHigh (i : Fin 8) (n : (E i).card<(N i).card) :
      ∃ u∈Shore D, 6≤G.degree u ∧ sixClassSpec G a b u i := by
    obtain ⟨u,un,uh⟩ := sixBucket_lt_has_high a b (Shore D) i n
    obtain ⟨ud,us⟩ := dat i un
    exact ⟨u,ud,uh,us⟩
  have qaEq : qa=N 0∪N 1 := by
    ext v
    simp [qa,cutPorts,N,mem_sixBucket (no v),sixClassSpec]
    tauto
  have qbEq : qb=N 2∪N 3 := by
    ext v
    simp [qb,cutPorts,N,mem_sixBucket (no v),sixClassSpec]
    tauto
  have caEq : qa.card=(N 0).card+(N 1).card := by
    rw [qaEq,card_union_of_disjoint (sixBuckets_disjoint a b _ _ (by decide : (0:Fin 8)≠1))]
  have cbEq : qb.card=(N 2).card+(N 3).card := by
    rw [qbEq,card_union_of_disjoint (sixBuckets_disjoint a b _ _ (by decide : (2:Fin 8)≠3))]
  have vc (i j k : Fin 8) (ij : i≠j) (ik : i≠k) (jk : j≠k) {r : V}
      (seen : ∀ z∈N i∪N j∪N k,G.dist r z=2) :
      (N i).card+(N j).card+(N k).card≤(cutSeen G (Shore D) r).card := by
    have dn : Disjoint (N i∪N j) (N k) := by
      rw [disjoint_union_left]
      exact ⟨sixBuckets_disjoint a b _ _ ik,sixBuckets_disjoint a b _ _ jk⟩
    have sub : N i∪N j∪N k⊆cutSeen G (Shore D) r := by
      intro z zz
      refine mem_cutSeen.mpr ⟨?_,seen z zz⟩
      rcases mem_union.mp zz with zz|zz
      · exact (mem_union.mp zz).elim (fun h=>(dat i h).1) (fun h=>(dat j h).1)
      · exact (dat k zz).1
    have card := card_le_card sub
    rwa [card_union_of_disjoint dn,card_union_of_disjoint (sixBuckets_disjoint a b _ _ ij)] at card
  have aVis := (vc 3 4 6 (by decide) (by decide) (by decide) (r:=a) (by
    intro v vv
    rcases mem_union.mp vv with vv|vv
    · rcases mem_union.mp vv with vv|vv
      · exact (dat 3 vv).2.2
      · exact (dat 4 vv).2.2.2.1
    · exact (dat 6 vv).2.2.2.1)).trans ta.2.1
  have bVis := (vc 1 5 6 (by decide) (by decide) (by decide) (r:=b) (by
    intro v vv
    rcases mem_union.mp vv with vv|vv
    · rcases mem_union.mp vv with vv|vv
      · exact (dat 1 vv).2.2
      · exact (dat 5 vv).2.2.2.2
    · exact (dat 6 vv).2.2.2.2)).trans tb.2.1

  have ep (i : Fin 8) : (E i).card≤(N i).card := by have h := hE i; omega
  have lo : ∃ l : ℕ,l≤8 ∧ (∀ i : Fin 8,(E i).card=(if l=i.val+1 then 1 else 0)) ∧
      ∀ z∈Shore D,G.degree z<6 → l=(sixClass G a b z).val+1 := by
    by_cases h : low.Nonempty
    · obtain ⟨v,vl⟩ := h
      have lv : low={v} := by
        symm
        apply eq_of_subset_of_card_le (singleton_subset_iff.mpr vl)
        simp
        omega
      let k := sixClass G a b v
      have kn := k.isLt
      refine ⟨k.val+1,by omega,?_,?_⟩
      · intro i
        change (low.filter (fun u=>sixClass G a b u=i)).card=_
        rw [lv]
        by_cases hi : k=i
        · have hval : k.val+1=i.val+1 := congrArg (fun t : Fin 8=>t.val+1) hi
          have hic : sixClass G a b v=i := hi
          rw [filter_singleton,if_pos hic,if_pos hval,card_singleton]
        · have hval : k.val+1≠i.val+1 := fun h=>hi (Fin.ext (Nat.add_right_cancel h))
          have hien : sixClass G a b v≠i := hi
          rw [filter_singleton,if_neg hien,if_neg hval,card_empty]
      · intro z zd zl
        have zm : z∈low := mem_filter.mpr ⟨zd,zl⟩
        rw [lv] at zm
        rw [mem_singleton.mp zm]
    · refine ⟨0,by decide,?_,?_⟩
      · intro i
        have l0 := not_nonempty_iff_eq_empty.mp h
        change (low.filter _).card=_
        rw [l0]
        simp
      · intro z zd zl
        exact (h ⟨z,mem_filter.mpr ⟨zd,zl⟩⟩).elim
  obtain ⟨l,l7,lc,lo⟩ := lo
  have ashape : qa.card+(N 5).card≤5 := by
    apply small_port_even_budget hc far ab conn even degree cd six
    intro v vn
    obtain ⟨vd,va,vb,na,db⟩ := dat 5 vn
    exact ⟨vd,db,unseen_nonport_ge_three hc (fun e=>(shore_off D).1 (e ▸ vd)) va na⟩
  have bshape : qb.card+(N 4).card≤5 := by
    simpa only [shore_swapCut] using (show (cutPorts G (Shore (swapCut D)) b).card+(N 4).card≤5 by
      apply small_port_even_budget hc far' ab.symm conn even degree cd' six'
      intro v vn
      obtain ⟨vd,va,vb,da,nb⟩ := dat 4 vn
      exact ⟨by rwa [shore_swapCut],da,unseen_nonport_ge_three hc (fun e=>(shore_off D).2 (e ▸ vd)) vb nb⟩)
  rw [caEq] at ashape
  rw [cbEq] at bshape
  have hiA := ta.2.2.2
  have hiB := tb.2.2.2
  rw [caEq] at hiA
  rw [cbEq] at hiB
  have shB := cut_port_range hc far' ab.symm conn even cd'.symm
  rw [shore_swapCut] at shB
  have smMin : 5≤pa.card+pb.card := by omega
  have mLocal (u : V) (ud : u∈Shore D) : 1≤(inside G (Shore D) u).card :=
    shore_inside_one_of_two_connected far conn ud
  have mDark (u : V) (ud : u∈Shore D) (ua : ¬G.Adj a u) (ub : ¬G.Adj b u) :
      2≤(inside G (Shore D) u).card := by
    have da : u≠a := fun e=>(shore_off D).1 (e ▸ ud)
    have h := degree_two_from_one_deletion conn da (fun e=>ua e.symm)
    have sub := card_le_card (neighbor_subset_of_dark D ud ua ub)
    rw [G.card_neighborFinset_eq_degree] at sub
    exact h.trans sub
  have d0 (u0 : (E 0).card<(N 0).card) : 6≤(N 0).card+(N 1).card+(N 4).card+(N 6).card := by
    obtain ⟨u,ud,uh,ur⟩ := chooseHigh 0 u0
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := shore_inside_five far D ud uh
    have r : 6≤∑ j ∈ allowedRoles 0, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have m0 (u0 : 0<(N 0).card) : 2≤(N 0).card+(N 1).card+(N 4).card+(N 6).card := by
    obtain ⟨u,um⟩ := card_pos.mp u0
    obtain ⟨ud,ur⟩ := dat 0 um
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := mLocal u ud
    have r : 2≤∑ j ∈ allowedRoles 0, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have d1 (u0 : (E 1).card<(N 1).card) : 6≤(N 0).card+(N 1).card+(N 3).card+(N 4).card+(N 6).card := by
    obtain ⟨u,ud,uh,ur⟩ := chooseHigh 1 u0
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := shore_inside_five far D ud uh
    have r : 6≤∑ j ∈ allowedRoles 1, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have m1 (u0 : 0<(N 1).card) : 2≤(N 0).card+(N 1).card+(N 3).card+(N 4).card+(N 6).card := by
    obtain ⟨u,um⟩ := card_pos.mp u0
    obtain ⟨ud,ur⟩ := dat 1 um
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := mLocal u ud
    have r : 2≤∑ j ∈ allowedRoles 1, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have d2 (u0 : (E 2).card<(N 2).card) : 6≤(N 2).card+(N 3).card+(N 5).card+(N 6).card := by
    obtain ⟨u,ud,uh,ur⟩ := chooseHigh 2 u0
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := shore_inside_five far D ud uh
    have r : 6≤∑ j ∈ allowedRoles 2, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have m2 (u0 : 0<(N 2).card) : 2≤(N 2).card+(N 3).card+(N 5).card+(N 6).card := by
    obtain ⟨u,um⟩ := card_pos.mp u0
    obtain ⟨ud,ur⟩ := dat 2 um
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := mLocal u ud
    have r : 2≤∑ j ∈ allowedRoles 2, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have d3 (u0 : (E 3).card<(N 3).card) : 6≤(N 1).card+(N 2).card+(N 3).card+(N 5).card+(N 6).card := by
    obtain ⟨u,ud,uh,ur⟩ := chooseHigh 3 u0
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := shore_inside_five far D ud uh
    have r : 6≤∑ j ∈ allowedRoles 3, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have m3 (u0 : 0<(N 3).card) : 2≤(N 1).card+(N 2).card+(N 3).card+(N 5).card+(N 6).card := by
    obtain ⟨u,um⟩ := card_pos.mp u0
    obtain ⟨ud,ur⟩ := dat 3 um
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := mLocal u ud
    have r : 2≤∑ j ∈ allowedRoles 3, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have d4 (u0 : (E 4).card<(N 4).card) : 7≤(N 0).card+(N 1).card+(N 4).card+(N 5).card+(N 6).card+(N 7).card := by
    obtain ⟨u,ud,uh,ur⟩ := chooseHigh 4 u0
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := dark_inside_six ud ur.1 ur.2.1 uh
    have r : 7≤∑ j ∈ allowedRoles 4, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have m4 (u0 : 0<(N 4).card) : 3≤(N 0).card+(N 1).card+(N 4).card+(N 5).card+(N 6).card+(N 7).card := by
    obtain ⟨u,um⟩ := card_pos.mp u0
    obtain ⟨ud,ur⟩ := dat 4 um
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := mDark u ud ur.1 ur.2.1
    have r : 3≤∑ j ∈ allowedRoles 4, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have d5 (u0 : (E 5).card<(N 5).card) : 7≤(N 2).card+(N 3).card+(N 4).card+(N 5).card+(N 6).card+(N 7).card := by
    obtain ⟨u,ud,uh,ur⟩ := chooseHigh 5 u0
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := dark_inside_six ud ur.1 ur.2.1 uh
    have r : 7≤∑ j ∈ allowedRoles 5, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have m5 (u0 : 0<(N 5).card) : 3≤(N 2).card+(N 3).card+(N 4).card+(N 5).card+(N 6).card+(N 7).card := by
    obtain ⟨u,um⟩ := card_pos.mp u0
    obtain ⟨ud,ur⟩ := dat 5 um
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := mDark u ud ur.1 ur.2.1
    have r : 3≤∑ j ∈ allowedRoles 5, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have d6 (u0 : (E 6).card<(N 6).card) : 7≤(N 0).card+(N 1).card+(N 2).card+(N 3).card+(N 4).card+(N 5).card+(N 6).card+(N 7).card := by
    obtain ⟨u,ud,uh,ur⟩ := chooseHigh 6 u0
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := dark_inside_six ud ur.1 ur.2.1 uh
    have r : 7≤∑ j ∈ allowedRoles 6, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have m6 (u0 : 0<(N 6).card) : 3≤(N 0).card+(N 1).card+(N 2).card+(N 3).card+(N 4).card+(N 5).card+(N 6).card+(N 7).card := by
    obtain ⟨u,um⟩ := card_pos.mp u0
    obtain ⟨ud,ur⟩ := dat 6 um
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := mDark u ud ur.1 ur.2.1
    have r : 3≤∑ j ∈ allowedRoles 6, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert ,Nat.add_assoc] using r
  have d7 (u0 : (E 7).card<(N 7).card) : 7≤(N 4).card+(N 5).card+(N 6).card+(N 7).card := by
    obtain ⟨u,ud,uh,ur⟩ := chooseHigh 7 u0
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := dark_inside_six ud ur.1 ur.2.1 uh
    have r : 7≤∑ j ∈ allowedRoles 7, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc] using r
  have m7 (u0 : 0<(N 7).card) : 3≤(N 4).card+(N 5).card+(N 6).card+(N 7).card := by
    obtain ⟨u,um⟩ := card_pos.mp u0
    obtain ⟨ud,ur⟩ := dat 7 um
    have b := role_card_bound hc far ud ur
    rw [allowedInShore_card] at b
    have l := mDark u ud ur.1 ur.2.1
    have r : 3≤∑ j ∈ allowedRoles 7, (N j).card := (Nat.add_le_add_right l 1).trans b
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc] using r
  have cls := classify_shape pa.card pb.card
    (N 0).card (N 1).card (N 2).card (N 3).card (N 4).card (N 5).card (N 6).card (N 7).card (E 0).card (E 1).card (E 2).card (E 3).card (E 4).card (E 5).card (E 6).card (E 7).card l
    (ta.1)
    (tb.1)
    (norm)
    (shB.2)
    (smMin)
    (small)
    (by omega)
    (by omega)
    (ashape)
    (bshape)
    (by simpa [Nat.add_assoc] using hiA)
    (by simpa [Nat.add_assoc] using hiB)
    (aVis)
    (bVis)
    (l7)
    (ep 0)
    (fun hy=>by rw [lc 0]; exact if_pos hy)
    (fun hn=>by rw [lc 0]; exact if_neg hn)
    (d0)
    (m0)
    (ep 1)
    (fun hy=>by rw [lc 1]; exact if_pos hy)
    (fun hn=>by rw [lc 1]; exact if_neg hn)
    (d1)
    (m1)
    (ep 2)
    (fun hy=>by rw [lc 2]; exact if_pos hy)
    (fun hn=>by rw [lc 2]; exact if_neg hn)
    (d2)
    (m2)
    (ep 3)
    (fun hy=>by rw [lc 3]; exact if_pos hy)
    (fun hn=>by rw [lc 3]; exact if_neg hn)
    (d3)
    (m3)
    (ep 4)
    (fun hy=>by rw [lc 4]; exact if_pos hy)
    (fun hn=>by rw [lc 4]; exact if_neg hn)
    (d4)
    (m4)
    (ep 5)
    (fun hy=>by rw [lc 5]; exact if_pos hy)
    (fun hn=>by rw [lc 5]; exact if_neg hn)
    (d5)
    (m5)
    (ep 6)
    (fun hy=>by rw [lc 6]; exact if_pos hy)
    (fun hn=>by rw [lc 6]; exact if_neg hn)
    (d6)
    (m6)
    (ep 7)
    (fun hy=>by rw [lc 7]; exact if_pos hy)
    (fun hn=>by rw [lc 7]; exact if_neg hn)
    (d7)
    (m7)
  obtain ⟨i,eq⟩ := cls
  exact ⟨i,l,eq,lo⟩

#print axioms classified_six_thirteen_shape
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
