import SixSevenCosts189
namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair
open scoped BigOperators
open private Shore shore_disjoint shore_off shore_closed shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far shore_inside_five from SixDistanceThreeShort189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open private neighbor_subset_of_dark from SixTenRegular189
open private degree_two_from_one_deletion from AdjacentCutFiveTwinThreeGeom189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open FiveAdjacent (shore_swapCut)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000000
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {C D : Cmp G a b}

theorem no_seven_eleven_shores (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ v,(EvenFrom G v).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (seven : (Shore C).card=7) (eleven : (Shore D).card=11) : False := by
  classical
  let X := sixBucket G a b (Shore C)
  let Y := sixBucket G a b (Shore D)
  let A := sixBucket G a b (highShore G (Shore C))
  let B := sixBucket G a b (highShore G (Shore D))
  have kn (z : V) : ¬(G.Adj a z∧G.Adj b z) := no_common_far far
  have xData (K : Cmp G a b) (i : Fin 8) {z : V} (zm : z∈sixBucket G a b (Shore K) i) :
      z∈Shore K ∧ sixClassSpec G a b z i := (mem_sixBucket (kn z) i).mp zm
  have hData (K : Cmp G a b) (i : Fin 8) {z : V} (zm : z∈sixBucket G a b (highShore G (Shore K)) i) :
      z∈Shore K ∧ 6≤G.degree z ∧ sixClassSpec G a b z i := by
    obtain ⟨m,r⟩ := (mem_sixBucket (kn z) i).mp zm
    exact ⟨(mem_filter.mp m).1,(mem_filter.mp m).2,r⟩
  have cHigh (K : Cmp G a b) (i : Fin 8) :
      (sixBucket G a b (highShore G (Shore K)) i).card≤(sixBucket G a b (Shore K) i).card := by
    exact card_le_card (fun z zz=>mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp zz).1).1,(mem_filter.mp zz).2⟩)
  have xSum := ((sixBuckets_card (G:=G) a b) (Shore C)).trans seven
  have ySum := ((sixBuckets_card (G:=G) a b) (Shore D)).trans eleven
  have axSum := (sixBuckets_card (G:=G) a b) (highShore G (Shore C))
  have bySum := (sixBuckets_card (G:=G) a b) (highShore G (Shore D))
  let low (K : Cmp G a b) := (Shore K).filter (fun v=>G.degree v<6)
  have lowCap : ((low C)∪(low D)).card≤1 := by
    apply card_le_one.mpr
    intro u um v vm
    have ul : G.degree u<6 := (mem_union.mp um).elim (fun h=>(mem_filter.mp h).2) (fun h=>(mem_filter.mp h).2)
    have vl : G.degree v<6 := (mem_union.mp vm).elim (fun h=>(mem_filter.mp h).2) (fun h=>(mem_filter.mp h).2)
    by_contra uv
    exact (degree u v uv).elim (Nat.not_le_of_lt ul) (Nat.not_le_of_lt vl)
  have lowDis : Disjoint (low C) (low D) := (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)
  rw [card_union_of_disjoint lowDis] at lowCap
  have highSplit (K : Cmp G a b) : (highShore G (Shore K)).card+(low K).card=(Shore K).card := by
    have d : Disjoint (highShore G (Shore K)) (low K) :=
      disjoint_left.mpr (fun v vh vl=>(Nat.not_le_of_lt (mem_filter.mp vl).2) (mem_filter.mp vh).2)
    have e : highShore G (Shore K)∪low K=Shore K := by
      ext v
      by_cases k : 6≤G.degree v
      · have nk := Nat.not_lt_of_ge k
        simp [highShore,low,k,nk]
      · have nk := Nat.lt_of_not_ge k
        simp [highShore,low,k,nk]
    rw [←card_union_of_disjoint d,e]
  have oneLow : 17≤(highShore G (Shore C)).card+(highShore G (Shore D)).card := by
    have q := highSplit C
    have r := highSplit D
    omega
  have far' : 3≤G.dist b a := by rwa [dist_comm]
  have cd' : swapCut C≠swapCut D := fun e=>cd (swapCut.injective e)
  have cover' : ∀ {z : V},z≠b → z≠a → z∈Shore (swapCut C) ∨ z∈Shore (swapCut D) := by
    intro z zb za
    simpa only [shore_swapCut] using cover za zb
  have hiA := cut_terminal_high_distance_three hc far ab conn even degree cd cover
  have hiB := cut_terminal_high_distance_three hc far' ab.symm conn even degree cd' cover'
  have pA := cut_ports_sum far cd cover
  have pB := cut_ports_sum far' cd' cover'
  simp only [shore_swapCut] at pB
  have cA := cut_port_range hc far ab conn even cd.symm
  have dA := cut_port_range hc far ab conn even cd
  have cB := cut_port_range hc far' ab.symm conn even cd'.symm
  have dB := cut_port_range hc far' ab.symm conn even cd'
  simp only [shore_swapCut] at cB dB
  have ov (K : Cmp G a b) := role_ports_seen far (Shore K)
  have portA (K : Cmp G a b) : (cutPorts G (Shore K) a).card =
      (sixBucket G a b (Shore K) 0).card+(sixBucket G a b (Shore K) 1).card := by
    rw [(ov K).1,card_union_of_disjoint (sixBuckets_disjoint a b _ _ (by decide : (0:Fin 8)≠1))]
  have portB (K : Cmp G a b) : (cutPorts G (Shore K) b).card =
      (sixBucket G a b (Shore K) 2).card+(sixBucket G a b (Shore K) 3).card := by
    rw [(ov K).2.1,card_union_of_disjoint (sixBuckets_disjoint a b _ _ (by decide : (2:Fin 8)≠3))]
  have seenCap (r : V) : (cutSeen G (Shore C) r).card+(cutSeen G (Shore D) r).card≤6 := by
    have d : Disjoint (cutSeen G (Shore C) r) (cutSeen G (Shore D) r) :=
      (shore_disjoint cd).mono inter_subset_left inter_subset_left
    have cap := (card_le_card (union_subset (show cutSeen G (Shore C) r ⊆ DistanceTwo G r from inter_subset_right)
      (show cutSeen G (Shore D) r ⊆ DistanceTwo G r from inter_subset_right))).trans
      (distanceTwo_le_of_even 6 r (even r))
    rwa [card_union_of_disjoint d] at cap
  have seenA (K : Cmp G a b) : (cutSeen G (Shore K) a).card =
      (sixBucket G a b (Shore K) 3).card+(sixBucket G a b (Shore K) 4).card+(sixBucket G a b (Shore K) 6).card := by
    rw [(ov K).2.2.1,card_union_of_disjoint (disjoint_union_right.mpr
      ⟨sixBuckets_disjoint a b _ _ (by decide : (3:Fin 8)≠4),sixBuckets_disjoint a b _ _ (by decide : (3:Fin 8)≠6)⟩),
      card_union_of_disjoint (sixBuckets_disjoint a b _ _ (by decide : (4:Fin 8)≠6)),Nat.add_assoc]
  have seenB (K : Cmp G a b) : (cutSeen G (Shore K) b).card =
      (sixBucket G a b (Shore K) 1).card+(sixBucket G a b (Shore K) 5).card+(sixBucket G a b (Shore K) 6).card := by
    rw [(ov K).2.2.2,card_union_of_disjoint (disjoint_union_right.mpr
      ⟨sixBuckets_disjoint a b _ _ (by decide : (1:Fin 8)≠5),sixBuckets_disjoint a b _ _ (by decide : (1:Fin 8)≠6)⟩),
      card_union_of_disjoint (sixBuckets_disjoint a b _ _ (by decide : (5:Fin 8)≠6)),Nat.add_assoc]
  have tac := seenCap a
  have tbc := seenCap b
  rw [seenA,seenA] at tac
  rw [seenB,seenB] at tbc
  have noDual (K : Cmp G a b) : Disjoint (cutPorts G (Shore K) a) (cutPorts G (Shore K) b) :=
    disjoint_left.mpr (fun v ha hb=>kn v ⟨(mem_filter.mp ha).2,(mem_filter.mp hb).2⟩)
  have littlePorts : (cutPorts G (Shore C) a).card+(cutPorts G (Shore C) b).card≤7 := by
    have sub : cutPorts G (Shore C) a∪cutPorts G (Shore C) b⊆Shore C := union_subset (filter_subset _ _) (filter_subset _ _)
    have le := card_le_card sub
    rwa [card_union_of_disjoint (noDual C),seven] at le
  have bigDarkCap : ((Shore D) \ (cutPorts G (Shore D) a∪cutPorts G (Shore D) b)).card≤6 := by
    have sub : cutPorts G (Shore D) a∪cutPorts G (Shore D) b⊆Shore D := union_subset (filter_subset _ _) (filter_subset _ _)
    rw [card_sdiff sub,card_union_of_disjoint (noDual D),eleven]
    omega
  have deep : (B 7).card=0 := by
    by_contra nc
    obtain ⟨v,vm⟩ := card_pos.mp (Nat.pos_of_ne_zero nc)
    obtain ⟨vd,vh,va,vb,na,nb⟩ := hData D 7 vm
    exact (Nat.not_le_of_lt (hidden_dark_not_high_of_dark_card hc bigDarkCap vd va vb na nb)) vh
  have darkVisible {v : V} (vc : v∈Shore C) (vh : 6≤G.degree v) (va : ¬G.Adj a v) (vb : ¬G.Adj b v) :
      G.dist a v=2 ∧ G.dist b v=2 := by
    obtain ⟨u,uc,au⟩ := shore_hit_a ab conn C
    obtain ⟨w,wc,bw⟩ := shore_hit_b ab conn C
    have uv : u≠v := fun e=>va (e ▸ au)
    have wv : w≠v := fun e=>vb (e ▸ bw)
    have vA : v≠a := fun e=>(shore_off C).1 (e ▸ vc)
    have vB : v≠b := fun e=>(shore_off C).2 (e ▸ vc)
    exact ⟨(mem_cutSeen.mp (visible_of_adj_port hc vA vc au
      (dark_high_universal_in_seven seven vc va vb vh u uc uv).symm va)).2,
      (mem_cutSeen.mp (visible_of_adj_port hc vB vc bw
      (dark_high_universal_in_seven seven vc va vb vh w wc wv).symm vb)).2⟩
  have dark4 : (A 4).card=0 := by
    by_contra nc
    obtain ⟨v,vm⟩ := card_pos.mp (Nat.pos_of_ne_zero nc)
    obtain ⟨vc,vh,va,vb,na,nb⟩ := hData C 4 vm
    exact nb (darkVisible vc vh va vb).2
  have dark5 : (A 5).card=0 := by
    by_contra nc
    obtain ⟨v,vm⟩ := card_pos.mp (Nat.pos_of_ne_zero nc)
    obtain ⟨vc,vh,va,vb,na,nb⟩ := hData C 5 vm
    exact na (darkVisible vc vh va vb).1
  have dark7 : (A 7).card=0 := by
    by_contra nc
    obtain ⟨v,vm⟩ := card_pos.mp (Nat.pos_of_ne_zero nc)
    obtain ⟨vc,vh,va,vb,na,nb⟩ := hData C 7 vm
    exact na (darkVisible vc vh va vb).1

  have smallDark : (A 4).card+(A 5).card+(A 7).card=0 := by omega
  rw [portA,portA] at pA
  rw [portB,portB] at pB
  rw [portA] at cA dA
  rw [portB] at cB dB
  have shigh0 (pos : 0<(A 0).card) : 6≤(X 0).card+(X 1).card+(X 4).card+(X 6).card := by
    obtain ⟨v,vm⟩ := card_pos.mp pos
    obtain ⟨vc,vh,vr⟩ := hData C 0 vm
    have k := role_card_bound hc far vc vr
    rw [allowedInShore_card] at k
    have d := shore_inside_five far C vc vh
    have e : 6≤∑ j ∈ allowedRoles 0, (sixBucket G a b (Shore C) j).card :=
      (Nat.add_le_add_right d 1).trans k
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc,X] using e
  have shigh1 (pos : 0<(A 1).card) : 6≤(X 0).card+(X 1).card+(X 3).card+(X 4).card+(X 6).card := by
    obtain ⟨v,vm⟩ := card_pos.mp pos
    obtain ⟨vc,vh,vr⟩ := hData C 1 vm
    have k := role_card_bound hc far vc vr
    rw [allowedInShore_card] at k
    have d := shore_inside_five far C vc vh
    have e : 6≤∑ j ∈ allowedRoles 1, (sixBucket G a b (Shore C) j).card :=
      (Nat.add_le_add_right d 1).trans k
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc,X] using e
  have shigh2 (pos : 0<(A 2).card) : 6≤(X 2).card+(X 3).card+(X 5).card+(X 6).card := by
    obtain ⟨v,vm⟩ := card_pos.mp pos
    obtain ⟨vc,vh,vr⟩ := hData C 2 vm
    have k := role_card_bound hc far vc vr
    rw [allowedInShore_card] at k
    have d := shore_inside_five far C vc vh
    have e : 6≤∑ j ∈ allowedRoles 2, (sixBucket G a b (Shore C) j).card :=
      (Nat.add_le_add_right d 1).trans k
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc,X] using e
  have shigh3 (pos : 0<(A 3).card) : 6≤(X 1).card+(X 2).card+(X 3).card+(X 5).card+(X 6).card := by
    obtain ⟨v,vm⟩ := card_pos.mp pos
    obtain ⟨vc,vh,vr⟩ := hData C 3 vm
    have k := role_card_bound hc far vc vr
    rw [allowedInShore_card] at k
    have d := shore_inside_five far C vc vh
    have e : 6≤∑ j ∈ allowedRoles 3, (sixBucket G a b (Shore C) j).card :=
      (Nat.add_le_add_right d 1).trans k
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc,X] using e
  have thigh0 (pos : 0<(B 0).card) : 6≤(Y 0).card+(Y 1).card+(Y 4).card+(Y 6).card := by
    obtain ⟨v,vm⟩ := card_pos.mp pos
    obtain ⟨vc,vh,vr⟩ := hData D 0 vm
    have k := role_card_bound hc far vc vr
    rw [allowedInShore_card] at k
    have d := shore_inside_five far D vc vh
    have e : 6≤∑ j ∈ allowedRoles 0, (sixBucket G a b (Shore D) j).card :=
      (Nat.add_le_add_right d 1).trans k
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc,Y] using e
  have thigh2 (pos : 0<(B 2).card) : 6≤(Y 2).card+(Y 3).card+(Y 5).card+(Y 6).card := by
    obtain ⟨v,vm⟩ := card_pos.mp pos
    obtain ⟨vc,vh,vr⟩ := hData D 2 vm
    have k := role_card_bound hc far vc vr
    rw [allowedInShore_card] at k
    have d := shore_inside_five far D vc vh
    have e : 6≤∑ j ∈ allowedRoles 2, (sixBucket G a b (Shore D) j).card :=
      (Nat.add_le_add_right d 1).trans k
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc,Y] using e
  have thigh4 (pos : 0<(B 4).card) : 7≤(Y 0).card+(Y 1).card+(Y 4).card+(Y 5).card+(Y 6).card+(Y 7).card := by
    obtain ⟨v,vm⟩ := card_pos.mp pos
    obtain ⟨vc,vh,vr⟩ := hData D 4 vm
    have k := role_card_bound hc far vc vr
    rw [allowedInShore_card] at k
    have d := dark_inside_six vc vr.1 vr.2.1 vh
    have e : 7≤∑ j ∈ allowedRoles 4, (sixBucket G a b (Shore D) j).card :=
      (Nat.add_le_add_right d 1).trans k
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc,Y] using e
  have thigh5 (pos : 0<(B 5).card) : 7≤(Y 2).card+(Y 3).card+(Y 4).card+(Y 5).card+(Y 6).card+(Y 7).card := by
    obtain ⟨v,vm⟩ := card_pos.mp pos
    obtain ⟨vc,vh,vr⟩ := hData D 5 vm
    have k := role_card_bound hc far vc vr
    rw [allowedInShore_card] at k
    have d := dark_inside_six vc vr.1 vr.2.1 vh
    have e : 7≤∑ j ∈ allowedRoles 5, (sixBucket G a b (Shore D) j).card :=
      (Nat.add_le_add_right d 1).trans k
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc,Y] using e

  have slow7 (pos : 0<(X 7).card) : 3≤(X 4).card+(X 5).card+(X 6).card+(X 7).card := by
    obtain ⟨v,vm⟩ := card_pos.mp pos
    obtain ⟨vc,vr⟩ := xData C 7 vm
    have va : v≠a := fun h=>(shore_off C).1 (h ▸ vc)
    have d := degree_two_from_one_deletion conn va (fun h=>vr.1 h.symm)
    have e := card_le_card (neighbor_subset_of_dark C vc vr.1 vr.2.1)
    rw [G.card_neighborFinset_eq_degree] at e
    have k := role_card_bound hc far vc vr
    rw [allowedInShore_card] at k
    have q : 3≤∑ j ∈ allowedRoles 7, (sixBucket G a b (Shore C) j).card :=
      (Nat.add_le_add_right (d.trans e) 1).trans k
    simpa [allowedRoles,Finset.sum_insert,Nat.add_assoc,X] using q
  have cost0 (p : 0<(B 0).card) : (X 0).card+(X 1).card+(X 2).card+(X 5).card+(X 7).card+(B 2).card+(B 3).card+(B 5).card+(B 7).card≤6 := by
    obtain ⟨v,vm⟩ := card_pos.mp p
    obtain ⟨vd,vh,vr⟩ := hData D 0 vm
    have q := seven_eleven_port_cost_0 hc far ab conn even degree cd seven eleven vd vh vr
    rw [portA] at q
    dsimp only [X,B]
    omega
  have cost1 (p : 0<(B 1).card) : (X 0).card+(X 1).card+1+(X 5).card+(X 7).card+(B 2).card+(B 5).card+(B 7).card≤6 := by
    obtain ⟨v,vm⟩ := card_pos.mp p
    obtain ⟨vd,vh,vr⟩ := hData D 1 vm
    have q := seven_eleven_port_cost_1 hc far ab conn even degree cd seven eleven vd vh vr
    rw [portA] at q
    dsimp only [X,B]
    omega
  have cost2 (p : 0<(B 2).card) : (X 2).card+(X 3).card+(X 0).card+(X 4).card+(X 7).card+(B 0).card+(B 1).card+(B 4).card+(B 7).card≤6 := by
    obtain ⟨v,vm⟩ := card_pos.mp p
    obtain ⟨vd,vh,vr⟩ := hData D 2 vm
    have q := seven_eleven_port_cost_2 hc far ab conn even degree cd seven eleven vd vh vr
    rw [portB] at q
    dsimp only [X,B]
    omega
  have cost3 (p : 0<(B 3).card) : (X 2).card+(X 3).card+1+(X 4).card+(X 7).card+(B 0).card+(B 4).card+(B 7).card≤6 := by
    obtain ⟨v,vm⟩ := card_pos.mp p
    obtain ⟨vd,vh,vr⟩ := hData D 3 vm
    have q := seven_eleven_port_cost_3 hc far ab conn even degree cd seven eleven vd vh vr
    rw [portB] at q
    dsimp only [X,B]
    omega

  have cost6 (p : 0<(B 6).card) : 2+(A 6).card≤6 := by
    obtain ⟨v,vm⟩ := card_pos.mp p
    obtain ⟨vd,vh,va,vb,da,db⟩ := hData D 6 vm
    have loc : (A 6)⊆Shore C := fun x m=>(hData C 6 m).1
    have ac : Disjoint (A 6) {a} := disjoint_left.mpr (fun x xm xs=>(shore_off C).1 ((mem_singleton.mp xs) ▸ loc xm))
    have bc : Disjoint (A 6) {b} := disjoint_left.mpr (fun x xm xs=>(shore_off C).2 ((mem_singleton.mp xs) ▸ loc xm))
    have abc : Disjoint ({a}:Finset V) {b} := disjoint_left.mpr (fun x xa xb=>ab ((mem_singleton.mp xa).symm.trans (mem_singleton.mp xb)))
    have r := even_budget_three even v (A 6) {a} {b} ac bc abc
      (by intro x xx; obtain ⟨xc,xh,xa,xb,xa2,xb2⟩ := hData C 6 xx
          exact mem_positive_four (both_seen_dark_cross_four hc cd vd xc da db xa2 xb2))
      (by intro x xx; rw [mem_singleton.mp xx]; exact in_positive_even_of_dist_two (by rwa [dist_comm]))
      (by intro x xx; rw [mem_singleton.mp xx]; exact in_positive_even_of_dist_two (by rwa [dist_comm]))
    simp only [card_singleton] at r
    omega
  apply impossible_seven_eleven_counts
    (X 0).card (X 1).card (X 2).card (X 3).card (X 4).card (X 5).card (X 6).card (X 7).card (Y 0).card (Y 1).card (Y 2).card (Y 3).card (Y 4).card (Y 5).card (Y 6).card (Y 7).card (A 0).card (A 1).card (A 2).card (A 3).card (A 4).card (A 5).card (A 6).card (A 7).card (B 0).card (B 1).card (B 2).card (B 3).card (B 4).card (B 5).card (B 6).card (B 7).card
    (xSum)
    (ySum)
    (cHigh C 0)
    (cHigh C 1)
    (cHigh C 2)
    (cHigh C 3)
    (cHigh C 4)
    (cHigh C 5)
    (cHigh C 6)
    (cHigh C 7)
    (cA)
    (cB)
    (shigh0)
    (shigh1)
    (shigh2)
    (shigh3)
    (slow7)
    (cHigh D 0)
    (cHigh D 1)
    (cHigh D 2)
    (cHigh D 3)
    (cHigh D 4)
    (cHigh D 5)
    (cHigh D 6)
    (cHigh D 7)
    (dA)
    (dB)
    (thigh0)
    (thigh2)
    (thigh4)
    (thigh5)
    (by simpa only [←axSum,←bySum,Nat.add_assoc,A,B] using oneLow)
    (smallDark)
    (deep)
    (by dsimp only [X,Y]; omega)
    (by dsimp only [X,Y]; omega)
    (by dsimp only [X,Y]; omega)
    (by dsimp only [X,Y]; omega)
    (cost0)
    (cost1)
    (cost2)
    (cost3)
    (cost6)

#print axioms no_seven_eleven_shores
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
