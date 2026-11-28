import SixTwelveSat189
namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair
open private Shore shore_disjoint shore_off shore_closed shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far from SixDistanceThreeShort189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (cross_metric shore_swapCut)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {C D : Cmp G a b}

theorem dark_to_k6_distance_four (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (six : (Shore C).card=6)
    {u v : V} (ud : u∈Shore D) (vc : v∈Shore C)
    (va : ¬G.Adj a v) (vb : ¬G.Adj b v)
    (ua : 2≤G.dist a u) (ub : 2≤G.dist b u)
    (vis : G.dist a u=2 ∨ G.dist b u=2) : G.dist u v=4 := by
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
  obtain ⟨y,yc,by'⟩ := shore_hit_b ab conn C
  have vx : x≠v := fun e=>va (e ▸ ax)
  have vy : y≠v := fun e=>vb (e ▸ by')
  have vA : v≠a := fun e=>(shore_off C).1 (e ▸ vc)
  have vB : v≠b := fun e=>(shore_off C).2 (e ▸ vc)
  have h := cut_shore_six_clique far C six degree
  have da := (mem_cutSeen.mp (visible_of_adj_port hc vA vc ax (h x xc v vc vx) va)).2
  have db := (mem_cutSeen.mp (visible_of_adj_port hc vB vc by' (h y yc v vc vy) vb)).2
  have out : v∉Shore D := fun vd=>disjoint_left.mp (shore_disjoint cd) vc vd
  rw [cross_metric (Shore D) hc ud out (shore_closed D),dist_comm (u:=u) (v:=a),
    dist_comm (u:=u) (v:=b),da,db]
  omega

/-- The local D2 cap after accounting for positive even distances
outside a twelve-shore, next to a six-shore. -/
theorem k6_profile_budget (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (six : (Shore C).card=6) {u : V} (ud : u∈Shore D)
    {i : Fin 8} (hi : i.val<7) (ur : sixClassSpec G a b u i)
    (H : Finset V) (hd : H⊆Shore D) (h2 : H⊆DistanceTwo G u) :
    H.card + (match i.val with
      | 0=>(cutPorts G (Shore C) a).card
      | 1=>(cutPorts G (Shore C) a).card+1
      | 2=>(cutPorts G (Shore C) b).card
      | 3=>(cutPorts G (Shore C) b).card+1
      | 4=>(cutPorts G (Shore C) b).card+1+(6-((cutPorts G (Shore C) a).card+(cutPorts G (Shore C) b).card))
      | 5=>(cutPorts G (Shore C) a).card+1+(6-((cutPorts G (Shore C) a).card+(cutPorts G (Shore C) b).card))
      | _=>2+(6-((cutPorts G (Shore C) a).card+(cutPorts G (Shore C) b).card)))≤6 := by
  classical
  let Pa := cutPorts G (Shore C) a
  let Pb := cutPorts G (Shore C) b
  let K := (Shore C) \ (Pa∪Pb)
  have asub : Pa⊆Shore C := filter_subset _ _
  have bsub : Pb⊆Shore C := filter_subset _ _
  have ks : K⊆Shore C := sdiff_subset
  have pd : Disjoint Pa Pb := disjoint_left.mpr
    (fun x xa xb=>no_common_far far ⟨(mem_filter.mp xa).2,(mem_filter.mp xb).2⟩)
  have kc : K.card=6-(Pa.card+Pb.card) := by
    change ((Shore C) \ (Pa∪Pb)).card=_
    rw [card_sdiff (union_subset asub bsub),card_union_of_disjoint pd,six]
  have kData {x : V} (xk : x∈K) : x∈Shore C ∧ ¬G.Adj a x ∧ ¬G.Adj b x := by
    obtain ⟨xc,xn⟩ := mem_sdiff.mp xk
    exact ⟨xc,fun h=>xn (mem_union_left _ (mem_filter.mpr ⟨xc,h⟩)),
      fun h=>xn (mem_union_right _ (mem_filter.mpr ⟨xc,h⟩))⟩
  have da : Disjoint Pa K := disjoint_left.mpr (fun x xa xk=>(mem_sdiff.mp xk).2 (mem_union_left _ xa))
  have db : Disjoint Pb K := disjoint_left.mpr (fun x xb xk=>(mem_sdiff.mp xk).2 (mem_union_right _ xb))
  have neqA : u≠a := fun e=>(shore_off D).1 (e ▸ ud)
  have neqB : u≠b := fun e=>(shore_off D).2 (e ▸ ud)
  have tc (T : Finset V) (outside : ∀ x∈T,x=a∨x=b) : Disjoint T (Shore C) :=
    disjoint_left.mpr (fun x xt xs=>(outside x xt).elim (fun e=>(shore_off C).1 (e ▸ xs))
      (fun e=>(shore_off C).2 (e ▸ xs)))
  have td (T : Finset V) (outside : ∀ x∈T,x=a∨x=b) : Disjoint T (Shore D) :=
    disjoint_left.mpr (fun x xt xs=>(outside x xt).elim (fun e=>(shore_off D).1 (e ▸ xs))
      (fun e=>(shore_off D).2 (e ▸ xs)))
  have tdist (T : Finset V) (h : ∀ x∈T,G.dist x u=2) : T⊆DistanceTwo G u := by
    intro x xt
    exact mem_filter.mpr ⟨mem_univ _,(dist_comm (G:=G) (u:=x) (v:=u)) ▸ h x xt⟩
  have far' : 3≤G.dist b a := by rwa [dist_comm]
  have cd' : swapCut C≠swapCut D := fun e=>cd (swapCut.injective e)
  have ud' : u∈Shore (swapCut D) := by rwa [shore_swapCut]
  have detA (T : Finset V) (up : G.Adj a u) (tC : Disjoint T (Shore C))
      (tD : Disjoint T (Shore D)) (t2 : T⊆DistanceTwo G u) :
      Pa.card+H.card+T.card≤6 :=
    port_even_from_local_twos hc even cd ud up H T hd h2 tC tD t2
  have detB (T : Finset V) (up : G.Adj b u) (tC : Disjoint T (Shore C))
      (tD : Disjoint T (Shore D)) (t2 : T⊆DistanceTwo G u) :
      Pb.card+H.card+T.card≤6 := by
    simpa only [shore_swapCut] using (port_even_from_local_twos hc even cd' ud' up H T
      (by rwa [shore_swapCut]) h2 (by rwa [shore_swapCut]) (by rwa [shore_swapCut]) t2)
  have de (F : Finset V) (T : Finset V) (fs : F⊆Shore C)
      (f4 : ∀ x∈F,G.dist u x=4) (out : ∀ x∈T,x=a∨x=b) (dt : ∀ x∈T,G.dist x u=2) :
      H.card+F.card+T.card≤6 := by
    have r := even_budget_three even u H F T
      ((shore_disjoint cd.symm).mono hd fs) ((td T out).symm.mono_left hd)
      ((tc T out).symm.mono_left fs)
      (fun x xx=>in_positive_even_of_dist_two (mem_filter.mp (h2 xx)).2)
      (fun x xx=>mem_positive_four (f4 x xx))
      (fun x xx=>in_positive_even_of_dist_two (mem_filter.mp (tdist T dt xx)).2)
    exact r
  have oneA : ∀ x∈({a}:Finset V),x=a∨x=b := fun x xm=>.inl (mem_singleton.mp xm)
  have oneB : ∀ x∈({b}:Finset V),x=a∨x=b := fun x xm=>.inr (mem_singleton.mp xm)
  fin_cases i
  · have q := detA ∅ ur.1 (by simp) (by simp) (by simp)
    simp only [card_empty,Nat.add_zero] at q
    change H.card+Pa.card≤6
    omega
  · have q := detA {b} ur.1 (tc _ oneB) (td _ oneB)
      (tdist _ (fun x xx=>by rw [mem_singleton.mp xx]; exact ur.2))
    simp only [card_singleton] at q
    change H.card+(Pa.card+1)≤6
    omega
  · have q := detB ∅ ur.1 (by simp) (by simp) (by simp)
    simp only [card_empty,Nat.add_zero] at q
    change H.card+Pb.card≤6
    omega
  · have q := detB {a} ur.1 (tc _ oneA) (td _ oneA)
      (tdist _ (fun x xx=>by rw [mem_singleton.mp xx]; exact ur.2))
    simp only [card_singleton] at q
    change H.card+(Pb.card+1)≤6
    omega
  · obtain ⟨ua,ub,ea,nb⟩ := ur
    have db' := unseen_nonport_ge_three hc neqB.symm ub nb
    have s : (Pb∪K)⊆Shore C := union_subset bsub ks
    have f4 : ∀ x∈Pb∪K,G.dist u x=4 := by
      intro x xm
      rcases mem_union.mp xm with xb|xk
      · exact small_dark_cross_four hc far ab conn degree cd six ud (bsub xb) ea db' (mem_filter.mp xb).2
      · obtain ⟨xc,xa,xb⟩ := kData xk
        exact dark_to_k6_distance_four hc far ab conn degree cd six ud xc xa xb (by omega) (by omega) (.inl ea)
    have q := de _ {a} s f4 oneA (fun x xm=>by rw [mem_singleton.mp xm]; exact ea)
    rw [card_union_of_disjoint db,card_singleton,kc] at q
    change H.card+(Pb.card+1+(6-(Pa.card+Pb.card)))≤6
    omega
  · obtain ⟨ua,ub,na,eb⟩ := ur
    have da' := unseen_nonport_ge_three hc neqA.symm ua na
    have six' : (Shore (swapCut C)).card=6 := by rwa [shore_swapCut]
    have s : (Pa∪K)⊆Shore C := union_subset asub ks
    have f4 : ∀ x∈Pa∪K,G.dist u x=4 := by
      intro x xm
      rcases mem_union.mp xm with xa|xk
      · have xc' : x∈Shore (swapCut C) := by rw [shore_swapCut]; exact asub xa
        exact small_dark_cross_four hc far' ab.symm conn degree cd' six' ud' xc' eb da' (mem_filter.mp xa).2
      · obtain ⟨xc,xa,xb⟩ := kData xk
        exact dark_to_k6_distance_four hc far ab conn degree cd six ud xc xa xb (by omega) (by omega) (.inr eb)
    have q := de _ {b} s f4 oneB (fun x xm=>by rw [mem_singleton.mp xm]; exact eb)
    rw [card_union_of_disjoint da,card_singleton,kc] at q
    change H.card+(Pa.card+1+(6-(Pa.card+Pb.card)))≤6
    omega
  · obtain ⟨ua,ub,ea,eb⟩ := ur
    have f4 : ∀ x∈K,G.dist u x=4 := by
      intro x xm
      obtain ⟨xc,xa,xb⟩ := kData xm
      exact dark_to_k6_distance_four hc far ab conn degree cd six ud xc xa xb (by omega) (by omega) (.inl ea)
    have q := de K {a,b} ks f4 (fun x xm=>by simpa using xm)
      (fun x xm=>by rcases (show x=a∨x=b by simpa using xm) with rfl|rfl; exact ea; exact eb)
    rw [show ({a,b}:Finset V).card=2 by simp [ab],kc] at q
    change H.card+(2+(6-(Pa.card+Pb.card)))≤6
    omega
  · exact ((by decide : ¬((7:Fin 8).val<7)) hi).elim

#print axioms k6_profile_budget
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
