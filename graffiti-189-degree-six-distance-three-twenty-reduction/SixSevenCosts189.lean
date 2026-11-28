import SixSevenBridge189
namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair
open scoped BigOperators
open private Shore shore_disjoint shore_off shore_closed from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far from SixDistanceThreeShort189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open private each_foreign_port_is_distance_two from SixCutHighShore189
open private d2 from CrossSaturation189
open FiveAdjacent (shore_swapCut)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {C D : Cmp G a b}

theorem port_even_three_regions (hc : G.Connected) {r : V} (cd : C≠D)
    (even : ∀ v,(EvenFrom G v).card≤7) {u : V} (ud : u∈Shore D) (ru : G.Adj r u)
    (F H T : Finset V) (fC : F⊆Shore C) (f4 : ∀ x∈F,G.dist u x=4)
    (fn : Disjoint (cutPorts G (Shore C) r) F)
    (hD : H⊆Shore D) (h2 : H⊆DistanceTwo G u)
    (tC : Disjoint T (Shore C)) (tD : Disjoint T (Shore D)) (t2 : T⊆DistanceTwo G u) :
    (cutPorts G (Shore C) r).card+F.card+H.card+T.card≤6 := by
  classical
  let P := cutPorts G (Shore C) r
  have psub : P⊆Shore C := filter_subset _ _
  have fc : P∪F⊆Shore C := union_subset psub fC
  have q := even_budget_three even u (P∪F) H T
    ((shore_disjoint cd).mono fc hD) (tC.symm.mono_left fc) (tD.symm.mono_left hD)
    (by
      intro x xx
      rcases mem_union.mp xx with xp|xf
      · obtain ⟨xc,rx⟩ := mem_filter.mp xp
        have od : x∉Shore D := fun hd=>disjoint_left.mp (shore_disjoint cd) xc hd
        have ne : u≠x := fun e=>od (e ▸ ud)
        have no : ¬G.Adj u x := fun ux=>(shore_closed D u ud x ux).elim
          (fun e=>(shore_off C).1 (e ▸ xc)) (fun e=>e.elim (fun e=>(shore_off C).2 (e ▸ xc)) od)
        have t := d2 hc ne no ru.symm rx
        exact in_positive_even_of_dist_two (mem_filter.mp t).2
      · exact mem_positive_four (f4 x xf))
    (fun x xx=>in_positive_even_of_dist_two (mem_filter.mp (h2 xx)).2)
    (fun x xx=>in_positive_even_of_dist_two (mem_filter.mp (t2 xx)).2)
  rw [card_union_of_disjoint fn] at q
  omega

noncomputable def highShore (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V := S.filter (fun x => 6≤G.degree x)

theorem seven_eleven_port_cost_0 (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (seven : (Shore C).card=7) (eleven : (Shore D).card=11)
    {u : V} (ud : u∈Shore D) (uh : 6≤G.degree u) (us : sixClassSpec G a b u 0) :
    (cutPorts G (Shore C) a).card+(sixBucket G a b (Shore C) 2).card+(sixBucket G a b (Shore C) 5).card+(sixBucket G a b (Shore C) 7).card+(sixBucket G a b (highShore G (Shore D)) 2).card+(sixBucket G a b (highShore G (Shore D)) 3).card+(sixBucket G a b (highShore G (Shore D)) 5).card+(sixBucket G a b (highShore G (Shore D)) 7).card≤6 := by
  classical
  have kn (x : V) : ¬(G.Adj a x∧G.Adj b x) := no_common_far far
  have up : G.Adj a u := us.1
  let F : Finset (Fin 8) := {2,5,7}
  let H : Finset (Fin 8) := {2,3,5,7}
  let f := F.biUnion (sixBucket G a b (Shore C))
  let h := H.biUnion (sixBucket G a b (highShore G (Shore D)))
  let t : Finset V := ∅
  have fC : f⊆Shore C := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    exact (mem_sixBucket (kn x) j).mp jx |>.1
  have hD : h⊆Shore D := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    exact (mem_filter.mp ((mem_sixBucket (kn x) j).mp jx).1).1
  have h2 : h⊆DistanceTwo G u := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    obtain ⟨loc,role⟩ := (mem_sixBucket (kn x) j).mp jx
    obtain ⟨xd,xh⟩ := mem_filter.mp loc
    exact little_disallowed_local_even hc far eleven ud xd uh xh us role (by
      revert jj; fin_cases j <;> decide)

  have f4 : ∀ x∈f,G.dist u x=4 := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    obtain ⟨xc,xr⟩ := (mem_sixBucket (kn x) j).mp jx
    have js : j=2 ∨ j=5 ∨ j=7 := by simpa [F] using jj
    rcases js with rfl|rfl|rfl
    · exact opposite_unseen_cross_four hc far ab conn degree cd seven eleven ud xc uh up xr.1 us.2 xr.2
    · exact unseen_dark_cross_four hc far ab conn degree cd seven ud xc up xr.1 xr.2.1 xr.2.2.1
    · exact unseen_dark_cross_four hc far ab conn degree cd seven ud xc up xr.1 xr.2.1 xr.2.2.1

  have dis : Disjoint (cutPorts G (Shore C) a) f := by
    apply disjoint_left.mpr
    intro x xp xf
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xf
    have r := ((mem_sixBucket (kn x) j).mp jx).2
    have port := (mem_filter.mp xp).2
    have nj := kn x
    fin_cases j <;> (first | exact (by decide : ¬(_∈F)) jj | simp only [sixClassSpec] at r; tauto)
  have tC : Disjoint t (Shore C) := by
    simp [t]
  have tD : Disjoint t (Shore D) := by
    simp [t]
  have t2 : t⊆DistanceTwo G u := by
    simp [t]
  have q := port_even_three_regions hc cd even ud up f h t fC f4 dis hD h2 tC tD t2
  dsimp only [f,h] at q
  rw [role_family_card,role_family_card] at q
  simpa [F,H,t,Finset.sum_insert,Nat.add_assoc] using q

#print axioms seven_eleven_port_cost_0

theorem seven_eleven_port_cost_1 (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (seven : (Shore C).card=7) (eleven : (Shore D).card=11)
    {u : V} (ud : u∈Shore D) (uh : 6≤G.degree u) (us : sixClassSpec G a b u 1) :
    (cutPorts G (Shore C) a).card+(sixBucket G a b (Shore C) 5).card+(sixBucket G a b (Shore C) 7).card+(sixBucket G a b (highShore G (Shore D)) 2).card+(sixBucket G a b (highShore G (Shore D)) 5).card+(sixBucket G a b (highShore G (Shore D)) 7).card + 1≤6 := by
  classical
  have kn (x : V) : ¬(G.Adj a x∧G.Adj b x) := no_common_far far
  have up : G.Adj a u := us.1
  let F : Finset (Fin 8) := {5,7}
  let H : Finset (Fin 8) := {2,5,7}
  let f := F.biUnion (sixBucket G a b (Shore C))
  let h := H.biUnion (sixBucket G a b (highShore G (Shore D)))
  let t : Finset V := {b}
  have fC : f⊆Shore C := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    exact (mem_sixBucket (kn x) j).mp jx |>.1
  have hD : h⊆Shore D := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    exact (mem_filter.mp ((mem_sixBucket (kn x) j).mp jx).1).1
  have h2 : h⊆DistanceTwo G u := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    obtain ⟨loc,role⟩ := (mem_sixBucket (kn x) j).mp jx
    obtain ⟨xd,xh⟩ := mem_filter.mp loc
    exact little_disallowed_local_even hc far eleven ud xd uh xh us role (by
      revert jj; fin_cases j <;> decide)

  have f4 : ∀ x∈f,G.dist u x=4 := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    obtain ⟨xc,xr⟩ := (mem_sixBucket (kn x) j).mp jx
    have js : j=5 ∨ j=7 := by simpa [F] using jj
    rcases js with rfl|rfl
    · exact unseen_dark_cross_four hc far ab conn degree cd seven ud xc up xr.1 xr.2.1 xr.2.2.1
    · exact unseen_dark_cross_four hc far ab conn degree cd seven ud xc up xr.1 xr.2.1 xr.2.2.1

  have dis : Disjoint (cutPorts G (Shore C) a) f := by
    apply disjoint_left.mpr
    intro x xp xf
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xf
    have r := ((mem_sixBucket (kn x) j).mp jx).2
    have port := (mem_filter.mp xp).2
    have nj := kn x
    fin_cases j <;> (first | exact (by decide : ¬(_∈F)) jj | simp only [sixClassSpec] at r; tauto)
  have tC : Disjoint t (Shore C) := by
    exact disjoint_left.mpr (fun x xt xc=>(shore_off C).2 ((mem_singleton.mp xt) ▸ xc))
  have tD : Disjoint t (Shore D) := by
    exact disjoint_left.mpr (fun x xt xd=>(shore_off D).2 ((mem_singleton.mp xt) ▸ xd))
  have t2 : t⊆DistanceTwo G u := by
    intro x xt; rw [mem_singleton.mp xt]; simp [DistanceTwo,dist_comm (u:=u) (v:=b),us.2]
  have q := port_even_three_regions hc cd even ud up f h t fC f4 dis hD h2 tC tD t2
  dsimp only [f,h] at q
  rw [role_family_card,role_family_card] at q
  simpa [F,H,t,Finset.sum_insert,Nat.add_assoc] using q

#print axioms seven_eleven_port_cost_1

theorem seven_eleven_port_cost_2 (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (seven : (Shore C).card=7) (eleven : (Shore D).card=11)
    {u : V} (ud : u∈Shore D) (uh : 6≤G.degree u) (us : sixClassSpec G a b u 2) :
    (cutPorts G (Shore C) b).card+(sixBucket G a b (Shore C) 0).card+(sixBucket G a b (Shore C) 4).card+(sixBucket G a b (Shore C) 7).card+(sixBucket G a b (highShore G (Shore D)) 0).card+(sixBucket G a b (highShore G (Shore D)) 1).card+(sixBucket G a b (highShore G (Shore D)) 4).card+(sixBucket G a b (highShore G (Shore D)) 7).card≤6 := by
  classical
  have kn (x : V) : ¬(G.Adj a x∧G.Adj b x) := no_common_far far
  have up : G.Adj b u := us.1
  let F : Finset (Fin 8) := {0,4,7}
  let H : Finset (Fin 8) := {0,1,4,7}
  let f := F.biUnion (sixBucket G a b (Shore C))
  let h := H.biUnion (sixBucket G a b (highShore G (Shore D)))
  let t : Finset V := ∅
  have fC : f⊆Shore C := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    exact (mem_sixBucket (kn x) j).mp jx |>.1
  have hD : h⊆Shore D := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    exact (mem_filter.mp ((mem_sixBucket (kn x) j).mp jx).1).1
  have h2 : h⊆DistanceTwo G u := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    obtain ⟨loc,role⟩ := (mem_sixBucket (kn x) j).mp jx
    obtain ⟨xd,xh⟩ := mem_filter.mp loc
    exact little_disallowed_local_even hc far eleven ud xd uh xh us role (by
      revert jj; fin_cases j <;> decide)

  have far' : 3≤G.dist b a := by rwa [dist_comm]
  have cd' : swapCut C≠swapCut D := fun e=>cd (swapCut.injective e)
  have ud' : u∈Shore (swapCut D) := by rwa [shore_swapCut]
  have s' : (Shore (swapCut C)).card=7 := by rwa [shore_swapCut]
  have e' : (Shore (swapCut D)).card=11 := by rwa [shore_swapCut]

  have f4 : ∀ x∈f,G.dist u x=4 := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    obtain ⟨xc,xr⟩ := (mem_sixBucket (kn x) j).mp jx
    have xc' : x∈Shore (swapCut C) := by rwa [shore_swapCut]
    have js : j=0 ∨ j=4 ∨ j=7 := by simpa [F] using jj
    rcases js with rfl|rfl|rfl
    · exact opposite_unseen_cross_four hc far' ab.symm conn degree cd' s' e' ud' xc' uh up xr.1 us.2 xr.2
    · exact unseen_dark_cross_four hc far' ab.symm conn degree cd' s' ud' xc' up xr.2.1 xr.1 xr.2.2.2
    · exact unseen_dark_cross_four hc far' ab.symm conn degree cd' s' ud' xc' up xr.2.1 xr.1 xr.2.2.2

  have dis : Disjoint (cutPorts G (Shore C) b) f := by
    apply disjoint_left.mpr
    intro x xp xf
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xf
    have r := ((mem_sixBucket (kn x) j).mp jx).2
    have port := (mem_filter.mp xp).2
    have nj := kn x
    fin_cases j <;> (first | exact (by decide : ¬(_∈F)) jj | simp only [sixClassSpec] at r; tauto)
  have tC : Disjoint t (Shore C) := by
    simp [t]
  have tD : Disjoint t (Shore D) := by
    simp [t]
  have t2 : t⊆DistanceTwo G u := by
    simp [t]
  have q := port_even_three_regions hc cd even ud up f h t fC f4 dis hD h2 tC tD t2
  dsimp only [f,h] at q
  rw [role_family_card,role_family_card] at q
  simpa [F,H,t,Finset.sum_insert,Nat.add_assoc] using q

#print axioms seven_eleven_port_cost_2

theorem seven_eleven_port_cost_3 (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (seven : (Shore C).card=7) (eleven : (Shore D).card=11)
    {u : V} (ud : u∈Shore D) (uh : 6≤G.degree u) (us : sixClassSpec G a b u 3) :
    (cutPorts G (Shore C) b).card+(sixBucket G a b (Shore C) 4).card+(sixBucket G a b (Shore C) 7).card+(sixBucket G a b (highShore G (Shore D)) 0).card+(sixBucket G a b (highShore G (Shore D)) 4).card+(sixBucket G a b (highShore G (Shore D)) 7).card + 1≤6 := by
  classical
  have kn (x : V) : ¬(G.Adj a x∧G.Adj b x) := no_common_far far
  have up : G.Adj b u := us.1
  let F : Finset (Fin 8) := {4,7}
  let H : Finset (Fin 8) := {0,4,7}
  let f := F.biUnion (sixBucket G a b (Shore C))
  let h := H.biUnion (sixBucket G a b (highShore G (Shore D)))
  let t : Finset V := {a}
  have fC : f⊆Shore C := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    exact (mem_sixBucket (kn x) j).mp jx |>.1
  have hD : h⊆Shore D := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    exact (mem_filter.mp ((mem_sixBucket (kn x) j).mp jx).1).1
  have h2 : h⊆DistanceTwo G u := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    obtain ⟨loc,role⟩ := (mem_sixBucket (kn x) j).mp jx
    obtain ⟨xd,xh⟩ := mem_filter.mp loc
    exact little_disallowed_local_even hc far eleven ud xd uh xh us role (by
      revert jj; fin_cases j <;> decide)

  have far' : 3≤G.dist b a := by rwa [dist_comm]
  have cd' : swapCut C≠swapCut D := fun e=>cd (swapCut.injective e)
  have ud' : u∈Shore (swapCut D) := by rwa [shore_swapCut]
  have s' : (Shore (swapCut C)).card=7 := by rwa [shore_swapCut]
  have e' : (Shore (swapCut D)).card=11 := by rwa [shore_swapCut]

  have f4 : ∀ x∈f,G.dist u x=4 := by
    intro x xx
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xx
    obtain ⟨xc,xr⟩ := (mem_sixBucket (kn x) j).mp jx
    have xc' : x∈Shore (swapCut C) := by rwa [shore_swapCut]
    have js : j=4 ∨ j=7 := by simpa [F] using jj
    rcases js with rfl|rfl
    · exact unseen_dark_cross_four hc far' ab.symm conn degree cd' s' ud' xc' up xr.2.1 xr.1 xr.2.2.2
    · exact unseen_dark_cross_four hc far' ab.symm conn degree cd' s' ud' xc' up xr.2.1 xr.1 xr.2.2.2

  have dis : Disjoint (cutPorts G (Shore C) b) f := by
    apply disjoint_left.mpr
    intro x xp xf
    obtain ⟨j,jj,jx⟩ := mem_biUnion.mp xf
    have r := ((mem_sixBucket (kn x) j).mp jx).2
    have port := (mem_filter.mp xp).2
    have nj := kn x
    fin_cases j <;> (first | exact (by decide : ¬(_∈F)) jj | simp only [sixClassSpec] at r; tauto)
  have tC : Disjoint t (Shore C) := by
    exact disjoint_left.mpr (fun x xt xc=>(shore_off C).1 ((mem_singleton.mp xt) ▸ xc))
  have tD : Disjoint t (Shore D) := by
    exact disjoint_left.mpr (fun x xt xd=>(shore_off D).1 ((mem_singleton.mp xt) ▸ xd))
  have t2 : t⊆DistanceTwo G u := by
    intro x xt; rw [mem_singleton.mp xt]; simp [DistanceTwo,dist_comm (u:=u) (v:=a),us.2]
  have q := port_even_three_regions hc cd even ud up f h t fC f4 dis hD h2 tC tD t2
  dsimp only [f,h] at q
  rw [role_family_card,role_family_card] at q
  simpa [F,H,t,Finset.sum_insert,Nat.add_assoc] using q

#print axioms seven_eleven_port_cost_3

end Graffiti189LongestPath.CrossSaturation.ThresholdSix
