import SixSingletonActual189
import SixSingletonThreeBoard189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
open private Dark Common strictA strictB bal singleton_neighborhood_exact a_port_lower_singleton_dist_two
  vis_six_of_nonadjacent_singleton all_dark_depth_two_of_visible_six from SixSingletonGeometry189
open private no_port_domination port_diff_one common_partition class_partition class_strict_dis class_bal_dis
  strict_port_data at_least_two_strict from SixSingletonShape189
open private card_preimage_label inside_label from SixSingletonLabel189
open private d2 from CrossSaturation189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut depth label_degree label_even label_dist traceable_label)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000

/-- Order-sixteen singleton closure for every nonadjacent cut profile. -/
theorem traceable_of_nonadjacent_singleton_thirteen
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_cases q2 : (bal D).card≤2
  · exact traceable_of_nonadjacent_singleton_thirteen_at_most_two_balanced hc two even conn degree
      sd cover one d13 q2
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have non : ¬G.Adj a b := fun e=>by have h := dist_eq_one_iff_adj.mpr e; omega
  obtain ⟨s,sS⟩ := card_eq_one.mp one
  have ss : s∈Shore S := by simp [sS]
  have sa : s≠a := fun e=>(shore_off S).1 (e ▸ ss)
  have sb : s≠b := fun e=>(shore_off S).2 (e ▸ ss)
  obtain ⟨sa',saS,asa⟩ := shore_hit_a ab conn S
  obtain ⟨sb',sbS,bsb⟩ := shore_hit_b ab conn S
  have as' : G.Adj a s := (show sa'=s by simpa only [sS,mem_singleton] using saS) ▸ asa
  have bs' : G.Adj b s := (show sb'=s by simpa only [sS,mem_singleton] using sbS) ▸ bsb
  have s2 : G.degree s=2 := by
    rw [←card_neighborFinset_eq_degree,singleton_neighborhood_exact sS as' bs',
      card_insert_of_not_mem (by simpa using ab),card_singleton]
  have high {z : V} (ne : z≠s) : 6≤G.degree z := (degree z s ne).resolve_right (by omega)
  have hiD (z : V) (zd : z∈Shore D) : 6≤G.degree z :=
    high (fun h=>disjoint_left.mp (shore_disjoint sd) ss (h ▸ zd))
  have a5 := a_port_lower_singleton_dist_two sd cover sS (high sa.symm) non
  have b5 : 5≤(bPorts D).card := by
    have s' : Shore (swapCut S)=({s}:Finset V) := by rwa [shore_swapCut]
    have g := a_port_lower_singleton_dist_two (a:=b) (b:=a)
      (S:=swapCut S) (D:=swapCut D) (fun h=>sd (swapCut.injective h))
      (fun zb za=>by rw [shore_swapCut,shore_swapCut]; exact cover za zb)
      s' (high sb.symm) (fun e=>non e.symm)
    simpa only [aPorts,bPorts,shore_swapCut] using g
  have v6 := vis_six_of_nonadjacent_singleton hc even ab non sd d13 cover sS as' bs' a5 b5
  have d7 : (Dark D).card=7 := by
    change (Shore D\Vis D).card=7
    rw [card_sdiff (vis_sub D),d13,v6]
  have near := all_dark_depth_two_of_visible_six hc even sd sS as' bs' v6
  have aN := no_port_domination hc even d7 near
  have swapDark : Dark (swapCut D)=Dark D := by
    simp only [Dark,Vis,shore_swapCut]
    congr 1
    ext z
    simp only [mem_filter]
    rw [or_comm (a:=G.Adj b z) (b:=G.Adj a z)]
  have swapNear : ∀ z∈Dark (swapCut D),depth G b a z=2 := by
    intro z zm
    rw [swapDark] at zm
    simpa only [depth,min_comm] using (near z zm)
  have bN : ¬bPorts D⊆aPorts D := by
    have s := no_port_domination (a:=b) (b:=a) hc even (by rwa [swapDark]) swapNear
    simpa only [aPorts,bPorts,shore_swapCut] using s
  have ae := port_diff_one v6 b5 aN
  have be : (bPorts D\aPorts D).card=1 := by
    have visSwap : Vis (swapCut D)=Vis D := by
      simp only [Vis,shore_swapCut]
      ext z
      simp only [mem_filter]
      rw [or_comm (a:=G.Adj b z) (b:=G.Adj a z)]
    have m := port_diff_one (D:=swapCut D) (by rwa [visSwap])
      (by simpa only [aPorts,bPorts,shore_swapCut] using a5)
      (by simpa only [aPorts,bPorts,shore_swapCut] using bN)
    simpa only [aPorts,bPorts,shore_swapCut] using m
  obtain ⟨x,xonly⟩ := card_eq_one.mp ae
  obtain ⟨y,yonly⟩ := card_eq_one.mp be
  have xp : x∈aPorts D\bPorts D := by simp [xonly]
  have yp : y∈bPorts D\aPorts D := by simp [yonly]
  have xx := mem_sdiff.mp xp
  have yy := mem_sdiff.mp yp
  have xyz : x≠y := fun e=>xx.2 (e.symm ▸ yy.1)
  have cX : x∉Common D := fun h=>xx.2 (mem_inter.mp h).2
  have cY : y∉Common D := fun h=>yy.2 (mem_inter.mp h).1
  have VP := common_partition xonly yonly
  have c4 : (Common D).card=4 := by
    rw [VP,card_insert_of_not_mem (by simp [xyz,cX]),card_insert_of_not_mem cY] at v6
    omega
  have size : Fintype.card V=16 := by
    have k := shore_sum_with_cover ab sd cover
    omega
  have shell (z : V) :
      z=a ∨ z=b ∨ z=s ∨ z=x ∨ z=y ∨ z∈Common D ∨ z∈Dark D := by
    by_cases za : z=a
    · exact .inl za
    by_cases zb : z=b
    · exact .inr (.inl zb)
    rcases cover za zb with zs|zd
    · exact .inr (.inr (.inl (by simpa only [sS,mem_singleton] using zs)))
    by_cases p : z∈Vis D
    · rw [VP] at p
      rcases mem_insert.mp p with p|p
      · exact .inr (.inr (.inr (.inl p)))
      rcases mem_insert.mp p with p|p
      · exact .inr (.inr (.inr (.inr (.inl p))))
      exact .inr (.inr (.inr (.inr (.inr (.inl p)))))
    exact .inr (.inr (.inr (.inr (.inr (.inr (mem_sdiff.mpr ⟨zd,p⟩))))))
  obtain ⟨e,fa,fb,fs,fx,fy,fK,fD⟩ := singleton_board_label size a b s x y (Common D) (Dark D) c4 d7 shell
  let J := G.comap e
  let iso : J ≃g G := SimpleGraph.Iso.comap e G
  let L : Finset I16 := univ.filter (fun i=>e i∈strictA D)
  let R : Finset I16 := univ.filter (fun i=>e i∈strictB D)
  have Lm (i : I16) : i∈L↔e i∈strictA D := by simp [L]
  have Rm (i : I16) : i∈R↔e i∈strictB D := by simp [R]
  have Left := strict_port_data hc xonly near hiD
  have Right :
      (∀ z∈strictB D,G.Adj y z) ∧
        ∀ z∈strictB D,5≤(inside G (Dark D) z).card := by
    have eq : strictA (swapCut D)=strictB D := by simp only [strictA,strictB,swapDark]
    have s := strict_port_data (a:=b) (b:=a) hc (D:=swapCut D) (x:=y)
      (by simpa only [aPorts,bPorts,shore_swapCut] using yonly) swapNear
      (fun z m=>hiD z (by simpa only [shore_swapCut] using m))
    simpa only [swapDark,eq] using s
  have lR := at_least_two_strict hc two even d7 near
  have cnt : (strictA D∪strictB D).card+(bal D).card=7 := by
    have hh := card_union_of_disjoint (class_bal_dis D)
    rw [class_partition,d7] at hh
    exact hh.symm
  have cLR := card_union_of_disjoint (class_strict_dis D)
  have q3 : (bal D).card=3 := by have h := lR.1; have j := lR.2; omega
  have l2 : (strictA D).card=2 := by have h := lR.1; have j := lR.2; omega
  have r2 : (strictB D).card=2 := by have h := lR.1; have j := lR.2; omega
  have lk : L⊆Singleton16.D := fun i h=>(fD _).mpr (mem_filter.mp ((Lm _).mp h)).1
  have rk : R⊆Singleton16.D := fun i h=>(fD _).mpr (mem_filter.mp ((Rm _).mp h)).1
  have ld : Disjoint L R := disjoint_left.mpr (fun i il ir=>
    disjoint_left.mp (class_strict_dis D) ((Lm _).mp il) ((Rm _).mp ir))
  have lifted (i j : I16) : J.Adj i j ↔ G.Adj (e i) (e j) := Iff.rfl
  have port_pull {j : I16} (p : e j∈Vis D) : j∈Singleton16.P := by
    rw [VP] at p
    rcases mem_insert.mp p with h|h
    · exact mem_insert.mpr (.inl (e.injective (h.trans fx.symm)))
    rcases mem_insert.mp h with h|h
    · exact mem_insert_of_mem (mem_insert.mpr (.inl (e.injective (h.trans fy.symm))))
    exact mem_insert_of_mem (mem_insert_of_mem ((fK _).mpr h))
  have cBound (u : I16) (uc : u∈Singleton16.K) (z : I16) (uz : J.Adj u z) :
      z∈insert Singleton16.a (insert Singleton16.b (Singleton16.P∪(Singleton16.D\(L∪R)))) := by
    have uk := (fK _).mp uc
    have ⟨ua,ub⟩ := mem_inter.mp uk
    have uD := (mem_filter.mp ua).1
    have uA := (mem_filter.mp ua).2
    have uB := (mem_filter.mp ub).2
    have edge := (lifted _ _).mp uz
    rcases shore_closed D (e u) uD (e z) edge with q|q|q
    · exact mem_insert.mpr (.inl (e.injective (q.trans fa.symm)))
    · exact mem_insert_of_mem (mem_insert.mpr (.inl (e.injective (q.trans fb.symm))))
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    by_cases vv : e z∈Vis D
    · exact mem_union_left _ (port_pull vv)
    have dz : e z∈Dark D := mem_sdiff.mpr ⟨q,vv⟩
    have az : ¬G.Adj a (e z) := fun h=>vv (mem_filter.mpr ⟨q,.inl h⟩)
    have bz : ¬G.Adj b (e z) := fun h=>vv (mem_filter.mpr ⟨q,.inr h⟩)
    have na : a≠e z := fun h=>(shore_off D).1 (h.symm ▸ q)
    have nb : b≠e z := fun h=>(shore_off D).2 (h.symm ▸ q)
    have da := (mem_filter.mp (d2 hc na az uA edge)).2
    have db := (mem_filter.mp (d2 hc nb bz uB edge)).2
    exact mem_union_right _ (mem_sdiff.mpr ⟨(fD _).mpr dz,fun h=>by
      rcases mem_union.mp h with hl|hr
      · have hx := (mem_filter.mp ((Lm _).mp hl)).2
        omega
      have hy := (mem_filter.mp ((Rm _).mp hr)).2
      omega⟩)
  let W := Singleton16.D\(L∪R)
  have bal_eq {z : I16} (zm : z∈W) : G.dist a (e z)=2 ∧ G.dist b (e z)=2 := by
    have ⟨zd,zno⟩ := mem_sdiff.mp zm
    have dark := (fD _).mp zd
    have ne := near (e z) dark
    change min (G.dist a (e z)) (G.dist b (e z))=2 at ne
    have na : ¬G.dist a (e z)<G.dist b (e z) := fun h=>zno <|
      mem_union_left _ ((Lm _).mpr (mem_filter.mpr ⟨dark,h⟩))
    have nb : ¬G.dist b (e z)<G.dist a (e z) := fun h=>zno <|
      mem_union_right _ ((Rm _).mpr (mem_filter.mpr ⟨dark,h⟩))
    omega
  have strictL {z : I16} (zm : z∈L) : G.dist a (e z)=2 ∧ 2<G.dist b (e z) := by
    have h := (mem_filter.mp ((Lm _).mp zm)).2
    have d := near _ (mem_filter.mp ((Lm _).mp zm)).1
    change min (G.dist a (e z)) (G.dist b (e z))=2 at d
    omega
  have strictR {z : I16} (zm : z∈R) : G.dist b (e z)=2 ∧ 2<G.dist a (e z) := by
    have h := (mem_filter.mp ((Rm _).mp zm)).2
    have d := near _ (mem_filter.mp ((Rm _).mp zm)).1
    change min (G.dist a (e z)) (G.dist b (e z))=2 at d
    omega
  have xn : ¬G.Adj b x := fun e=>xx.2 (mem_filter.mpr ⟨(mem_filter.mp xx.1).1,e⟩)
  have yn : ¬G.Adj a y := fun e=>yy.2 (mem_filter.mpr ⟨(mem_filter.mp yy.1).1,e⟩)
  have no_s {z : V} (zd : z∈Shore D) : ¬G.Adj s z := by
    intro h
    have q := (mem_neighborFinset _ _ _).mpr h
    rw [singleton_neighborhood_exact sS as' bs'] at q
    rcases (by simpa using q : z=a ∨ z=b) with e|e
    · exact (shore_off D).1 (e ▸ zd)
    exact (shore_off D).2 (e ▸ zd)
  have frame : Singleton16.ThreeBoard J L R := by
    refine ⟨lk,rk,ld,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,cBound,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · change (univ.filter (fun i : I16=>e i∈strictA D)).card=2
      rw [card_preimage_label]
      exact l2
    · change (univ.filter (fun i : I16=>e i∈strictB D)).card=2
      rw [card_preimage_label]
      exact r2
    · apply (lifted _ _).mpr; rw [fs,fa]; exact as'.symm
    · apply (lifted _ _).mpr; rw [fs,fb]; exact bs'.symm
    · apply (lifted _ _).mpr; rw [fa,fx]; exact (mem_filter.mp xx.1).2
    · apply (lifted _ _).mpr; rw [fb,fy]; exact (mem_filter.mp yy.1).2
    · intro z hz
      apply (lifted _ _).mpr
      rw [fa]
      exact (mem_filter.mp (mem_inter.mp ((fK _).mp hz)).1).2
    · intro z hz
      apply (lifted _ _).mpr
      rw [fb]
      exact (mem_filter.mp (mem_inter.mp ((fK _).mp hz)).2).2
    · intro z hz
      apply (lifted _ _).mpr
      rw [fx]
      exact Left.1 _ ((Lm _).mp hz)
    · intro z hz
      apply (lifted _ _).mpr
      rw [fy]
      exact Right.1 _ ((Rm _).mp hz)
    · intro z hz
      change 5≤(inside (G.comap e) Singleton16.D z).card
      rw [inside_label e _ _ fD]
      exact (mem_union.mp hz).elim (fun h=>Left.2 _ ((Lm _).mp h)) (fun h=>Right.2 _ ((Rm _).mp h))
    · intro z hz
      rw [label_degree iso]
      exact hiD _ (mem_filter.mp (mem_inter.mp ((fK _).mp hz)).1).1
    · rw [label_degree iso,label_degree iso]
      change 6≤G.degree (e 3) ∧ 6≤G.degree (e 4)
      rw [fx,fy]
      exact ⟨hiD _ (mem_filter.mp xx.1).1,hiD _ (mem_filter.mp yy.1).1⟩
    · rw [label_dist iso hc]
      change G.dist (e 0) (e 1)=2
      rwa [fa,fb]
    · rw [lifted,fb,fx]
      exact xn
    · rw [lifted,fa,fy]
      exact yn
    · rw [lifted,fs,fx]
      exact no_s (mem_filter.mp xx.1).1
    · rw [lifted,fs,fy]
      exact no_s (mem_filter.mp yy.1).1
    · intro z zm
      rw [label_dist iso hc]
      change G.dist (e 0) (e z)=2
      rw [fa]
      exact (mem_union.mp zm).elim (fun h=>(strictL h).1) (fun h=>(bal_eq h).1)
    · intro z zm
      rw [label_dist iso hc]
      change G.dist (e 1) (e z)=2
      rw [fb]
      exact (mem_union.mp zm).elim (fun h=>(strictR h).1) (fun h=>(bal_eq h).2)
    · intro z zm
      rw [label_dist iso hc]
      change 2<G.dist (e 1) (e z)
      rw [fb]
      exact (strictL zm).2
    · intro z zm
      rw [label_dist iso hc]
      change 2<G.dist (e 0) (e z)
      rw [fa]
      exact (strictR zm).2
  apply traceable_label iso
  apply Singleton16.traceable_of_normalized_singleton_three_balanced frame (iso.connected_iff.mpr hc)
  intro z
  rw [label_even iso hc]
  exact even _

#print axioms traceable_of_nonadjacent_singleton_thirteen
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
