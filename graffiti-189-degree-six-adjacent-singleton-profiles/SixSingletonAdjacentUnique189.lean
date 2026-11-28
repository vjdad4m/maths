import SixSingletonActual189

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
open FiveAdjacent (shore_swapCut depth label_degree label_even traceable_label)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000

private theorem at_least_two_strict_off_slots {u v : V} (u2 : G.dist a u=2) (v2 : G.dist b v=2)
    (even : ∀ z,(EvenFrom G z).card≤7)
    {D : Cmp G a b} (d7 : (Dark D).card=7)
    (near : ∀ z∈Dark D,depth G a b z=2) (un : u∉Dark D) (vn : v∉Dark D) :
    2≤(strictA D).card ∧ 2≤(strictB D).card := by
  classical
  have n : (strictA D).card+(strictB D).card+(bal D).card=7 := by
    have p := card_union_of_disjoint (class_bal_dis D)
    rw [class_partition,d7,card_union_of_disjoint (class_strict_dis D)] at p
    omega
  have allA : strictA D⊆DistanceTwo G a := by
    intro z zm
    have ⟨zD,l⟩ := mem_filter.mp zm
    have r := near z zD
    change min (G.dist a z) (G.dist b z)=2 at r
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have allB : strictB D⊆DistanceTwo G b := by
    intro z zm
    have ⟨zD,l⟩ := mem_filter.mp zm
    have r := near z zD
    change min (G.dist a z) (G.dist b z)=2 at r
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have via {t : V} (T : Finset V) (d : Disjoint T (bal D))
      (sub : T⊆DistanceTwo G t)
      (evenT : (DistanceTwo G t).card≤6) {o : V} (ot : G.dist t o=2)
      (no : o∉T) (noBal : o∉bal D) (eq : ∀ z∈bal D,G.dist t z=2) :
      T.card+(bal D).card≤5 := by
    have h : insert o (T∪bal D)⊆DistanceTwo G t :=
      insert_subset (mem_filter.mpr ⟨mem_univ _,ot⟩)
        (union_subset sub (fun z zm=>mem_filter.mpr ⟨mem_univ _,eq z zm⟩))
    have c := card_le_card h
    rw [card_insert_of_not_mem (by simp [no,noBal]),card_union_of_disjoint d] at c
    omega
  have da : Disjoint (strictA D) (bal D) := (class_bal_dis D).mono_left subset_union_left
  have db : Disjoint (strictB D) (bal D) := (class_bal_dis D).mono_left subset_union_right
  have M := via (t:=a) (strictA D) da allA (distanceTwo_le_of_even 6 a (even a)) u2
    (fun h=>un (mem_filter.mp h).1) (fun h=>un (mem_filter.mp h).1)
    (fun z zm=>by
      have ⟨d,e⟩ := mem_filter.mp zm
      have p := near z d
      change min (G.dist a z) (G.dist b z)=2 at p
      omega)
  have N := via (t:=b) (strictB D) db allB (distanceTwo_le_of_even 6 b (even b)) v2
    (fun h=>vn (mem_filter.mp h).1) (fun h=>vn (mem_filter.mp h).1)
    (fun z zm=>by
      have ⟨d,e⟩ := mem_filter.mp zm
      have p := near z d
      change min (G.dist a z) (G.dist b z)=2 at p
      omega)
  omega

/-- Adjacent singleton plus thirteen with six visible vertices, unique
exclusive port on each side, and at most two balanced dark vertices. -/
theorem traceable_of_adjacent_singleton_thirteen_unique_at_most_two_balanced
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v6 : (Vis D).card=6)
    (ae : (aPorts D\bPorts D).card=1) (be : (bPorts D\aPorts D).card=1)
    (q2 : (bal D).card≤2) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have ne : a≠b := ab.ne
  obtain ⟨s,sS⟩ := card_eq_one.mp one
  have ss : s∈Shore S := by simp [sS]
  obtain ⟨sa',saS,asa⟩ := shore_hit_a ne conn S
  obtain ⟨sb',sbS,bsb⟩ := shore_hit_b ne conn S
  have as' : G.Adj a s := (show sa'=s by simpa only [sS,mem_singleton] using saS) ▸ asa
  have bs' : G.Adj b s := (show sb'=s by simpa only [sS,mem_singleton] using sbS) ▸ bsb
  have s2 : G.degree s=2 := by
    rw [←card_neighborFinset_eq_degree,singleton_neighborhood_exact sS as' bs',
      card_insert_of_not_mem (by simpa using ne),card_singleton]
  have high {z : V} (ne : z≠s) : 6≤G.degree z := (degree z s ne).resolve_right (by omega)
  have hiD (z : V) (zd : z∈Shore D) : 6≤G.degree z :=
    high (fun h=>disjoint_left.mp (shore_disjoint sd) ss (h ▸ zd))
  have d7 : (Dark D).card=7 := by
    change (Shore D\Vis D).card=7
    rw [card_sdiff (vis_sub D),d13,v6]
  have near := all_dark_depth_two_of_visible_six hc even sd sS as' bs' v6
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
    have k := shore_sum_with_cover ne sd cover
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
  have xv : x∈Vis D := mem_filter.mpr ⟨(mem_filter.mp xx.1).1,.inl (mem_filter.mp xx.1).2⟩
  have yv : y∈Vis D := mem_filter.mpr ⟨(mem_filter.mp yy.1).1,.inr (mem_filter.mp yy.1).2⟩
  have xno : ¬G.Adj b x := fun bx=>xx.2 (mem_filter.mpr ⟨(mem_filter.mp xx.1).1,bx⟩)
  have yno : ¬G.Adj a y := fun ay=>yy.2 (mem_filter.mpr ⟨(mem_filter.mp yy.1).1,ay⟩)
  have x2 := (mem_filter.mp (d2 (x:=b) (z:=x) hc (fun e=>(shore_off D).2 (e.symm ▸ (mem_filter.mp xx.1).1))
    xno ab.symm (mem_filter.mp xx.1).2)).2
  have y2 := (mem_filter.mp (d2 (x:=a) (z:=y) hc (fun e=>(shore_off D).1 (e.symm ▸ (mem_filter.mp yy.1).1))
    yno ab (mem_filter.mp yy.1).2)).2
  have lR := at_least_two_strict_off_slots y2 x2 even d7 near
    (fun h=>(mem_sdiff.mp h).2 yv) (fun h=>(mem_sdiff.mp h).2 xv)
  have cnt : (strictA D∪strictB D).card+(bal D).card=7 := by
    have hh := card_union_of_disjoint (class_bal_dis D)
    rw [class_partition,d7] at hh
    exact hh.symm
  have L5 : 5≤(L∪R).card := by
    have eq : L∪R=univ.filter (fun i=>e i∈strictA D∪strictB D) := by
      ext i
      simp only [mem_union,mem_filter,mem_univ,true_and,Lm,Rm]
    rw [eq,card_preimage_label]
    omega
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
  have dBound (u : I16) (ud : u∈Singleton16.D) (z : I16) (uz : J.Adj u z) :
      z∈Singleton16.P∪Singleton16.D := by
    have ⟨dz,dark⟩ := mem_sdiff.mp ((fD _).mp ud)
    have edge := (lifted _ _).mp uz
    rcases shore_closed D (e u) dz (e z) edge with r|r|r
    · exact (dark (mem_filter.mpr ⟨dz,.inl (r ▸ edge.symm)⟩)).elim
    · exact (dark (mem_filter.mpr ⟨dz,.inr (r ▸ edge.symm)⟩)).elim
    by_cases p : e z∈Vis D
    · exact mem_union_left _ (port_pull p)
    exact mem_union_right _ ((fD _).mpr (mem_sdiff.mpr ⟨r,p⟩))
  have frame : Singleton16.Frame J L R := by
    refine ⟨lk,rk,ld,?_,?_,L5,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,cBound,dBound⟩
    · change 2≤(univ.filter (fun i : I16=>e i∈strictA D)).card
      rw [card_preimage_label]
      exact lR.1
    · change 2≤(univ.filter (fun i : I16=>e i∈strictB D)).card
      rw [card_preimage_label]
      exact lR.2
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
      exact hiD _ (mem_sdiff.mp ((fD _).mp hz)).1
    · intro z hz
      rw [label_degree iso]
      exact hiD _ (mem_filter.mp (mem_inter.mp ((fK _).mp hz)).1).1
  apply traceable_label iso
  apply Singleton16.traceable_of_normalized_singleton_at_most_two_balanced frame (iso.connected_iff.mpr hc)
  intro z
  rw [label_even iso hc]
  exact even _

#print axioms traceable_of_adjacent_singleton_thirteen_unique_at_most_two_balanced
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
