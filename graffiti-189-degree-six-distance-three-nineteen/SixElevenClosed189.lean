import SixElevenPartition189
import SixElevenArithmetic189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_disjoint shore_off shore_closed from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far from SixDistanceThreeShort189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}

/-- A distance-three separating pair at threshold six cannot have
shores of orders six and eleven. -/
theorem no_six_eleven_shores (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ u,(EvenFrom G u).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (six : (Shore C).card=6) (eleven : (Shore D).card=11) : False := by
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
  have eleven' : (Shore (swapCut D)).card=11 := by rwa [shore_swapCut]
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
      (E 4).card+(E 5).card+(E 6).card+(E 7).card=low.card := sixBuckets_card a b low
  have nSum : (N 0).card+(N 1).card+(N 2).card+(N 3).card+
      (N 4).card+(N 5).card+(N 6).card+(N 7).card=11 := (sixBuckets_card a b (Shore D)).trans eleven
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
  let R := Shore D \ (qa∪qb)
  have dr : R.card+qa.card+qb.card=11 := by
    have h := card_sdiff_add_card_eq_card spanQ
    rw [card_union_of_disjoint qdis,eleven] at h
    change R.card+(qa.card+qb.card)=11 at h
    omega
  have r5 : R.card≤5 := by have qa := ta.2.2.2; have qb := tb.2.2.2; omega
  have allDarkLow : N 7⊆E 7 := by
    intro u um
    obtain ⟨ud,ua,ub,da,db⟩ := dat 7 um
    have ur : u∈R := mem_sdiff.mpr ⟨ud,fun h=>(mem_union.mp h).elim
      (fun h=>ua (mem_filter.mp h).2) (fun h=>ub (mem_filter.mp h).2)⟩
    have sub : G.neighborFinset u⊆R.erase u := by
      intro v vv
      have uv := (G.mem_neighborFinset _ _).mp vv
      rcases shore_closed D u ud v uv with rfl|rfl|vd
      · exact (ua uv.symm).elim
      · exact (ub uv.symm).elim
      refine mem_erase.mpr ⟨uv.ne.symm,mem_sdiff.mpr ⟨vd,?_⟩⟩
      intro inP
      rcases mem_union.mp inP with av|bv
      · have una : u≠a := fun e=>(shore_off D).1 (e ▸ ud)
        have visible := visible_of_adj_port (S:=Shore D) hc una
          ud (mem_filter.mp av).2 uv.symm ua
        exact da (mem_cutSeen.mp visible).2
      · have unb : u≠b := fun e=>(shore_off D).2 (e ▸ ud)
        have visible := visible_of_adj_port (S:=Shore D) hc unb
          ud (mem_filter.mp bv).2 uv.symm ub
        exact db (mem_cutSeen.mp visible).2
    have dn := card_le_card sub
    rw [G.card_neighborFinset_eq_degree,card_erase_of_mem ur] at dn
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨ud,by omega⟩,(mem_filter.mp um).2⟩
  have visibleNE {S : Finset V} {r u v : V}
      (vs : v∈S) (vr : v≠r) (ru : G.Adj r u) (nov : ¬G.Adj r v)
      (not2 : G.dist r v≠2) : ¬G.Adj u v :=
    fun uv=>not2 (mem_cutSeen.mp (visible_of_adj_port hc vr vs ru uv nov)).2
  have budgetA {u : V} (ud : u∈Shore D) (au : G.Adj a u) (uh : 6≤G.degree u)
      (B T : Finset V) (loc : ∀ v∈B,v∈Shore D ∧ 6≤G.degree v ∧ v≠u ∧ ¬G.Adj u v)
      (tc : Disjoint T (Shore C)) (td : Disjoint T (Shore D)) (t2 : T⊆DistanceTwo G u) :
      pa.card+B.card+T.card≤6 :=
    port_even_eleven hc far even cd eleven ud au uh B T loc tc td t2
  have budgetB {u : V} (ud : u∈Shore D) (bu : G.Adj b u) (uh : 6≤G.degree u)
      (B T : Finset V) (loc : ∀ v∈B,v∈Shore D ∧ 6≤G.degree v ∧ v≠u ∧ ¬G.Adj u v)
      (tc : Disjoint T (Shore C)) (td : Disjoint T (Shore D)) (t2 : T⊆DistanceTwo G u) :
      pb.card+B.card+T.card≤6 := by
    have ud' : u∈Shore (swapCut D) := by rwa [shore_swapCut]
    have loc' : ∀ v∈B,v∈Shore (swapCut D) ∧ 6≤G.degree v ∧ v≠u ∧ ¬G.Adj u v := by
      simpa only [shore_swapCut] using loc
    simpa only [shore_swapCut] using (port_even_eleven hc far' even cd' eleven' ud' bu uh B T loc'
      (by rwa [shore_swapCut]) (by rwa [shore_swapCut]) t2)
  have cardForeignA : (H 2∪H 3).card=(H 2).card+(H 3).card :=
    card_union_of_disjoint (sixBuckets_disjoint a b _ _ (by decide : (2:Fin 8)≠3))
  have foreignA {z : V} (zh : z∈H 2∪H 3) : z∈Shore D ∧ 6≤G.degree z ∧ G.Adj b z := by
    rcases mem_union.mp zh with z|z
    · obtain ⟨zd,zg,zu,_⟩ := highdat 2 z
      exact ⟨zd,zg,zu⟩
    · obtain ⟨zd,zg,zu,_⟩ := highdat 3 z
      exact ⟨zd,zg,zu⟩
  have plainA (live : (E 0).card<(N 0).card) :
      pa.card+(N 2).card+(N 3).card≤6+(E 2).card+(E 3).card := by
    obtain ⟨x,xd,xh,xu,not2⟩ := chooseHigh 0 live
    have nx : ¬G.Adj b x := fun h => no x ⟨xu,h⟩
    have xn : x≠b := fun e=>(shore_off D).2 (e ▸ xd)
    have s := budgetA xd xu xh (H 2∪H 3) ∅ (by
      intro z zh
      obtain ⟨zd,zh,zv⟩ := foreignA zh
      have neq : z≠x := fun e => nx (e ▸ zv)
      exact ⟨zd,zh,neq,fun h => visibleNE xd xn zv nx not2 h.symm⟩)
      (by simp) (by simp) (empty_subset _)
    rw [cardForeignA,card_empty] at s
    have k := hE 2
    have m := hE 3
    omega
  have seesA (live : (E 1).card<(N 1).card) :
      pa.card+1+(N 2).card≤6+(E 2).card := by
    obtain ⟨x,xd,xh,xu,seen⟩ := chooseHigh 1 live
    have ts : ({b}:Finset V)⊆DistanceTwo G x := by
      intro v vm
      rw [mem_singleton.mp vm]
      exact mem_filter.mpr ⟨mem_univ _,by rwa [dist_comm]⟩
    have c : Disjoint ({b}:Finset V) (Shore C) := by
      exact disjoint_left.mpr (fun v vt vc=>(shore_off C).2 ((mem_singleton.mp vt) ▸ vc))
    have e : Disjoint ({b}:Finset V) (Shore D) := by
      exact disjoint_left.mpr (fun v vt vd=>(shore_off D).2 ((mem_singleton.mp vt) ▸ vd))
    have s := budgetA xd xu xh (H 2) {b} (by
      intro z zh
      obtain ⟨zd,zh,zv,not2⟩ := highdat 2 zh
      have nz : ¬G.Adj a z := fun h => no z ⟨h,zv⟩
      have zn : z≠a := fun e => (shore_off D).1 (e ▸ zd)
      exact ⟨zd,zh,fun e=>nz (e.symm ▸ xu),visibleNE zd zn xu nz not2⟩) c e ts
    rw [card_singleton] at s
    have k := hE 2
    omega
  have onlyA (live : (E 4).card<(N 4).card) :
      pb.card+1+(N 2).card+(N 3).card≤6+(E 2).card+(E 3).card := by
    obtain ⟨x,xd,xh,xa,xb,yes,no⟩ := chooseHigh 4 live
    have ns : x∉cutSeen G (Shore D) b := fun h=>no (mem_cutSeen.mp h).2
    have vnx : b≠x := fun e => (shore_off D).2 (e.symm ▸ xd)
    have farX := unseen_nonport_dist_ge_three hc xd vnx xb ns
    have s := dark_one_even_eleven hc far ab conn even degree cd six eleven xd xh yes farX
      (H 2∪H 3) (fun _ h=>foreignA h)
    change pb.card+(H 2∪H 3).card+1≤6 at s
    rw [cardForeignA] at s
    have k := hE 2
    have m := hE 3
    omega
  have cardForeignB : (H 0∪H 1).card=(H 0).card+(H 1).card :=
    card_union_of_disjoint (sixBuckets_disjoint a b _ _ (by decide : (0:Fin 8)≠1))
  have foreignB {z : V} (zh : z∈H 0∪H 1) : z∈Shore D ∧ 6≤G.degree z ∧ G.Adj a z := by
    rcases mem_union.mp zh with z|z
    · obtain ⟨zd,zg,zu,_⟩ := highdat 0 z
      exact ⟨zd,zg,zu⟩
    · obtain ⟨zd,zg,zu,_⟩ := highdat 1 z
      exact ⟨zd,zg,zu⟩
  have plainB (live : (E 2).card<(N 2).card) :
      pb.card+(N 0).card+(N 1).card≤6+(E 0).card+(E 1).card := by
    obtain ⟨x,xd,xh,xu,not2⟩ := chooseHigh 2 live
    have nx : ¬G.Adj a x := fun h => no x ⟨h,xu⟩
    have xn : x≠a := fun e=>(shore_off D).1 (e ▸ xd)
    have s := budgetB xd xu xh (H 0∪H 1) ∅ (by
      intro z zh
      obtain ⟨zd,zh,zv⟩ := foreignB zh
      have neq : z≠x := fun e => nx (e ▸ zv)
      exact ⟨zd,zh,neq,fun h => visibleNE xd xn zv nx not2 h.symm⟩)
      (by simp) (by simp) (empty_subset _)
    rw [cardForeignB,card_empty] at s
    have k := hE 0
    have m := hE 1
    omega
  have seesB (live : (E 3).card<(N 3).card) :
      pb.card+1+(N 0).card≤6+(E 0).card := by
    obtain ⟨x,xd,xh,xu,seen⟩ := chooseHigh 3 live
    have ts : ({a}:Finset V)⊆DistanceTwo G x := by
      intro v vm
      rw [mem_singleton.mp vm]
      exact mem_filter.mpr ⟨mem_univ _,by rwa [dist_comm]⟩
    have c : Disjoint ({a}:Finset V) (Shore C) := by
      exact disjoint_left.mpr (fun v vt vc=>(shore_off C).1 ((mem_singleton.mp vt) ▸ vc))
    have e : Disjoint ({a}:Finset V) (Shore D) := by
      exact disjoint_left.mpr (fun v vt vd=>(shore_off D).1 ((mem_singleton.mp vt) ▸ vd))
    have s := budgetB xd xu xh (H 0) {a} (by
      intro z zh
      obtain ⟨zd,zh,zv,not2⟩ := highdat 0 zh
      have nz : ¬G.Adj b z := fun h => no z ⟨zv,h⟩
      have zn : z≠b := fun e => (shore_off D).2 (e ▸ zd)
      exact ⟨zd,zh,fun e=>nz (e.symm ▸ xu),visibleNE zd zn xu nz not2⟩) c e ts
    rw [card_singleton] at s
    have k := hE 0
    omega
  have onlyB (live : (E 5).card<(N 5).card) :
      pa.card+1+(N 0).card+(N 1).card≤6+(E 0).card+(E 1).card := by
    obtain ⟨x,xd,xh,xa,xb,no,yes⟩ := chooseHigh 5 live
    have ns : x∉cutSeen G (Shore D) a := fun h=>no (mem_cutSeen.mp h).2
    have vnx : a≠x := fun e => (shore_off D).1 (e.symm ▸ xd)
    have farX := unseen_nonport_dist_ge_three hc xd vnx xa ns
    have xd' : x∈Shore (swapCut D) := by rwa [shore_swapCut]
    have s : pa.card+(H 0∪H 1).card+1≤6 := by
      simpa only [shore_swapCut] using
        (dark_one_even_eleven hc far' ab.symm conn even degree cd' six' eleven' xd' xh yes farX
          (H 0∪H 1) (fun z zh=>by simpa only [shore_swapCut] using foreignB zh))
    rw [cardForeignB] at s
    have k := hE 0
    have m := hE 1
    omega
  have capA := ta.2.2.1
  have capB := tb.2.2.1
  have highA := ta.2.2.2
  have highB := tb.2.2.2
  rw [caEq] at capA highA
  rw [cbEq] at capB highB
  exact impossible_six_eleven_counts pa.card pb.card
    (N 0).card (N 1).card (N 2).card (N 3).card (N 4).card (N 5).card (N 6).card (N 7).card
    (E 0).card (E 1).card (E 2).card (E 3).card (E 4).card (E 5).card (E 6).card (E 7).card
    ta.1 tb.1 small (by omega) nSum capA capB (by omega) (by omega)
    aVis bVis (card_le_card allDarkLow) plainA plainB seesA seesB onlyA onlyB

#print axioms no_six_eleven_shores
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
