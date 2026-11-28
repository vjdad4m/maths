import DegreeFiveSevenSmallInner189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private left_boundary from AdjacentCut189
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

/-- Geometry of the order-three inner pool of a nonbridge four-A shore. -/
theorem four_a_no_bridge_three_inner_geometry (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (a4 : S.localA.card=4) (foreign : S.foreignA.card=3)
    (b4 : (S.L.filter (G.Adj b)).card≤4) (i3 : (farNonports S.L a b G).card=3)
    (big : 9≤S.L.card) (noBridge : ¬portBridge S)
    (visible : farNonports S.L a b G⊆secondA G S.L a)
    (bcap : (secondA G S.L b).card≤2) :
    let A := S.localA
    let B := S.L.filter (G.Adj b)
    let I := farNonports S.L a b G
    B.card=3 ∧ CompleteOn G A ∧ CompleteOn G B ∧
      ∃ i j k : V,i≠j ∧ i≠k ∧ j≠k ∧ I={i,j,k} ∧
      (∀ p∈A,G.Adj p k) ∧
      (∀ p∈A,G.Adj p i ↔ G.Adj p j) ∧
      (∃ p∈A,G.Adj p i) ∧
      (∃ r∈B,G.Adj j r) ∧
      ((A.filter (fun p=>G.Adj p i)).card=1 → G.Adj i j) := by
  classical
  dsimp only
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let I := farNonports S.L a b G
  let H := B.filter (fun v=>5≤G.degree v)
  let C := I.filter (fun t=>∃ q∈B,G.Adj t q)
  have hB : H⊆B := filter_subset _ _
  have bL : B⊆S.L := filter_subset _ _
  have iL : I⊆S.L := filter_subset _ _
  have aL : A⊆S.L := filter_subset _ _
  have cI : C⊆I := filter_subset _ _
  have sep : Disjoint A B := disjoint_left.mpr
    (fun x xa xb=>not_common far (mem_filter.mp xa).2 (mem_filter.mp xb).2)
  have n : A.card+B.card+I.card=S.L.card := left_port_count S far
  change A.card=4 at a4
  change B.card≤4 at b4
  change I.card=3 at i3
  have b2 : 2≤B.card := by omega
  have Hn : B.card≤H.card+1 := count_high_subset_of_one_low degree B
  have no (p : V) (pa : p∈A) (q : V) (qb : q∈B) : ¬G.Adj p q :=
    distance_two_charge_from_no_bridge S pa qb noBridge
  have aPorts (p : V) (pa : p∈A) :
      G.neighborFinset p⊆insert a ((A.erase p)∪I) :=
    bounds_of_local_color_port S far pa (no p pa)
  have ibSwap : farNonports S.flip.L b a G=I := by
    ext z
    simp [I,farNonports,and_comm,and_left_comm,and_assoc,Split.flip]
  have bPorts (q : V) (qb : q∈B) :
      G.neighborFinset q⊆insert b ((B.erase q)∪I) := by
    have fd : 3≤G.dist b a := by rwa [dist_comm]
    have step := bounds_of_local_color_port S.flip fd (show q∈S.flip.localA from qb)
      (fun p pp h=>no p pp q qb h.symm)
    change G.neighborFinset q⊆insert b ((B.erase q)∪farNonports S.flip.L b a G) at step
    rwa [ibSwap] at step
  have hitB (q : V) (qh : q∈H) : ∃ i∈I,G.Adj q i := by
    obtain ⟨qb,hi⟩ := mem_filter.mp qh
    have x := far_port_nonport_degree_lower qb (bPorts q qb)
    obtain ⟨i,ii⟩ := card_pos.mp (show 0<(I.filter (G.Adj q)).card by omega)
    exact ⟨i,(mem_filter.mp ii).1,(mem_filter.mp ii).2⟩
  have hitA (i : V) (ii : i∈I) : ∃ p∈A,G.Adj p i :=
    nonport_a_neighbor S hc far (iL ii) (mem_inter.mp (visible ii)).2
  have allB (p : V) (pa : p∈A) (links : ∀ i∈I,G.Adj p i) :
      H⊆DistanceTwo G p := by
    intro q qh
    obtain ⟨i,ii,qi⟩ := hitB q qh
    obtain ⟨pl,ap⟩ := mem_filter.mp pa
    have qb : q∈B := hB qh
    have nq : p≠q := fun e=>disjoint_left.mp sep (e ▸ pa) qb
    exact d2 hc nq (no p pa q qb) (links i ii) qi.symm
  have charges (p : V) (pa : p∈A) {W : Finset V} (loc : W⊆S.L)
      (all : W⊆DistanceTwo G p) : W.card≤2 :=
    local_distance_two_at_foreign_three S hc even foreign (aL pa) (mem_filter.mp pa).2
      (fun _ w=>mem_insert_of_mem (loc w)) all
  have cb : C⊆secondA G S.L b := by
    intro v vc
    obtain ⟨vi,q,qb,vq⟩ := mem_filter.mp vc
    have bv := (mem_filter.mp vi).2.2
    have ne : b≠v := fun h=>S.leftOff.2 (h.symm ▸ iL vi)
    exact mem_inter.mpr ⟨iL vi,d2 hc ne bv (mem_filter.mp qb).2 vq.symm⟩
  have c2 : C.card≤2 := (card_le_card cb).trans bcap
  have bBound (q : V) (qb : q∈B) :
      G.neighborFinset q⊆insert b ((B.erase q)∪C) := by
    intro v vn
    rcases mem_insert.mp (bPorts q qb vn) with e|h
    · exact mem_insert.mpr (.inl e)
    rcases mem_union.mp h with e|vi
    · exact mem_insert_of_mem (mem_union_left _ e)
    exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr
      ⟨vi,q,qb,((mem_neighborFinset G q v).mp vn).symm⟩))
  have ng : 3≤B.card := by
    obtain ⟨q,qh⟩ := card_pos.mp (show 0<H.card by omega)
    have bnd := far_port_nonport_degree_lower (hB qh) (bBound q (hB qh))
    have m := card_le_card (show C.filter (G.Adj q)⊆C from filter_subset _ _)
    have hi := (mem_filter.mp qh).2
    omega
  have h2 : 2≤H.card := by omega
  have good (p : V) (pa : p∈A) (v : V) (vi : v∈I) (pv : G.Adj p v) :
      B.filter (G.Adj v)⊆DistanceTwo G p := by
    intro x xxx
    obtain ⟨xb,vx⟩ := mem_filter.mp xxx
    exact d2 hc (fun e=>disjoint_left.mp sep (e ▸ pa) xb)
      (no p pa x xb) pv vx
  have full (p : V) (pa : p∈A) {W : Finset V} (W2 : W.card=2)
      (wB : W⊆B) (wd : W⊆DistanceTwo G p) :
      (∀ q∈A,p≠q → G.Adj p q) ∧ (∀ q∈I,G.Adj p q) :=
    two_charges_force_full_on_a_and_nonports S hc far even foreign visible pa W2
      (fun _ h=>mem_insert_of_mem (wB h)) wd
  have b3 : B.card=3 := by
    by_cases e : B.card=3
    · exact e
    have size : B.card=4 := by omega
    have many : 3≤H.card := by omega
    have noMany (v : V) (vi : v∈I) : (B.filter (G.Adj v)).card≤1 := by
      apply Classical.byContradiction
      intro h
      obtain ⟨p,pa,pv⟩ := hitA v vi
      obtain ⟨u,uu,w,ww,uw⟩ := one_lt_card.mp (show 1<(B.filter (G.Adj v)).card by omega)
      have ob : ({u,w} : Finset V)⊆B :=
        insert_subset_iff.mpr ⟨(mem_filter.mp uu).1,singleton_subset_iff.mpr (mem_filter.mp ww).1⟩
      have d := good p pa v vi pv
      have t : ({u,w} : Finset V)⊆DistanceTwo G p :=
        insert_subset_iff.mpr ⟨d uu,singleton_subset_iff.mpr (d ww)⟩
      have f := full p pa (show ({u,w} : Finset V).card=2 by simp [uw]) ob t
      have z := charges p pa (hB.trans bL) (allB p pa f.2)
      omega
    have cs (q : V) (qh : q∈H) : ∃ v∈C,G.Adj q v := by
      obtain ⟨v,vi,qv⟩ := hitB q qh
      exact ⟨v,mem_filter.mpr ⟨vi,q,hB qh,qv.symm⟩,qv⟩
    obtain ⟨q,qq⟩ := card_pos.mp (show 0<H.card by omega)
    obtain ⟨v,vc,qv⟩ := cs q qq
    by_cases c1 : C.card=1
    · obtain ⟨w,eq⟩ := card_eq_one.mp c1
      have wi : w∈I := cI (by simp [eq])
      have sub : H⊆B.filter (G.Adj w) := by
        intro q qh
        obtain ⟨v,vc,qv⟩ := cs q qh
        have e : v=w := by simpa [eq] using vc
        exact mem_filter.mpr ⟨hB qh,e ▸ qv.symm⟩
      have bound := (card_le_card sub).trans (noMany w wi)
      omega
    have m := card_pos.mpr ⟨v,vc⟩
    obtain ⟨x,y,xy,eq⟩ := card_eq_two.mp (show C.card=2 by omega)
    have xi : x∈I := cI (by simp [eq])
    have yi : y∈I := cI (by simp [eq])
    have om : H⊆(B.filter (G.Adj x))∪(B.filter (G.Adj y)) := by
      intro q qh
      obtain ⟨r,rc,qr⟩ := cs q qh
      have t : r=x ∨ r=y := by simpa [eq] using rc
      exact t.elim
        (fun e=>mem_union_left _ (mem_filter.mpr ⟨hB qh,e ▸ qr.symm⟩))
        (fun e=>mem_union_right _ (mem_filter.mpr ⟨hB qh,e ▸ qr.symm⟩))
    have nx := noMany x xi
    have ny := noMany y yi
    have bound := (card_le_card om).trans (card_union_le _ _)
    omega
  have fullB (q : V) (qh : q∈H) :
      (∀ p∈B,q≠p → G.Adj q p) ∧ ∀ t∈C,G.Adj q t := by
    have h := (mem_filter.mp qh).2
    have n := far_port_nonport_degree_lower (hB qh) (bBound q (hB qh))
    have f := card_le_card (show C.filter (G.Adj q)⊆C from filter_subset _ _)
    exact far_port_full_at_tight_pool (hB qh) (bBound q (hB qh)) (by omega) h
  obtain ⟨q,qh⟩ := card_pos.mp (show 0<H.card by omega)
  have f := far_port_nonport_degree_lower (hB qh) (bBound q (hB qh))
  have g := card_le_card (show C.filter (G.Adj q)⊆C from filter_subset _ _)
  have q5 := (mem_filter.mp qh).2
  obtain ⟨i,j,ij,IJ⟩ := card_eq_two.mp (show C.card=2 by omega)
  have ic : i∈C := by simp [IJ]
  have jc : j∈C := by simp [IJ]
  have ii : i∈I := cI ic
  have ji : j∈I := cI jc
  have haves : ∀ p∈A,∀ t∈C,G.Adj p t → H⊆DistanceTwo G p := by
    intro p pa t tc pt r rh
    exact good p pa t (cI tc) pt (mem_filter.mpr ⟨hB rh,((fullB r rh).2 t tc).symm⟩)
  obtain ⟨p,pa,pi⟩ := hitA i ii
  have hcap : H.card=2 := by
    have n := charges p pa (hB.trans bL) (haves p pa i ic pi)
    omega
  have hfull (p : V) (pa : p∈A) (v : V) (vc : v∈C) (pv : G.Adj p v) :
      (∀ r∈A,p≠r → G.Adj p r) ∧ ∀ w∈I,G.Adj p w :=
    full p pa hcap hB (haves p pa v vc pv)
  have activeAdj (p : V) (pa : p∈A) : G.Adj p i ↔ G.Adj p j :=
    ⟨fun e=>(hfull p pa i ic e).2 j ji,fun e=>(hfull p pa j jc e).2 i ii⟩
  have bcl : CompleteOn G B := fun u ub v vb uv=>(degree u v uv).elim
    (fun h=>(fullB u (mem_filter.mpr ⟨ub,h⟩)).1 v vb uv)
    (fun h=>((fullB v (mem_filter.mpr ⟨vb,h⟩)).1 u ub uv.symm).symm)
  have partialA (u : V) (ua : u∈A) (no : ¬G.Adj u i) :
      (∀ r∈A,u≠r → G.Adj u r) := by
    have uj : ¬G.Adj u j := fun e=>no ((activeAdj u ua).mpr e)
    have up : u≠p := fun e=>no (e.symm ▸ pi)
    have pu := (hfull p pa i ic pi).1 u ua up.symm
    have ui : u≠i := fun e=>(mem_filter.mp ii).2.1 (e ▸ (mem_filter.mp ua).2)
    have uj' : u≠j := fun e=>(mem_filter.mp ji).2.1 (e ▸ (mem_filter.mp ua).2)
    have i2 := d2 hc ui no pu.symm pi
    have j2 := d2 hc uj' uj pu.symm ((activeAdj p pa).mp pi)
    intro v va uv
    apply Classical.byContradiction
    intro uvn
    have v2 := d2 hc uv uvn (mem_filter.mp ua).2.symm (mem_filter.mp va).2
    have vi : v≠i := fun e=>(mem_filter.mp ii).2.1 (e ▸ (mem_filter.mp va).2)
    have vj : v≠j := fun e=>(mem_filter.mp ji).2.1 (e ▸ (mem_filter.mp va).2)
    let W : Finset V := {v,i,j}
    have w : W⊆S.L := insert_subset_iff.mpr ⟨aL va,insert_subset_iff.mpr ⟨iL ii,singleton_subset_iff.mpr (iL ji)⟩⟩
    have d : W⊆DistanceTwo G u := insert_subset_iff.mpr ⟨v2,insert_subset_iff.mpr ⟨i2,singleton_subset_iff.mpr j2⟩⟩
    have n := charges u ua w d
    have c : W.card=3 := by simp [W,vi,vj,ij]
    omega
  have acl : CompleteOn G A := by
    intro u ua v va uv
    by_cases e : G.Adj u i
    · exact (hfull u ua i ic e).1 v va uv
    exact partialA u ua e v va uv
  have existsLow : ∃ l∈B,l∉H := by
    have s := card_sdiff_add_card_eq_card hB
    obtain ⟨l,ll⟩ := card_pos.mp (show 0<(B\H).card by omega)
    exact ⟨l,(mem_sdiff.mp ll).1,(mem_sdiff.mp ll).2⟩
  obtain ⟨l,lb,lh⟩ := existsLow
  have lowL : ¬5≤G.degree l := fun e=>lh (mem_filter.mpr ⟨lb,e⟩)
  have aHigh (u : V) (ua : u∈A) : 5≤G.degree u :=
    (degree u l (fun e=>disjoint_left.mp sep (e ▸ ua) lb)).resolve_right lowL
  have iHigh (u : V) (ui : u∈I) : 5≤G.degree u :=
    (degree u l (fun e=>(mem_filter.mp ui).2.2 (e.symm ▸ (mem_filter.mp lb).2))).resolve_right lowL
  have lowNo (t : V) (ti : t∈C) : ¬G.Adj t l := by
    intro tl
    obtain ⟨u,ua,ut⟩ := hitA t (cI ti)
    have hit := haves u ua t ti ut
    have extra := good u ua t (cI ti) ut (mem_filter.mpr ⟨lb,tl⟩)
    have all := charges u ua (insert_subset_iff.mpr ⟨bL lb,hB.trans bL⟩)
      (insert_subset_iff.mpr ⟨extra,hit⟩)
    rw [card_insert_of_not_mem lh,hcap] at all
    omega
  obtain ⟨k,kk⟩ := card_pos.mp (show 0<(I\C).card by
    have z := card_sdiff_add_card_eq_card cI
    have c : C.card=2 := by simp [IJ,ij]
    omega)
  obtain ⟨ki,kc⟩ := mem_sdiff.mp kk
  have ik : i≠k := fun e=>kc (e ▸ ic)
  have jk : j≠k := fun e=>kc (e ▸ jc)
  have eqI : I={i,j,k} := (eq_of_subset_of_card_le
    (insert_subset_iff.mpr ⟨ii,insert_subset_iff.mpr ⟨ji,singleton_subset_iff.mpr ki⟩⟩)
    (by rw [i3]; simp [ij,ik,jk])).symm
  have allK (u : V) (ua : u∈A) : G.Adj u k := by
    by_cases f : G.Adj u i
    · exact (hfull u ua i ic f).2 k ki
    have nj : ¬G.Adj u j := fun e=>f ((activeAdj u ua).mpr e)
    have n := far_port_nonport_degree_lower ua (aPorts u ua)
    have sub : I.filter (G.Adj u)⊆{k} := by
      intro v h
      obtain ⟨vi,uv⟩ := mem_filter.mp h
      have e : v=i ∨ v=j ∨ v=k := by simpa [eqI] using vi
      rcases e with e|e|e
      · exact (f (e ▸ uv)).elim
      · exact (nj (e ▸ uv)).elim
      exact mem_singleton.mpr e
    have z := card_le_card sub
    rw [card_singleton] at z
    have upper := aHigh u ua
    apply Classical.byContradiction
    intro uk
    have empty : I.filter (G.Adj u)=∅ := Finset.eq_empty_iff_forall_not_mem.mpr
      (fun v h=>uk ((mem_singleton.mp (sub h)) ▸ (mem_filter.mp h).2))
    rw [empty,card_empty] at n
    omega
  have edgeIf (one : (A.filter (fun u=>G.Adj u i)).card=1) : G.Adj i j := by
    obtain ⟨u,eq⟩ := card_eq_one.mp one
    have ue : u=p := by
      have no : p∈A.filter (fun v=>G.Adj v i) := mem_filter.mpr ⟨pa,pi⟩
      have n : p=u := by simpa [eq] using no
      exact n.symm
    apply Classical.byContradiction
    intro edge
    have sub : G.neighborFinset i⊆insert p (insert k H) := by
      intro v vv
      have iv := (mem_neighborFinset G i v).mp vv
      rcases left_boundary S i (iL ii) v iv with e|e|vl
      · exact ((mem_filter.mp ii).2.1 (e ▸ iv.symm)).elim
      · exact ((mem_filter.mp ii).2.2 (e ▸ iv.symm)).elim
      have e : v∈A ∨ v∈B ∨ v∈I := by
        have c := left_port_partition S far
        rw [←c] at vl
        rcases mem_union.mp vl with h|h
        · exact (mem_union.mp h).imp id Or.inl
        exact .inr (.inr h)
      rcases e with va|vb|vi
      · have n : v∈A.filter (fun u=>G.Adj u i) := mem_filter.mpr ⟨va,iv.symm⟩
        have z : v=u := by simpa [eq] using n
        exact mem_insert.mpr (.inl (z.trans ue))
      · have vh : v∈H := by
          have ne : v≠l := fun e=>lowNo i ic (e ▸ iv)
          exact mem_filter.mpr ⟨vb,(degree v l ne).resolve_right lowL⟩
        exact mem_insert_of_mem (mem_insert_of_mem vh)
      have e : v=i ∨ v=j ∨ v=k := by simpa [eqI] using vi
      rcases e with h|h|h
      · exact (iv.ne h.symm).elim
      · exact (edge (h ▸ iv)).elim
      exact mem_insert_of_mem (mem_insert.mpr (.inl h))
    have n := (card_le_card sub).trans (card_insert_le p (insert k H))
    have m := card_insert_le k H
    rw [card_neighborFinset_eq_degree] at n
    have h := iHigh i ii
    omega
  change B.card=3 ∧ CompleteOn G A ∧ CompleteOn G B ∧ _
  exact ⟨b3,acl,bcl,i,j,k,ij,ik,jk,eqI,allK,activeAdj,⟨p,pa,pi⟩,
    ⟨q,hB qh,((fullB q qh).2 j jc).symm⟩,edgeIf⟩

#print axioms four_a_no_bridge_three_inner_geometry
end Graffiti189LongestPath.CrossSaturation.Split.Five
