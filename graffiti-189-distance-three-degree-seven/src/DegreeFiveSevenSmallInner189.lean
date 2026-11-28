import DegreeFiveFarSlotDegrees189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private not_common from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem count_high_subset_of_one_low (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (U : Finset V) : U.card≤(U.filter (fun x=>5≤G.degree x)).card+1 := by
  classical
  let H := U.filter (fun x=>5≤G.degree x)
  have s : H⊆U := filter_subset _ _
  have n : (U\H).card≤1 := by
    apply Classical.byContradiction
    intro h
    obtain ⟨x,xu,y,yu,xy⟩ := one_lt_card.mp (show 1<(U\H).card by omega)
    obtain ⟨xU,xH⟩ := mem_sdiff.mp xu
    obtain ⟨yU,yH⟩ := mem_sdiff.mp yu
    exact (degree x y xy).elim
      (fun f=>xH (mem_filter.mpr ⟨xU,f⟩)) (fun f=>yH (mem_filter.mpr ⟨yU,f⟩))
  have m := card_sdiff_add_card_eq_card s
  change U.card≤H.card+1
  omega

theorem four_a_no_bridge_small_inner_free (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (a4 : S.localA.card=4) (foreign : S.foreignA.card=3)
    (b4 : (S.L.filter (G.Adj b)).card≤4) (i2 : (farNonports S.L a b G).card≤2)
    (big : 9≤S.L.card) (noBridge : ¬portBridge S)
    (visible : farNonports S.L a b G⊆secondA G S.L a) :
    ∃ u v,G.Adj a u ∧ RouteOn G S.L u v := by
  classical
  let A := S.localA
  let B := S.L.filter (G.Adj b)
  let I := farNonports S.L a b G
  let H := B.filter (fun v=>5≤G.degree v)
  have hB : H⊆B := filter_subset _ _
  have bL : B⊆S.L := filter_subset _ _
  have iL : I⊆S.L := filter_subset _ _
  have aL : A⊆S.L := filter_subset _ _
  have sep : Disjoint A B := disjoint_left.mpr
    (fun x xa xb=>not_common far (mem_filter.mp xa).2 (mem_filter.mp xb).2)
  have n : A.card+B.card+I.card=S.L.card := left_port_count S far
  change A.card=4 at a4
  change B.card≤4 at b4
  change I.card≤2 at i2
  have b3 : 3≤B.card := by omega
  have i1 : 1≤I.card := by omega
  have Hn : B.card≤H.card+1 := count_high_subset_of_one_low degree B
  have H2 : 2≤H.card := by omega
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
  have core : I.card=2 := by
    by_cases h : I.card=2
    · exact h
    have c : I.card=1 := by omega
    obtain ⟨i,eq⟩ := card_eq_one.mp c
    have ii : i∈I := by simp [eq]
    obtain ⟨p,pa,pi⟩ := hitA i ii
    have co := charges p pa (hB.trans bL) (allB p pa (fun j ji=>by
      have e : j=i := by simpa [eq] using ji
      exact e.symm ▸ pi))
    omega
  obtain ⟨r,s,rs,eqI⟩ := card_eq_two.mp core
  have rr : r∈I := by simp [eqI]
  have ss : s∈I := by simp [eqI]
  have aClique : CompleteOn G A := by
    intro p pa q qa pq
    apply Classical.byContradiction
    intro noP
    have use (p q : V) (pa : p∈A) (qa : q∈A) (pq : p≠q) (noP : ¬G.Adj p q)
        (hp : 5≤G.degree p) : False := by
      have n := far_port_nonport_degree_lower_of_missing_peer pa qa pq.symm noP (aPorts p pa)
      have eq : I.filter (G.Adj p)=I := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
      have all := allB p pa (fun z zi=>(mem_filter.mp (eq.symm ▸ zi)).2)
      have q2 := d2 hc pq noP (mem_filter.mp pa).2.symm (mem_filter.mp qa).2
      have qOff : q∉H := fun t=>disjoint_left.mp sep qa (hB t)
      have k := charges p pa (insert_subset_iff.mpr ⟨aL qa,hB.trans bL⟩)
        (insert_subset_iff.mpr ⟨q2,all⟩)
      rw [card_insert_of_not_mem qOff] at k
      omega
    exact (degree p q pq).elim (use p q pa qa pq noP) (use q p qa pa pq.symm (fun e=>noP e.symm))
  have bb : B.card=3 := by
    by_cases h : B.card=3
    · exact h
    have B4 : B.card=4 := by omega
    have H3 : 3≤H.card := by omega
    have notBoth (p : V) (pa : p∈A) (pr : G.Adj p r) (ps : G.Adj p s) : False := by
      have z := charges p pa (hB.trans bL) (allB p pa (fun i ii=>by
        have e : i=r ∨ i=s := by simpa [eqI] using ii
        exact e.elim (fun h=>h.symm ▸ pr) (fun h=>h.symm ▸ ps)))
      omega
    have per (u v : V) (ui : u∈I) (vi : v∈I) (uv : u≠v) :
        (B.filter (G.Adj u)).card≤1 := by
      obtain ⟨p,pa,pu⟩ := hitA u ui
      obtain ⟨q,qa,qv⟩ := hitA v vi
      have pv : ¬G.Adj p v := by
        intro pv
        have ucases : u=r ∨ u=s := by simpa [eqI] using ui
        have vcases : v=r ∨ v=s := by simpa [eqI] using vi
        rcases ucases with u'|u' <;> rcases vcases with v'|v'
        · exact uv (u'.trans v'.symm)
        · exact notBoth p pa (u' ▸ pu) (v' ▸ pv)
        · exact notBoth p pa (v' ▸ pv) (u' ▸ pu)
        exact uv (u'.trans v'.symm)
      have pq : p≠q := fun e=>pv (e.symm ▸ qv)
      have pnv : p≠v := fun e=>(mem_filter.mp vi).2.1 (e ▸ (mem_filter.mp pa).2)
      have v2 := d2 hc pnv pv (aClique p pa q qa pq) qv
      let X := B.filter (G.Adj u)
      have sub : X⊆DistanceTwo G p := by
        intro t tx
        obtain ⟨tb,ut⟩ := mem_filter.mp tx
        exact d2 hc (fun e=>disjoint_left.mp sep (e ▸ pa) tb) (no p pa t tb) pu ut
      have off : v∉X := fun m=>(mem_filter.mp vi).2.2 (mem_filter.mp (mem_filter.mp m).1).2
      have c := charges p pa (insert_subset_iff.mpr ⟨iL vi,(filter_subset _ _).trans bL⟩)
        (insert_subset_iff.mpr ⟨v2,sub⟩)
      rw [card_insert_of_not_mem off] at c
      change X.card≤1
      omega
    have cr := per r s rr ss rs
    have cs := per s r ss rr rs.symm
    have hs : H⊆(B.filter (G.Adj r))∪(B.filter (G.Adj s)) := by
      intro v vh
      obtain ⟨u,ui,vu⟩ := hitB v vh
      have c : u=r ∨ u=s := by simpa [eqI] using ui
      exact c.elim
        (fun e=>mem_union_left _ (mem_filter.mpr ⟨hB vh,e ▸ vu.symm⟩))
        (fun e=>mem_union_right _ (mem_filter.mpr ⟨hB vh,e ▸ vu.symm⟩))
    have z := (card_le_card hs).trans (card_union_le _ _)
    omega
  have bFull (q : V) (qh : q∈H) :
      (∀ v∈B,q≠v → G.Adj q v) ∧ ∀ i∈I,G.Adj q i := by
    obtain ⟨qb,q5⟩ := mem_filter.mp qh
    exact far_port_full_at_tight_pool qb (bPorts q qb) (by omega) q5
  have bClique : CompleteOn G B := fun q qb v vb qv=>(degree q v qv).elim
    (fun h=>(bFull q (mem_filter.mpr ⟨qb,h⟩)).1 v vb qv)
    (fun h=>((bFull v (mem_filter.mpr ⟨vb,h⟩)).1 q qb qv.symm).symm)
  have aFull (p : V) (pa : p∈A) (v : V) (vi : v∈I) : G.Adj p v := by
    have p2 (i : V) (ii : i∈I) (pi : G.Adj p i) : H⊆DistanceTwo G p := by
      intro q qh
      have qb := hB qh
      exact d2 hc (fun e=>disjoint_left.mp sep (e ▸ pa) qb) (no p pa q qb)
        pi ((bFull q qh).2 i ii).symm
    apply Classical.byContradiction
    intro pv
    have eq : I.filter (G.Adj p)=∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro i h
      obtain ⟨ii,pi⟩ := mem_filter.mp h
      obtain ⟨q,qa,qv⟩ := hitA v vi
      have pq : p≠q := fun e=>pv (e.symm ▸ qv)
      have ne : p≠v := fun e=>(mem_filter.mp vi).2.1 (e ▸ (mem_filter.mp pa).2)
      have v2 := d2 hc ne pv (aClique p pa q qa pq) qv
      have off : v∉H := fun m=>(mem_filter.mp vi).2.2 (mem_filter.mp (hB m)).2
      have z := charges p pa (insert_subset_iff.mpr ⟨iL vi,hB.trans bL⟩)
        (insert_subset_iff.mpr ⟨v2,p2 i ii pi⟩)
      rw [card_insert_of_not_mem off] at z
      omega
    have pLow : ¬5≤G.degree p := by
      have z := far_port_nonport_degree_lower pa (aPorts p pa)
      rw [eq,card_empty] at z
      omega
    have hEq : H=B := eq_of_subset_of_card_le hB (by
      have sub : B⊆H := by
        intro q qb
        have ne : p≠q := fun e=>disjoint_left.mp sep (e ▸ pa) qb
        exact mem_filter.mpr ⟨qb,(degree p q ne).resolve_left pLow⟩
      exact card_le_card sub)
    obtain ⟨q,qa,qr⟩ := hitA r rr
    have hit : H⊆DistanceTwo G q := by
      intro w wh
      have wb := hB wh
      exact d2 hc (fun e=>disjoint_left.mp sep (e ▸ qa) wb) (no q qa w wb)
        qr ((bFull w wh).2 r rr).symm
    have z := charges q qa (hB.trans bL) hit
    rw [hEq] at z
    omega
  have disAI : Disjoint A I := disjoint_left.mpr
    (fun w wa wi=>(mem_filter.mp wi).2.1 (mem_filter.mp wa).2)
  have disIB : Disjoint I B := disjoint_left.mpr
    (fun w wi wb=>(mem_filter.mp wi).2.2 (mem_filter.mp wb).2)
  obtain ⟨x,xL,ax⟩ := S.leftA
  have xA : x∈A := mem_filter.mpr ⟨xL,ax⟩
  obtain ⟨p,pa,route⟩ := route_clique_join_end_leaf disAI aClique
    (fun p pa i ii=>aFull p pa i (mem_erase.mp ii).2) (show I.card≤A.card by omega) xA rr (aFull x xA r rr)
  obtain ⟨q,qh⟩ := card_pos.mp (show 0<H.card by omega)
  obtain ⟨v,path,pth,supp⟩ := rooted_path_in_clique B bClique (hB qh)
  have qb : RouteOn G B q v := ⟨path,pth,supp⟩
  have main := route.join qb (disjoint_union_left.mpr ⟨sep,disIB⟩) ((bFull q qh).2 r rr).symm
  have sum : (A∪I)∪B=S.L := by
    rw [union_right_comm]
    exact left_port_partition S far
  exact ⟨p,v,(mem_filter.mp pa).2,sum ▸ main⟩

#print axioms four_a_no_bridge_small_inner_free
end Graffiti189LongestPath.CrossSaturation.Split.Five
