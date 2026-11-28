import SixTripleCutSingletonIsolate189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

open private Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark from SixTripleCutSingleton189

theorem Shore.foreign_visible_of_universal {S A B : Finset V}
    (sh : Shore G S A) (shB : Shore G S B) (dis : Disjoint A B) (hc : G.Connected)
    {x : V} (xm : x∈A) (un : ∀ t∈S,G.Adj x t) :
    visible G S B⊆DistanceTwo G x := by
  intro z zm
  obtain ⟨zb,t,ts,zt⟩ := mem_filter.mp zm
  have ne : x≠z := fun e=>disjoint_left.mp dis xm (e ▸ zb)
  have na : ¬G.Adj x z := fun a=>(sh.closed x xm z a).elim
    (fun za=>disjoint_left.mp dis za zb) (fun zs=>disjoint_left.mp shB.disjoint zb zs)
  exact two_of_common hc ne na (un t ts) zt.symm

theorem Shore.port_neighbor_cover {S A : Finset V}
    (sh : Shore G S A) (hc : G.Connected)
    {t x : V} (ts : t∈S) (xp : x∈ports G A t) :
    G.neighborFinset x⊆((ports G A t).erase x ∪ localTwo G A t) ∪ S := by
  intro y ym
  have xy := (G.mem_neighborFinset ..).mp ym
  rcases sh.closed x (mem_filter.mp xp).1 y xy with ya|ys
  · apply mem_union_left _
    by_cases ty : G.Adj t y
    · exact mem_union_left _ (mem_erase.mpr ⟨xy.ne.symm,mem_filter.mpr ⟨ya,ty⟩⟩)
    have yt : t≠y := fun e=>disjoint_left.mp sh.disjoint ya (e ▸ ts)
    exact mem_union_right _ (mem_inter.mpr ⟨ya,two_of_common hc yt ty (mem_filter.mp xp).2 xy⟩)
  · exact mem_union_right _ ys

theorem disjoint_ports_localTwo (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (t : V) :
    Disjoint (ports G A t) (localTwo G A t) := by
  apply disjoint_left.mpr
  intro z zp zq
  have a := dist_eq_one_iff_adj.mpr ((mem_filter.mp zp).2)
  have b : G.dist t z=2 := by simpa [DistanceTwo] using (mem_inter.mp zq).2
  omega

/-- A singleton shore is impossible in a three-component three-cut
having even one isolated terminal. The two mandatory universal ports
see four foreign vertices at distance two; the small local degree
budget gives at least three more at one of them. -/
theorem no_singleton_three_shores_of_isolated_terminal
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S A B : Finset V} (ss : S.card=3) {s t : V}
    (one : Shore G S ({s}:Finset V)) (shA : Shore G S A) (shB : Shore G S B)
    (sA : Disjoint ({s}:Finset V) A) (sB : Disjoint ({s}:Finset V) B) (ab : Disjoint A B)
    (ts : t∈S) (isolate : ∀ a∈S,a≠t → ¬G.Adj t a) : False := by
  classical
  obtain ⟨va,vb,da,_,cover,_⟩ := singleton_pin_dark_geometry hc cap conn degree ss one shA shB sA sB ab
  obtain ⟨⟨p2,q2,all⟩,_⟩ := singleton_three_shore_isolated_terminal hc cap conn degree ss one shA shB
    sA sB ab ts isolate
  let P := ports G A t
  let Q := localTwo G A t
  let D := dark G S A
  let M := visible G S A
  have p2' : P.card=2 := p2
  have q2' : Q.card=2 := q2
  have pm : P⊆M := fun x xp => mem_filter.mpr
    ⟨(mem_filter.mp xp).1,t,ts,(mem_filter.mp xp).2.symm⟩
  have w1 : (M\P).card=1 := by rw [card_sdiff pm,show M.card=3 from va,p2']
  obtain ⟨w,wEq⟩ := card_eq_one.mp w1
  have wm : w∈M := (mem_sdiff.mp (wEq ▸ mem_singleton_self _)).1
  have wp : w∉P := (mem_sdiff.mp (wEq ▸ mem_singleton_self _)).2
  have sLow : G.degree s<6 := by
    have b := one.degree_bound (mem_singleton_self s)
    rw [card_singleton,ss] at b
    omega
  have high (x : V) (xm : x∈A) : 6≤G.degree x := by
    have ne : x≠s := fun e=>disjoint_left.mp sA (mem_singleton_self s) (e ▸ xm)
    exact (degree x s ne).resolve_right (by omega)
  have d2t {x y : V} (xp : x∈P) (yd : y∈D) (xy : G.Adj x y) : y∈Q := by
    have ya := (mem_sdiff.mp yd).1
    have ty := fun e : G.Adj t y=>Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark yd ts e.symm
    have ne : t≠y := fun e=>disjoint_left.mp shA.disjoint ya (e ▸ ts)
    exact mem_inter.mpr ⟨ya,two_of_common hc ne ty (mem_filter.mp xp).2 xy⟩
  have local_cap (x : V) (xp : x∈P) : (A∩DistanceTwo G x).card≤2 := by
    have xm := (mem_filter.mp xp).1
    let F := insert s (visible G S B)
    have fin : F.card=4 := by
      have ns : s∉visible G S B := fun a=>disjoint_left.mp sB (mem_singleton_self s) (mem_filter.mp a).1
      change (insert s (visible G S B)).card=4
      rw [card_insert_of_not_mem ns,vb]
    have inc : F⊆DistanceTwo G x := by
      apply insert_subset _
        (shA.foreign_visible_of_universal shB ab hc xm (all x xp))
      have st : G.Adj t s := by
        obtain ⟨y,ym,e⟩ := one.hit ss conn ts
        rwa [mem_singleton.mp ym] at e
      exact shA.foreign_distance_two one sA.symm hc xp (mem_filter.mpr ⟨mem_singleton_self s,st⟩)
    have dis : Disjoint F (A∩DistanceTwo G x) := by
      apply disjoint_left.mpr
      intro z zf za
      rcases mem_insert.mp zf with zs|zb
      · exact disjoint_left.mp sA (mem_singleton_self s) (zs ▸ (mem_inter.mp za).1)
      · exact disjoint_left.mp ab (mem_inter.mp za).1 (mem_filter.mp zb).1
    have upper := (card_le_card (show F∪(A∩DistanceTwo G x)⊆DistanceTwo G x from union_subset inc inter_subset_right)).trans (distanceTwo_le_of_even 6 x (cap x))
    rw [card_union_of_disjoint dis,fin] at upper
    omega
  by_cases link : ∃ u∈P,G.Adj u w
  · obtain ⟨u,up,uw⟩ := link
    have wa := (mem_filter.mp wm).1
    have no : ¬G.Adj t w := fun e=>wp (mem_filter.mpr ⟨wa,e⟩)
    have ne : t≠w := fun e=>disjoint_left.mp shA.disjoint wa (e ▸ ts)
    have wq : w∈Q := mem_inter.mpr ⟨wa,two_of_common hc ne no (mem_filter.mp up).2 uw⟩
    let K := D\Q
    have small : (D∩Q).card≤1 := by
      have sub : D∩Q⊆Q.erase w := by
        intro z zm
        obtain ⟨zd,zq⟩ := mem_inter.mp zm
        exact mem_erase.mpr ⟨fun e=>(mem_sdiff.mp zd).2 (e ▸ wm),zq⟩
      have c := card_le_card sub
      rwa [card_erase_of_mem wq,q2'] at c
    have k3 : 3≤K.card := by
      have c := card_sdiff_add_card_eq_card (show D∩Q⊆D from inter_subset_left)
      have eq : D\(D∩Q)=K := by ext z; simp [K,and_comm]
      rw [eq] at c
      change 4≤D.card at da
      omega
    have sub : K⊆A∩DistanceTwo G u := by
      intro z zk
      obtain ⟨zd,zq⟩ := mem_sdiff.mp zk
      have za := (mem_sdiff.mp zd).1
      obtain ⟨y,ym,zy⟩ := cover z zd
      have ynot : y∉P := fun h=>zq (d2t h zd zy.symm)
      have yw : y=w := mem_singleton.mp (wEq.symm ▸ mem_sdiff.mpr ⟨ym,ynot⟩)
      have uz : u≠z := fun e=>(mem_sdiff.mp zd).2 (e ▸ pm up)
      have notuz : ¬G.Adj u z := fun e=>zq (d2t up zd e)
      exact mem_inter.mpr ⟨za,two_of_common hc uz notuz uw (yw ▸ zy).symm⟩
    have l := card_le_card sub
    have c := local_cap u up
    omega
  · obtain ⟨u,up⟩ := card_pos.mp (show 0<P.card by omega)
    have uw : ¬G.Adj u w := fun e=>link ⟨u,up,e⟩
    let T := (P.erase u∪Q)∪S
    have usub : G.neighborFinset u⊆T := shA.port_neighbor_cover hc ts up
    have six : T.card≤6 := by
      have a := card_union_le (P.erase u∪Q) S
      have b := card_union_le (P.erase u) Q
      rw [card_erase_of_mem up,p2',q2'] at b
      rw [ss] at a
      change T.card≤(P.erase u∪Q).card+3 at a
      change T.card≤6
      omega
    have uh := high u (mem_filter.mp up).1
    have full : G.neighborFinset u=T := eq_of_subset_of_card_le usub (by
      rw [card_neighborFinset_eq_degree]; exact six.trans uh)
    have wQ : w∉Q := fun h=>uw ((G.mem_neighborFinset ..).mp
      (full.symm ▸ mem_union_left _ (mem_union_right _ h)))
    obtain ⟨y,yq⟩ := card_pos.mp (show 0<Q.card by omega)
    have ya := (mem_inter.mp yq).1
    have darkY : y∈D := by
      refine mem_sdiff.mpr ⟨ya,?_⟩
      intro ym
      have yp : y∉P := fun h=>disjoint_left.mp (disjoint_ports_localTwo G A t) h yq
      have yw : y=w := mem_singleton.mp (wEq.symm ▸ mem_sdiff.mpr ⟨ym,yp⟩)
      exact wQ (yw ▸ yq)
    have uy : G.Adj u y := (G.mem_neighborFinset ..).mp
      (full.symm ▸ mem_union_left _ (mem_union_right _ yq))
    let H := P∪Q
    let J := (G.neighborFinset y)\H
    have hy : y∈H := mem_union_right _ yq
    have h4 : H.card≤4 := by
      have h := card_union_le P Q
      rw [p2',q2'] at h
      exact h
    have inc : G.neighborFinset y⊆H.erase y∪J := by
      intro v vN
      by_cases vh : v∈H
      · exact mem_union_left _ (mem_erase.mpr ⟨((G.mem_neighborFinset ..).mp vN).ne.symm,vh⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨vN,vh⟩)
    have count := (card_le_card inc).trans (card_union_le _ _)
    rw [card_neighborFinset_eq_degree,card_erase_of_mem hy] at count
    have j3 : 3≤J.card := by have h := high y ya; omega
    have sub : J⊆A∩DistanceTwo G u := by
      intro z zm
      obtain ⟨zN,zH⟩ := mem_sdiff.mp zm
      have yz := (G.mem_neighborFinset ..).mp zN
      have za := (shA.closed y ya z yz).resolve_right
        (fun s=>Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark darkY s yz)
      have ne : u≠z := fun e=>zH (mem_union_left _ (e ▸ up))
      have no : ¬G.Adj u z := fun e=>by
        have member := usub ((G.mem_neighborFinset ..).mpr e)
        rcases mem_union.mp member with c|s
        · exact zH ((mem_union.mp c).elim (fun z=>mem_union_left _ (mem_erase.mp z).2)
            (mem_union_right _))
        · exact disjoint_left.mp shA.disjoint za s
      exact mem_inter.mpr ⟨za,two_of_common hc ne no uy yz⟩
    have l := card_le_card sub
    have d := local_cap u up
    omega

#print axioms no_singleton_three_shores_of_isolated_terminal
end Graffiti189LongestPath.ThresholdSix.ThreeCut
