import AdjacentCutFiveFourteenDarkLift189
import AdjacentCutFiveFourteenSingletonTerminal189
import AdjacentCutFiveMixedRouteSmall189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

structure SingletonEC1Frame (G : SimpleGraph V) [DecidableRel G.Adj] where
  (a b s x y e : V)
  (W K A B : Finset V)
  -- The outside block excludes e, and D's dark block is W plus e.
  xOff : x∉({y,b,s,a}:Finset V)
  eOff : e∉({x,y,b,s,a}:Finset V)
  wk : Disjoint W K
  wOff : Disjoint W {a,b,s,x,y,e}
  kOff : Disjoint K {a,b,s,x,y,e}
  cover : W ∪ K ∪ {a,b,s,x,y,e}=univ
  stem : RouteOn G {y,b,s,a} y a
  ak : ∀ k∈K,G.Adj a k
  xA : ∀ u∈A,G.Adj x u
  yB : ∀ u∈B,G.Adj y u
  aW : A⊆W
  bW : B⊆W
  apart : Disjoint A B
  a2 : 2≤A.card
  b2 : 2≤B.card
  small : W.card≤6
  k2 : 2≤K.card
  k3 : K.card≤3
  linkK : ∀ k∈K,∃ v∈K,G.Adj k v
  lowEk : (inside G W e).card≤1 → 2≤(K.filter (G.Adj e)).card
  highW : ∀ u∈W,4≤(inside G (insert e W) u).card

private theorem prepend_common_chain
    (K : Finset V) (two : 2≤K.card) (three : K.card≤3)
    (link : ∀ k∈K,∃ v∈K,G.Adj k v) :
    ∃ p q, p∈K ∧ q∈K ∧ p≠q ∧ RouteOn G K p q := by
  classical
  obtain ⟨x,xm⟩ := card_pos.mp (show 0<K.card by omega)
  obtain ⟨y,ym,xy⟩ := link x xm
  let P : Finset V := {x,y}
  have sub : P⊆K := insert_subset_iff.mpr ⟨xm,singleton_subset_iff.mpr ym⟩
  have p2 : P.card=2 := by simp [P,xy.ne]
  by_cases c : K.card=2
  · have f : P=K := eq_of_subset_of_card_le sub (by omega)
    exact ⟨x,y,xm,ym,xy.ne,f ▸ RouteOn.edge xy⟩
  obtain ⟨z,zm⟩ := card_pos.mp (show 0<(K\P).card by
    have g := card_sdiff_add_card_eq_card sub
    omega)
  obtain ⟨zK,zP⟩ := mem_sdiff.mp zm
  have zx : z≠x := fun e=>zP (by simp [P,e])
  have zy : z≠y := fun e=>zP (by simp [P,e])
  have f : insert z P=K := by
    apply eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨zK,sub⟩)
    rw [card_insert_of_not_mem zP,p2]
    omega
  obtain ⟨v,vK,zv⟩ := link z zK
  have zP' : v∈P := by
    have vm : v∈insert z P := f.symm ▸ vK
    exact (mem_insert.mp vm).resolve_left zv.ne.symm
  have vz : v=x ∨ v=y := by simpa [P] using zP'
  rcases vz with rfl|rfl
  · exact ⟨z,y,zK,ym,zy,f ▸ (RouteOn.edge xy).prefix zv zP⟩
  · exact ⟨z,x,zK,xm,zx,f ▸ (RouteOn.edge xy).reverse.prefix zv zP⟩

private theorem lower_inside_after_insert (S : Finset V) {x w : V} :
    (inside G (insert x S) w).card≤(inside G S w).card+1 := by
  classical
  have sub : inside G (insert x S) w⊆insert x (inside G S w) := by
    intro z zm
    obtain ⟨s,e⟩ := mem_filter.mp zm
    rcases mem_insert.mp s with rfl|h
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨h,e⟩)
  exact (card_le_card sub).trans (card_insert_le _ _)

private theorem equal_inside_after_insert (S : Finset V) {x w : V}
    (no : ¬G.Adj w x) : inside G (insert x S) w=inside G S w := by
  classical
  ext z
  simp only [inside,mem_filter,mem_insert]
  constructor
  · rintro ⟨h,e⟩
    exact ⟨h.resolve_left (fun z=>no (z ▸ e)),e⟩
  · exact fun h=>⟨.inr h.1,h.2⟩

set_option maxHeartbeats 3000000 in
theorem SingletonEC1Frame.traceable (F : SingletonEC1Frame G) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨p,q,pm,qm,pq,commonP⟩ := prepend_common_chain F.K F.k2 F.k3 F.linkK
  have Woff {z : V} (h : z∈({F.a,F.b,F.s,F.x,F.y,F.e}:Finset V)) : z∉F.W :=
    fun e=>disjoint_left.mp F.wOff e h
  have Koff {z : V} (h : z∈({F.a,F.b,F.s,F.x,F.y,F.e}:Finset V)) : z∉F.K :=
    fun e=>disjoint_left.mp F.kOff e h
  have eW : F.e∉F.W := Woff (by simp)
  have eK : F.e∉F.K := Koff (by simp)
  have xW : F.x∉F.W := Woff (by simp)
  have xE : F.x≠F.e := fun e=>F.eOff (by simp [←e])
  have assemble (S R : Finset V) {u v k : V} (aU : u∈F.A) (bV : v∈F.B) (kK : k∈F.K)
      (pD : RouteOn G S u v) {t : V} (qK : RouteOn G R k t)
      (sB : S⊆insert F.e F.W) (rB : R⊆insert F.e F.K)
      (sep : Disjoint S R) (cov : S∪R=insert F.e (F.W∪F.K)) :
      ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
    have xS : F.x∉S := fun h=>(mem_insert.mp (sB h)).elim xE xW
    have xR : F.x∉R := fun h=>(mem_insert.mp (rB h)).elim xE (Koff (by simp))
    have spr : Disjoint (insert F.x S) ({F.y,F.b,F.s,F.a}:Finset V) := by
      apply disjoint_left.mpr
      intro z zm zo
      rcases mem_insert.mp zm with rfl|zm
      · exact F.xOff zo
      rcases mem_insert.mp (sB zm) with ez|zw
      · exact F.eOff (by rw [← ez]; simp only [mem_insert,mem_singleton] at zo ⊢; tauto)
      · exact Woff (by simp only [mem_insert,mem_singleton] at zo ⊢; tauto) zw
    have rr : Disjoint ((insert F.x S)∪{F.y,F.b,F.s,F.a}) R := by
      apply disjoint_left.mpr
      intro z zm zr
      rcases mem_union.mp zm with zm|zm
      · rcases mem_insert.mp zm with rfl|zm
        · exact xR zr
        · exact disjoint_left.mp sep zm zr
      rcases mem_insert.mp (rB zr) with ez|zk
      · exact F.eOff (by rw [←ez]; simp only [mem_insert,mem_singleton] at zm ⊢; tauto)
      · exact Koff (by simp only [mem_insert,mem_singleton] at zm ⊢; tauto) zk
    have path := ((pD.prefix (F.xA u aU) xS).join F.stem spr (F.yB v bV).symm).join qK rr (F.ak k kK)
    obtain ⟨w,wp,ws⟩ := path
    refine ⟨F.x,t,w,wp,fun z=>(ws z).mpr ?_⟩
    have c := F.cover
    have mem : z∈F.W∪F.K∪({F.a,F.b,F.s,F.x,F.y,F.e}:Finset V) := c.symm ▸ mem_univ _
    have mc : z∈insert F.e (F.W∪F.K) ∨ z∈({F.x,F.y,F.b,F.s,F.a}:Finset V) := by
      simp only [mem_union,mem_insert,mem_singleton] at mem ⊢
      tauto
    rw [←cov] at mc
    simp only [mem_union,mem_insert,mem_singleton] at mc ⊢
    tauto
  by_cases twoE : 2≤(inside G F.W F.e).card
  · obtain ⟨u,um,v,vm,ne⟩ := one_lt_card.mp twoE
    obtain ⟨uW,eu⟩ := mem_filter.mp um
    obtain ⟨vW,ev⟩ := mem_filter.mp vm
    obtain ⟨j,jA,l,lB,jl,avoid⟩ :=
      choose_opposite_endpoints_away_from_pair F.A F.B F.apart
        (card_pos.mp (by have t:=F.a2; omega)) (card_pos.mp (by have t:=F.b2; omega)) (.inl F.a2) (u:=u) (v:=v)
    let S := insert F.e F.W
    have rm : S.erase F.e=F.W := erase_insert eW
    have route : RouteOn G S j l := terminal_route_on_via_one_exception S
      (mem_insert_self _ _) (rm.symm ▸ F.aW jA) (rm.symm ▸ F.bW lB) jl
      (rm.symm ▸ uW) (rm.symm ▸ vW) ne eu ev avoid (by
        intro x xm y ym _ _
        rw [rm] at xm ym
        have U := F.highW x xm
        have V := F.highW y ym
        have c := card_insert_le F.e F.W
        have small := F.small
        change (insert F.e F.W).card+1≤(inside G (insert F.e F.W) x).card+(inside G (insert F.e F.W) y).card
        omega)
    exact assemble S F.K jA lB pm route commonP (Subset.rfl) (subset_insert _ _)
      (by
        apply disjoint_left.mpr
        intro z zs zk
        rcases mem_insert.mp zs with rfl|zw
        · exact eK zk
        exact disjoint_left.mp F.wk zw zk)
      (by rw [insert_union])
  have common_end : ∃ k∈F.K,RouteOn G (insert F.e F.K) k F.e := by
    have many := F.lowEk (by omega)
    by_cases qe : G.Adj F.e q
    · exact ⟨p,pm,commonP.suffix qe.symm eK⟩
    have pe : G.Adj F.e p := by
      apply Classical.byContradiction
      intro pe
      have sub : F.K.filter (G.Adj F.e)⊆(F.K.erase p).erase q := by
        intro z zm
        obtain ⟨zk,ez⟩ := mem_filter.mp zm
        exact mem_erase.mpr ⟨fun d=>qe (d ▸ ez),mem_erase.mpr ⟨fun d=>pe (d ▸ ez),zk⟩⟩
      have bd := card_le_card sub
      have qm' : q∈F.K.erase p := mem_erase.mpr ⟨pq.symm,qm⟩
      rw [card_erase_of_mem qm',card_erase_of_mem pm] at bd
      have h := F.k3
      omega
    exact ⟨q,qm,commonP.reverse.suffix pe.symm eK⟩
  obtain ⟨k,kK,tail⟩ := common_end
  have finish {u v : V} (ua : u∈F.A) (vb : v∈F.B) (p : RouteOn G F.W u v) :
      ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support :=
    assemble F.W (insert F.e F.K) ua vb kK p tail (subset_insert _ _) (Subset.rfl)
      (by
        apply disjoint_left.mpr
        intro z zw zs
        rcases mem_insert.mp zs with rfl|zk
        · exact eW zw
        exact disjoint_left.mp F.wk zw zk)
      (by rw [union_insert])
  have low3 (z : V) (zw : z∈F.W) : 3≤(inside G F.W z).card := by
    have h := F.highW z zw
    have r := lower_inside_after_insert (G:=G) F.W (x:=F.e) (w:=z)
    omega
  by_cases n : (inside G F.W F.e).Nonempty
  · obtain ⟨z,ze⟩ := n
    obtain ⟨zw,ez⟩ := mem_filter.mp ze
    have high (w : V) (wm : w∈F.W.erase z) : 4≤(inside G F.W w).card := by
      obtain ⟨wz,ww⟩ := mem_erase.mp wm
      have no : ¬G.Adj w F.e := by
        intro we
        have q : 2≤(inside G F.W F.e).card := one_lt_card.mpr
          ⟨w,mem_filter.mpr ⟨ww,we.symm⟩,z,ze,wz⟩
        exact twoE q
      have f := F.highW w ww
      rwa [equal_inside_after_insert F.W no] at f
    obtain ⟨u,ua'⟩ := card_pos.mp (show 0<(F.A.erase z).card by
      have h := F.a2
      have k := card_erase_add_one (s:=F.A) (a:=z)
      by_cases p : z∈F.A
      · have q := k p; omega
      · rw [erase_eq_of_not_mem p]; omega)
    obtain ⟨v,vb'⟩ := card_pos.mp (show 0<(F.B.erase z).card by
      have h := F.b2
      by_cases p : z∈F.B
      · have q := card_erase_add_one p; omega
      · rw [erase_eq_of_not_mem p]; omega)
    obtain ⟨uz,ua⟩ := mem_erase.mp ua'
    obtain ⟨vz,vb⟩ := mem_erase.mp vb'
    have uv : u≠v := fun e=>disjoint_left.mp F.apart ua (e.symm ▸ vb)
    let I := inside G F.W z
    have n3 : 3≤I.card := low3 z zw
    have N : ¬ I⊆({u,v}:Finset V) := by
      intro h
      have b := card_le_card h
      have k := card_insert_le u ({v}:Finset V)
      rw [card_singleton] at k
      omega
    obtain ⟨i,im,io⟩ := not_subset.mp N
    obtain ⟨j,jm⟩ := card_pos.mp (show 0<(I.erase i).card by
      rw [card_erase_of_mem im]
      omega)
    obtain ⟨ji,jm⟩ := mem_erase.mp jm
    obtain ⟨iw,zi⟩ := mem_filter.mp im
    obtain ⟨jw,zj⟩ := mem_filter.mp jm
    apply finish ua vb
    apply terminal_route_on_via_one_exception F.W zw (mem_erase.mpr ⟨uz,F.aW ua⟩)
      (mem_erase.mpr ⟨vz,F.bW vb⟩) uv (mem_erase.mpr ⟨zi.ne.symm,iw⟩) (mem_erase.mpr ⟨zj.ne.symm,jw⟩)
      ji.symm zi zj
    · intro h
      rcases h with ⟨h,_⟩|⟨_,h⟩
      · exact io (by simp [←h])
      · exact io (by simp [←h])
    · intro i im j jm _ _
      have hi := high i im
      have hj := high j jm
      have sm := F.small
      omega
  have high (z : V) (zw : z∈F.W) : 4≤(inside G F.W z).card := by
    have no : ¬G.Adj z F.e := fun h=>n ⟨z,mem_filter.mpr ⟨zw,h.symm⟩⟩
    have f := F.highW z zw
    rwa [equal_inside_after_insert F.W no] at f
  obtain ⟨u,ua⟩ := card_pos.mp (show 0<F.A.card by have k:=F.a2; omega)
  obtain ⟨v,vb⟩ := card_pos.mp (show 0<F.B.card by have k:=F.b2; omega)
  exact finish ua vb (terminal_route_on_of_local_ore F.W (F.aW ua) (F.bW vb)
    (fun e=>disjoint_left.mp F.apart ua (e.symm ▸ vb)) (by
      intro i im j jm _ _
      have hi := high i im
      have hj := high j jm
      have sm := F.small
      omega))

#print axioms SingletonEC1Frame.traceable
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
