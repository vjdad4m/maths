import AdjacentVacancyHelpers

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open PathSlides Substitute
noncomputable section

/-- Three new vertices can cost at most three old vacancies, if two
have only one old contact each and those two contacts are adjacent in the
old graph. When all three are in different tiles, the first two new
vertices leave a 4-vertex path on their old contacts and mates. -/
theorem three_aux_repair_with_adjacent_vacancies
    {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
    {G : SimpleGraph V} {H : SimpleGraph X} (e : V↪X)
    (reflects : ∀ x y,H.Adj (e x) (e y)→G.Adj x y)
    (extra : Fintype.card X=Fintype.card V+3)
    {p q r : X} (pn : ¬∃ v,e v=p) (qn : ¬∃ v,e v=q) (rn : ¬∃ v,e v=r)
    (pq : p≠q) (pr : p≠r) (qr : q≠r)
    {a b : V} (aB : G.Adj a b)
    (onlyP : ∀ v,H.Adj p (e v)→v=a)
    (onlyQ : ∀ v,H.Adj q (e v)→v=b)
    (linkedR : ∀ u v,u≠v→H.Adj r (e u)→H.Adj r (e v)→G.Adj u v)
    (fac : KelmansStarter.HasP3Factor H) :
    KelmansStarter.HasP3Factor G ∨
      ∃ P : Parts V,PackIn G univ P ∧
        ((univ : Finset V)\P.biUnion id).card≤3 ∧
        ∃ i j,G.Adj i j ∧ i∉P.biUnion id ∧ j∉P.biUnion id := by
  classical
  obtain ⟨Q,tile,disj,cover⟩ := fac
  obtain ⟨P,ok,kept,exactCount,limit,paired⟩ :=
    packing_restrict_factor_report e reflects tile disj cover
  have delta : Fintype.card X-Fintype.card V=3 := by omega
  rw [delta] at exactCount limit
  have exist (x : X) : ∃ t∈Q,x∈t :=
    mem_biUnion.mp (cover.symm ▸ (mem_univ x))
  obtain ⟨t,tt,pt⟩ := exist p
  obtain ⟨s,ss,qs⟩ := exist q
  obtain ⟨j,jj,rj⟩ := exist r
  have miss {x : X} (xn : ¬∃ v,e v=x) {u : Finset X} (uQ : u∈Q) (xu : x∈u)
      {v : V} (vu : e v∈u) : v∉P.biUnion id := by
    intro used
    obtain ⟨r,rP,vr⟩ := mem_biUnion.mp used
    have rQ := kept r rP
    have rid : r.map e≠u := fun eq=>xn (let ⟨k,_,eke⟩ := mem_map.mp (eq.symm ▸ xu); ⟨k,eke⟩)
    exact disjoint_left.mp (disj _ rQ _ uQ rid) (mem_map.mpr ⟨v,vr,rfl⟩) vu
  have linkedP (u v : V) (ne : u≠v) (pu : H.Adj p (e u)) (pv : H.Adj p (e v)) :
      G.Adj u v := (ne ((onlyP _ pu).trans (onlyP _ pv).symm)).elim
  have linkedQ (u v : V) (ne : u≠v) (qu : H.Adj q (e u)) (qv : H.Adj q (e v)) :
      G.Adj u v := (ne ((onlyQ _ qu).trans (onlyQ _ qv).symm)).elim
  by_cases small : Q.card-P.card≤2
  · let old := (univ : Finset V).map e
    let extras := (univ : Finset X)\old
    let aux : Finset X := {p,q,r}
    have auxSize : aux.card=3 := by simp [aux,pq,pr,qr]
    have extrasSize : extras.card=3 := by
      change (((univ : Finset X)\old).card)=3
      rw [card_sdiff (subset_univ _),card_univ]
      simpa [old] using delta
    have auxEq : aux=extras := by
      apply eq_of_subset_of_card_le
      · intro z zm
        apply mem_sdiff.mpr
        refine ⟨mem_univ _,?_⟩
        intro zo
        obtain ⟨u,_,ue⟩ := mem_map.mp zo
        simp only [aux,mem_insert,mem_singleton] at zm
        rcases zm with rfl|rfl|rfl
        · exact pn ⟨u,ue⟩
        · exact qn ⟨u,ue⟩
        · exact rn ⟨u,ue⟩
      · rw [auxSize,extrasSize]
    have classify (x : X) (no : ¬∃ v,e v=x) : x=p ∨ x=q ∨ x=r := by
      have inSet : x∈aux := auxEq.symm ▸
        (mem_sdiff.mpr ⟨mem_univ _,fun h=>let ⟨v,_,eq⟩:=mem_map.mp h;no ⟨v,eq⟩⟩)
      simpa [aux] using inSet
    have conflict {T U : Finset X} (TM : T∈Q) (UM : U∈Q) (ne : T≠U)
        {x : X} (xT : x∈T) : x∉U := fun xU=>disjoint_left.mp (disj _ TM _ UM ne) xT xU
    have fromSolo {x : X} {T : Finset X} (xn : ¬∃ v,e v=x)
        (TM : T∈Q) (xT : x∈T)
        (only : ∀ y∈T,y≠x→y≠p ∧ y≠q ∧ y≠r)
        (links : ∀ u v,u≠v→H.Adj x (e u)→H.Adj x (e v)→G.Adj u v) :
        ∃ i j,G.Adj i j ∧ i∉P.biUnion id ∧ j∉P.biUnion id := by
      have oldOff (y : X) (ym : y∈T) (neq : y≠x) : ∃ v,e v=y := by
        refine Classical.byContradiction ?_
        intro no
        have ⟨hp,hq,hr⟩ := only y ym neq
        rcases classify y no with e|e|e
        · exact hp e
        · exact hq e
        · exact hr e
      obtain ⟨i,j,ia,mi,mj⟩ := aux_tile_has_adjacent_pair e reflects (tile T TM) xT oldOff links
      exact ⟨i,j,ia,miss xn TM xT mi,miss xn TM xT mj⟩
    have bound : ((univ : Finset V)\P.biUnion id).card≤3 := by omega
    by_cases ts : t=s
    · by_cases tj : t=j
      · have qT : q∈t := ts.symm ▸ qs
        have rT : r∈t := tj.symm ▸ rj
        have same : aux=t := by
          apply eq_of_subset_of_card_le
          · intro x hx
            simp only [aux,mem_insert,mem_singleton] at hx
            rcases hx with rfl|rfl|rfl <;> assumption
          · rw [auxSize,(tile t tt).1]
        left
        apply factor_off_auxiliary_tile e reflects tile disj cover tt
        intro z
        constructor
        · intro zt
          refine Classical.byContradiction ?_
          intro no
          rcases classify z no with rfl|rfl|rfl <;> contradiction
        · rintro ⟨u,h⟩ zm
          have ex : z∈extras := auxEq ▸ (same.symm ▸ zm)
          exact (mem_sdiff.mp ex).2 (mem_map.mpr ⟨u,mem_univ _,h⟩)
      · right
        refine ⟨P,ok,bound,fromSolo rn jj rj ?_ linkedR⟩
        intro y ym yr
        exact ⟨fun e=>conflict tt jj tj pt (e ▸ ym),
          fun e=>conflict tt jj tj (ts.symm ▸ qs) (e ▸ ym),yr⟩
    · by_cases tj : t=j
      · right
        refine ⟨P,ok,bound,fromSolo qn ss qs ?_ linkedQ⟩
        intro y ym yq
        exact ⟨fun e=>conflict tt ss ts pt (e ▸ ym),yq,
          fun e=>conflict tt ss ts (tj.symm ▸ rj) (e ▸ ym)⟩
      · right
        refine ⟨P,ok,bound,fromSolo pn tt pt ?_ linkedP⟩
        intro y ym yp
        exact ⟨yp,fun e=>conflict ss tt (Ne.symm ts) qs (e ▸ ym),
          fun e=>conflict jj tt (Ne.symm tj) rj (e ▸ ym)⟩
  right
  have atMostOne {z : X} (zn : ¬∃ v,e v=z) {t : Finset X}
      (tQ : t∈Q) (zt : z∈t) {y : X} (yt : y∈t) (yz : y≠z) : ∃ v,e v=y := by
    refine Classical.byContradiction ?_
    intro yn
    have good := paired yn zn yz ⟨t,tQ,yt,zt⟩
    rw [delta] at good
    omega
  have split {z : X} (zn : ¬∃ v,e v=z) {d : V}
      (only : ∀ v,H.Adj z (e v)→v=d) {t : Finset X}
      (ht : t∈Q) (zt : z∈t) :
      ∃ w, d≠w ∧ G.Adj d w ∧ e d∈t ∧ e w∈t := by
    obtain ⟨sz,c,ct,star⟩ := tile t ht
    have notCenter : c≠z := by
      intro h
      rw [h] at star
      have sub : t⊆({z,e d} : Finset X) := by
        intro x xt
        by_cases same : x=z
        · simp [same]
        · obtain ⟨v,rfl⟩ := atMostOne zn ht zt xt same
          have vd := only v (star (e v) xt same)
          simp [vd]
      have bound := (card_le_card sub).trans
        (card_insert_le z ({e d}:Finset X))
      rw [sz,card_singleton] at bound
      omega
    obtain ⟨u,hc⟩ := atMostOne zn ht zt ct notCenter
    have ud : u=d := only u (hc.symm ▸ (star z zt notCenter.symm).symm)
    have centerEq : c=e d := by simpa [ud] using hc.symm
    have other : ∃ w∈t,w≠z ∧ w≠c := by
      refine Classical.byContradiction ?_
      intro no
      have sub : t⊆({z,c} : Finset X) := by
        intro x xt
        by_cases ez : x=z
        · simp [ez]
        · have ec : x=c := by
            refine Classical.byContradiction ?_
            intro ec
            exact no ⟨x,xt,ez,ec⟩
          simp [ec]
      have bound := (card_le_card sub).trans (card_insert_le z ({c}:Finset X))
      rw [sz,card_singleton] at bound
      omega
    obtain ⟨w,wt,wz,wc⟩ := other
    obtain ⟨v,ve⟩ := atMostOne zn ht zt wt wz
    have adj : H.Adj (e d) (e v) := by rw [ve,←centerEq]; exact star w wt wc
    exact ⟨v,fun h=>adj.ne (congrArg e h),reflects _ _ adj,centerEq ▸ ct,ve.symm ▸ wt⟩
  have ts : t≠s := by
    intro h
    exact qn (atMostOne pn tt pt (h.symm ▸ qs) pq.symm)
  obtain ⟨w,aw,awE,atPort,wt⟩ := split pn onlyP tt pt
  obtain ⟨_,_,_,bs,_⟩ := split qn onlyQ ss qs
  have wb : w≠b := fun eq=>disjoint_left.mp (disj t tt s ss ts) wt (eq.symm ▸ bs)
  let tileNew : Finset V := {w,a,b}
  have sz : tileNew.card=3 := by simp [tileNew,aw.symm,aB.ne,wb]
  have newOk : KelmansStarter.IsTile G tileNew := ⟨sz,
    (Kelmans.tile_iff_path G tileNew sz).mpr
      ⟨w,a,b,aw.symm,wb,aB.ne,awE.symm,aB,rfl⟩⟩
  have sep : Disjoint (P.biUnion id) tileNew := by
    apply disjoint_left.mpr
    intro v cov hv
    simp only [tileNew,mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl
    · exact miss pn tt pt wt cov
    · exact miss pn tt pt atPort cov
    · exact miss qn ss qs bs cov
  obtain ⟨R,rOk⟩ := add_closed (⟨P,ok.part⟩ : Closed G _) (tile_closed newOk) sep
  have uBound : (R.biUnion id).card≤Fintype.card V := card_le_univ _
  have newSize : (R.biUnion id).card=(P.biUnion id).card+3 := by
    rw [rOk.cover,card_union_of_disjoint sep,sz]
  rw [card_sdiff (subset_univ _),card_univ] at exactCount
  have tj : t≠j := by
    intro h
    exact rn (atMostOne pn tt pt (h.symm ▸ rj) pr.symm)
  have sj : s≠j := by
    intro h
    exact rn (atMostOne qn ss qs (h.symm ▸ rj) qr.symm)
  obtain ⟨k,l,kl,kj,lj⟩ := aux_tile_has_adjacent_pair e reflects (tile j jj) rj
    (fun y ym ne=>atMostOne rn jj rj ym ne) linkedR
  have still {y : V} (hy : e y∈j) : y∉R.biUnion id := by
    intro used
    rw [rOk.cover] at used
    rcases mem_union.mp used with kept|new
    · exact miss rn jj rj hy kept
    · simp only [tileNew,mem_insert,mem_singleton] at new
      rcases new with rfl|rfl|rfl
      · exact disjoint_left.mp (disj _ tt _ jj tj) wt hy
      · exact disjoint_left.mp (disj _ tt _ jj tj) atPort hy
      · exact disjoint_left.mp (disj _ ss _ jj sj) bs hy
  refine ⟨R,⟨⟨rOk.tile,rOk.disj,rfl⟩,subset_univ _⟩,?_,k,l,kl,still kj,still lj⟩
  rw [card_sdiff (subset_univ _),card_univ,newSize]
  omega

#print axioms three_aux_repair_with_adjacent_vacancies
end
end KelmansCactus.AtomicBridge
