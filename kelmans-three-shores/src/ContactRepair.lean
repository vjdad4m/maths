import FactorRestriction
import Substitute

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open PathSlides Substitute
noncomputable section

/-- Three new vertices can cost at most three old vacancies, if two
have only one old contact each and those two contacts are adjacent in the
old graph. When all three are in different tiles, the first two new
vertices leave a 4-vertex path on their old contacts and mates. -/
theorem three_aux_single_contact_repair
    {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
    {G : SimpleGraph V} {H : SimpleGraph X} (e : V↪X)
    (reflects : ∀ x y,H.Adj (e x) (e y)→G.Adj x y)
    (extra : Fintype.card X=Fintype.card V+3)
    {p q : X} (pn : ¬∃ v,e v=p) (qn : ¬∃ v,e v=q) (pq : p≠q)
    {a b : V} (aB : G.Adj a b)
    (onlyP : ∀ v,H.Adj p (e v)→v=a)
    (onlyQ : ∀ v,H.Adj q (e v)→v=b)
    (fac : KelmansStarter.HasP3Factor H) :
    ∃ P : Parts V,PackIn G univ P ∧
      ((univ : Finset V)\P.biUnion id).card≤3 := by
  classical
  obtain ⟨Q,tile,disj,cover⟩ := fac
  obtain ⟨P,ok,kept,exactCount,limit,paired⟩ :=
    packing_restrict_factor_report e reflects tile disj cover
  have delta : Fintype.card X-Fintype.card V=3 := by omega
  rw [delta] at exactCount limit
  by_cases small : Q.card-P.card≤2
  · exact ⟨P,ok,by omega⟩
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
  have exist (x : X) : ∃ t∈Q,x∈t :=
    mem_biUnion.mp (cover.symm ▸ (mem_univ x))
  obtain ⟨t,tt,pt⟩ := exist p
  obtain ⟨s,ss,qs⟩ := exist q
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
  have miss {x : X} (xn : ¬∃ v,e v=x) {u : Finset X} (uQ : u∈Q) (xu : x∈u)
      {v : V} (vu : e v∈u) : v∉P.biUnion id := by
    intro used
    obtain ⟨r,rP,vr⟩ := mem_biUnion.mp used
    have rQ := kept r rP
    have rid : r.map e≠u := fun eq=>xn (let ⟨k,_,eke⟩ := mem_map.mp (eq.symm ▸ xu); ⟨k,eke⟩)
    exact disjoint_left.mp (disj _ rQ _ uQ rid) (mem_map.mpr ⟨v,vr,rfl⟩) vu
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
  refine ⟨R,⟨⟨rOk.tile,rOk.disj,rfl⟩,subset_univ _⟩,?_⟩
  rw [card_sdiff (subset_univ _),card_univ,newSize]
  omega

#print axioms three_aux_single_contact_repair
end
end KelmansCactus.AtomicBridge
