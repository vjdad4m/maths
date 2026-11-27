import PathSlides

open Finset
namespace KelmansCactus.AtomicBridge
open PathSlides
noncomputable section

/-- Exact count for the canonical restriction of a packing to the old
vertices. Two auxiliary vertices sharing any tile save one of the
discarded tiles. -/
theorem packing_restrict_factor_report
    {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
    {G : SimpleGraph V} {H : SimpleGraph X} (e : V↪X)
    (reflects : ∀ x y,H.Adj (e x) (e y)→G.Adj x y)
    {Q : Parts X} (tile : ∀ t∈Q,KelmansStarter.IsTile H t)
    (disj : ∀ t∈Q,∀ s∈Q,t≠s→Disjoint t s) (cover : Q.biUnion id=univ) :
    ∃ P : Parts V,PackIn G univ P ∧
      (∀ t∈P,t.map e∈Q) ∧
      ((univ : Finset V) \ P.biUnion id).card+(Fintype.card X-Fintype.card V)
        =3*(Q.card-P.card) ∧
      Q.card-P.card≤Fintype.card X-Fintype.card V ∧
      (∀ {x y : X}, (¬∃ v,e v=x) → (¬∃ v,e v=y) → x≠y →
        (∃ t∈Q,x∈t ∧ y∈t) →
        Q.card-P.card+1≤Fintype.card X-Fintype.card V) := by
  classical
  let old := (univ : Finset V).map e
  let U := Q.filter (fun t=>t⊆old)
  let pre (t : Finset X) := (univ : Finset V).filter (fun v=>e v∈t)
  have pre_mem (t : Finset X) (v : V) : v∈pre t ↔ e v∈t := by simp [pre]
  have inv {t : Finset X} (sub : t⊆old) : (pre t).map e=t := by
    ext x
    constructor
    · intro hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
      exact (pre_mem _ _).mp hv
    · intro hx
      obtain ⟨v,_,rfl⟩ := mem_map.mp (sub hx)
      exact mem_map.mpr ⟨v,(pre_mem _ _).mpr hx,rfl⟩
  let P := U.image pre
  have each : ∀ t∈P,KelmansStarter.IsTile G t := by
    intro s hs
    obtain ⟨t,tU,rfl⟩ := mem_image.mp hs
    obtain ⟨tQ,sub⟩ := mem_filter.mp tU
    obtain ⟨size,c,cm,star⟩ := tile t tQ
    obtain ⟨r,_,rfl⟩ := mem_map.mp (sub cm)
    have sz : (pre t).card=3 := (card_map e).symm.trans ((congrArg Finset.card (inv sub)).trans size)
    refine ⟨sz,r,(pre_mem t r).mpr cm,?_⟩
    intro y hm ne
    exact reflects _ _ (star (e y) ((pre_mem t y).mp hm) (fun eq=>ne (e.injective eq)))
  have apart : ∀ t∈P,∀ s∈P,t≠s→Disjoint t s := by
    intro t ht s hs ne
    obtain ⟨x,mx,rfl⟩ := mem_image.mp ht
    obtain ⟨y,my,rfl⟩ := mem_image.mp hs
    have D := disj x (mem_filter.mp mx).1 y (mem_filter.mp my).1 (fun eq=>ne (congrArg pre eq))
    exact disjoint_left.mpr fun z za zb=>
      disjoint_left.mp D ((pre_mem _ _).mp za) ((pre_mem _ _).mp zb)
  have pcard : P.card=U.card := by
    apply card_image_of_injOn
    intro x hx y hy eq
    rw [←inv (mem_filter.mp hx).2,←inv (mem_filter.mp hy).2,eq]
  have countQ : (Q.biUnion id).card=3*Q.card := by
    rw [card_biUnion (show (↑Q : Set (Finset X)).PairwiseDisjoint id from
      fun t ht r hr ne=>disj t ht r hr ne)]
    have sz : ∀ t∈Q,(id t).card=3 := fun t ht=>(tile t ht).1
    rw [sum_congr rfl sz]
    simp [Nat.mul_comm]
  have countP : (P.biUnion id).card=3*P.card := by
    rw [card_biUnion (show (↑P : Set (Finset V)).PairwiseDisjoint id from
      fun t ht r hr ne=>apart t ht r hr ne)]
    have sz : ∀ t∈P,(id t).card=3 := fun t ht=>(each t ht).1
    rw [sum_congr rfl sz]
    simp [Nat.mul_comm]
  let B := Q \ U
  let C := (univ : Finset X) \ old
  have find (x : B) : ∃ v : X,v∈x.val ∧ v∈C := by
    obtain ⟨hq,nu⟩ := mem_sdiff.mp x.property
    have nsub : ¬x.val⊆old := fun h=>nu (mem_filter.mpr ⟨hq,h⟩)
    refine Classical.byContradiction ?_
    intro no
    apply nsub
    intro v hv
    refine Classical.byContradiction ?_
    intro nv
    exact no ⟨v,hv,mem_sdiff.mpr ⟨mem_univ _,nv⟩⟩
  let choose (x : B) : C := ⟨Classical.choose (find x),(Classical.choose_spec (find x)).2⟩
  have inj : Function.Injective choose := by
    intro a b eq
    apply Subtype.ext
    refine Classical.byContradiction ?_
    intro ne
    have aa := (Classical.choose_spec (find a)).1
    have bb := (Classical.choose_spec (find b)).1
    have h : Classical.choose (find a)=Classical.choose (find b) :=
      congrArg Subtype.val eq
    exact disjoint_left.mp (disj _ (mem_sdiff.mp a.property).1 _ (mem_sdiff.mp b.property).1 ne)
      aa (h.symm ▸ bb)
  have bound : B.card≤C.card := by
    simpa using Fintype.card_le_of_injective choose inj
  have nB : B.card=Q.card-U.card :=
    card_sdiff (filter_subset _ _)
  have nC : C.card=Fintype.card X-Fintype.card V := by
    change ((univ : Finset X)\old).card=_
    rw [card_sdiff (subset_univ _),card_univ]
    simp [old]
  have oldLe : Fintype.card V≤Fintype.card X := Fintype.card_le_of_injective e e.injective
  have uLe : U.card≤Q.card := card_le_card (filter_subset _ _)
  have pLe : (P.biUnion id).card≤Fintype.card V := card_le_univ _
  rw [cover,card_univ] at countQ
  refine ⟨P,⟨⟨each,apart,rfl⟩,subset_univ _⟩,?_,?_,?_,?_⟩
  · intro s sm
    obtain ⟨t,tU,rfl⟩ := mem_image.mp sm
    rw [inv (mem_filter.mp tU).2]
    exact (mem_filter.mp tU).1
  · rw [card_sdiff (subset_univ _),card_univ,countP,pcard]
    omega
  · rw [pcard,←nB,←nC]
    exact bound
  · intro x y noX noY xy pair
    obtain ⟨T,tQ,xt,yt⟩ := pair
    have xC : x∈C := mem_sdiff.mpr ⟨mem_univ _,fun h=>
      let ⟨v,_,vx⟩ := mem_map.mp h
      noX ⟨v,vx⟩⟩
    have yC : y∈C := mem_sdiff.mpr ⟨mem_univ _,fun h=>
      let ⟨v,_,vy⟩ := mem_map.mp h
      noY ⟨v,vy⟩⟩
    have choose_without (a : B) : ∃ v : X,v∈a.val ∧ v∈C.erase y := by
      by_cases ac : a.val=T
      · exact ⟨x,ac.symm ▸ xt,mem_erase.mpr ⟨xy,xC⟩⟩
      · have noty : y∉a.val :=
          fun h=>disjoint_left.mp (disj _ (mem_sdiff.mp a.property).1 _ tQ ac) h yt
        obtain ⟨v,va,vc⟩ := find a
        exact ⟨v,va,mem_erase.mpr ⟨fun h=>noty (h ▸ va),vc⟩⟩
    let choose₂ (a : B) : C.erase y :=
      ⟨Classical.choose (choose_without a),(Classical.choose_spec (choose_without a)).2⟩
    have inj₂ : Function.Injective choose₂ := by
      intro a b eq
      apply Subtype.ext
      refine Classical.byContradiction ?_
      intro ne
      have aa := (Classical.choose_spec (choose_without a)).1
      have bb := (Classical.choose_spec (choose_without b)).1
      have h : Classical.choose (choose_without a)=Classical.choose (choose_without b) :=
        congrArg Subtype.val eq
      exact disjoint_left.mp (disj _ (mem_sdiff.mp a.property).1 _ (mem_sdiff.mp b.property).1 ne)
        aa (h.symm ▸ bb)
    have strict : B.card≤(C.erase y).card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective choose₂ inj₂
    rw [card_erase_of_mem yC] at strict
    have pos := card_pos.mpr ⟨y,yC⟩
    rw [pcard,←nB,←nC]
    omega

/-- Removing auxiliary vertices from a path factor and restoring any
missing old edges produces a packing with at most twice as many vacancies
as auxiliary vertices. -/
theorem packing_restrict_factor
    {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
    {G : SimpleGraph V} {H : SimpleGraph X} (e : V↪X)
    (reflects : ∀ x y,H.Adj (e x) (e y)→G.Adj x y)
    (fac : KelmansStarter.HasP3Factor H) :
    ∃ P : Parts V,PackIn G univ P ∧
      ((univ : Finset V) \ P.biUnion id).card≤2*(Fintype.card X-Fintype.card V) := by
  obtain ⟨Q,tile,disj,cover⟩ := fac
  obtain ⟨P,ok,_,sum,bd,_⟩ := packing_restrict_factor_report e reflects tile disj cover
  exact ⟨P,ok,by omega⟩

#print axioms packing_restrict_factor_report
#print axioms packing_restrict_factor
end
end KelmansCactus.AtomicBridge
