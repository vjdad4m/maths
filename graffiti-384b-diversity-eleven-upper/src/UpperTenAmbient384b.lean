import UpperTenCut384b
import Q8Original384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph OddStars OddStars.LeafCritical
open private Q8Original.triangle_comap from Q8Original384b
open private Repair.omit_set from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V]

structure TenFrame (K : SimpleGraph (Fin 10)) [DecidableRel K.Adj]
    (u v : Fin 10) (B : Finset (Fin 10)) : Prop where
  distinct : u≠v
  apart : ¬K.Adj u v
  uDegree : K.degree u=3
  vDegree : K.degree v=3
  uScore : trianglesAt K u=2
  vScore : trianglesAt K v=3
  balanced : B.card=5
  rootLeft : v∈B
  uCross : (crossed K B u).card=2
  vCross : (crossed K B v).card=2
  ordinary : ∀ x,x≠u→x≠v→4≤K.degree x ∧ 4≤trianglesAt K x ∧ 3≤(crossed K B x).card
  localActive : ∀ x,2≤nbr K x (if x∈B then B else Bᶜ) →
    x∈crossed K B u ∨ x∈crossed K B v

theorem exact_of_upper_ten_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : (types G).card=11) (ten : (high (patch G ∅)).card=10)
    (certificate : ∀ (K : SimpleGraph (Fin 10)) (dec : DecidableRel K.Adj),
      letI := dec
      ∀ (u v : Fin 10) (B : Finset (Fin 10)), TenFrame K u v B →
        ∃ D : Finset (Fin 10), D.card≤4 ∧ TwoDominates K D) : gamma G≤bound G := by
  classical
  by_contra! bad
  let J := patch G ∅
  let H := high J
  have size : H.card+1=(types G).card := by change H.card=10 at ten; omega
  obtain ⟨keep,inj,positive,_,u,v,uv,us,vs,sep,cubics,cuts⟩ := upper_ten G t bad ten
  obtain ⟨A,max,vA⟩ := choose_max_with J v
  obtain ⟨crit,balanced⟩ := cuts A max
  obtain ⟨bigCross,act⟩ := upper_cut_conditions G bad size max crit
  let q : Fin 10 ≃ H := (Fintype.equivFinOfCardEq ((Fintype.card_coe H).trans ten)).symm
  let K := (J.induce (H : Set V)).comap q
  let f : Fin 10 ↪ V := q.toEmbedding.trans (Function.Embedding.subtype _)
  let dk : DecidableRel K.Adj := inferInstanceAs (DecidableRel ((J.induce (H : Set V)).comap q).Adj)
  letI := dk
  have inH (i : Fin 10) : f i∈H := (q i).property
  have surj {x : V} (hx : x∈H) : ∃ i, f i=x :=
    ⟨q.symm ⟨x,hx⟩,congrArg Subtype.val (q.apply_symm_apply ⟨x,hx⟩)⟩
  have edgesHigh {x y : V} (e : J.Adj x y) : y∈H := by
    have d := (J.degree_pos_iff_exists_adj y).mpr ⟨x,e.symm⟩
    have lo := skeleton_degree_bound G y
    change J.degree y≤_ at lo
    exact (PendantAudit.upper_branch G bad size).1 y (by omega)
  have ff (i j : Fin 10) : K.Adj i j ↔ J.Adj (f i) (f j) := Iff.rfl
  have nbf (i : Fin 10) : (K.neighborFinset i).map f=J.neighborFinset (f i) := by
    ext x
    constructor
    · intro xm
      obtain ⟨j,jm,rfl⟩ := mem_map.mp xm
      exact (J.mem_neighborFinset ..).mpr ((ff _ _).mp ((K.mem_neighborFinset ..).mp jm))
    · intro xm
      have e := (J.mem_neighborFinset ..).mp xm
      obtain ⟨j,rfl⟩ := surj (edgesHigh e)
      exact mem_map.mpr ⟨j,(K.mem_neighborFinset ..).mpr ((ff _ _).mpr e),rfl⟩
  have degree (i : Fin 10) : K.degree i=J.degree (f i) := by
    have e := congrArg Finset.card (nbf i)
    simpa only [card_map,card_neighborFinset_eq_degree] using e
  have tri (i : Fin 10) : trianglesAt K i=trianglesAt J (f i) :=
    (Q8Original.triangle_comap (J.induce (H : Set V)) q i).trans
      (Prune.counts_preserved J H (show nonleaves J⊆H from keep.le) (q i))
  have hu : u∈H := by
    have de : J.degree u=3 := (cubics u).mpr (Or.inl rfl)
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hv : v∈H := by
    have de : J.degree v=3 := (cubics v).mpr (Or.inr rfl)
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  obtain ⟨i,fi⟩ := surj hu
  obtain ⟨j,fj⟩ := surj hv
  let B := univ.filter (fun i : Fin 10=> f i∈A)
  have side (x : Fin 10) : x∈B ↔ f x∈A := by simp [B]
  have mapB : B.map f=H∩A := by
    ext w
    constructor
    · intro wm
      obtain ⟨x,xm,rfl⟩ := mem_map.mp wm
      exact mem_inter.mpr ⟨inH x,(side x).mp xm⟩
    · intro wm
      obtain ⟨wm,wa⟩ := mem_inter.mp wm
      obtain ⟨x,rfl⟩ := surj wm
      exact mem_map.mpr ⟨x,(side x).mpr wa,rfl⟩
  have bcard : B.card=5 := by
    rw [←card_map f,mapB]
    exact balanced
  have cMap (x : Fin 10) : (crossed K B x).map f=crossed J A (f x) := by
    ext y
    constructor
    · intro ym
      obtain ⟨w,wm,rfl⟩ := mem_map.mp ym
      obtain ⟨adj,opp⟩ := mem_filter.mp wm
      have e := (ff _ _).mp ((K.mem_neighborFinset ..).mp adj)
      exact mem_filter.mpr ⟨(J.mem_neighborFinset ..).mpr e,fun h=>opp ((side x).trans (h.trans (side w).symm))⟩
    · intro ym
      obtain ⟨adj,opp⟩ := mem_filter.mp ym
      have e := (J.mem_neighborFinset ..).mp adj
      obtain ⟨w,rfl⟩ := surj (edgesHigh e)
      exact mem_map.mpr ⟨w,mem_filter.mpr ⟨(K.mem_neighborFinset ..).mpr ((ff _ _).mpr e),
        fun h=>opp ((side x).symm.trans (h.trans (side w)))⟩,rfl⟩
  have crossCard (x : Fin 10) : (crossed K B x).card=(crossed J A (f x)).card := by
    rw [←card_map f,cMap]
  have nSide (x : Fin 10) (D : Finset (Fin 10)) (E : Finset V)
      (same : ∀ y, y∈D ↔ f y∈E) : nbr K x D=nbr J (f x) E := by
    have eq : (D.filter (K.Adj x)).map f=E.filter (J.Adj (f x)) := by
      ext z
      constructor
      · intro zm
        obtain ⟨w,wm,rfl⟩ := mem_map.mp zm
        obtain ⟨wd,wx⟩ := mem_filter.mp wm
        exact mem_filter.mpr ⟨(same w).mp wd,(ff _ _).mp wx⟩
      · intro zm
        obtain ⟨zd,zx⟩ := mem_filter.mp zm
        obtain ⟨w,rfl⟩ := surj (edgesHigh zx)
        exact mem_map.mpr ⟨w,mem_filter.mpr ⟨(same w).mpr zd,(ff _ _).mpr zx⟩,rfl⟩
    unfold nbr
    rw [←card_map f,eq]
  have sameCard (x : Fin 10) :
      nbr K x (if x∈B then B else Bᶜ)=nbr J (f x) (if f x∈A then A else Aᶜ) := by
    by_cases xB : x∈B
    · rw [if_pos xB,if_pos ((side x).mp xB)]
      exact nSide x B A side
    · rw [if_neg xB,if_neg (fun m=>xB ((side x).mpr m))]
      exact nSide x Bᶜ Aᶜ (by intro y; simpa only [mem_compl] using not_congr (side y))
  have cU : (crossed J A u).card=2 := (mem_filter.mp
    (show u∈critical J A from crit ▸ mem_insert_self ..)).2
  have cV : (crossed J A v).card=2 := (mem_filter.mp
    (show v∈critical J A from crit ▸ mem_insert_of_mem (mem_singleton_self _))).2
  have frame : TenFrame K i j B := by
    refine ⟨fun eq=>uv (fi.symm.trans ((congrArg f eq).trans fj)),
      fun e=>sep (fi ▸ fj ▸ (ff i j).mp e),
      by rw [degree,fi]; exact (cubics u).mpr (Or.inl rfl),
      by rw [degree,fj]; exact (cubics v).mpr (Or.inr rfl),
      by rw [tri,fi]; exact us,by rw [tri,fj]; exact vs,
      bcard,(side j).mpr (fj.symm ▸ vA),by rwa [crossCard,fi],by rwa [crossCard,fj],?_,?_⟩
    · intro x xi xj
      have xu : f x≠u := fun e=>xi (f.injective (e.trans fi.symm))
      have xv : f x≠v := fun e=>xj (f.injective (e.trans fj.symm))
      have h := inH x
      have gd : 3≤J.degree (f x) := (mem_filter.mp h).2
      have ge : 2≤trianglesAt J (f x) := positive _ h
      have d := bigCross _ h xu xv
      refine ⟨by rw [degree]; have not : J.degree (f x)≠3 := mt (cubics (f x)).mp (not_or.mpr ⟨xu,xv⟩); omega,?_,by rwa [crossCard]⟩
      rw [tri]
      have no2 : trianglesAt J (f x)≠2 := fun eq=>xu (inj h hu (eq.trans us.symm))
      have no3 : trianglesAt J (f x)≠3 := fun eq=>xv (inj h hv (eq.trans vs.symm))
      omega
    · intro x a
      rw [sameCard] at a
      rcases act _ (inH x) a with t|s
      · left
        have z : f x∈(crossed K B i).map f := by rw [cMap,fi]; exact t
        obtain ⟨y,ym,eq⟩ := mem_map.mp z
        exact f.injective eq ▸ ym
      · right
        have z : f x∈(crossed K B j).map f := by rw [cMap,fj]; exact s
        obtain ⟨y,ym,eq⟩ := mem_map.mp z
        exact f.injective eq ▸ ym
  obtain ⟨D,small,dom⟩ := certificate K dk i j B frame
  let O := Dᶜ.map f
  have save := Repair.omit_set G O (by
    intro x xm
    obtain ⟨w,wm,rfl⟩ := mem_map.mp xm
    have sub : (D.filter (K.Adj w)).map f ⊆ Oᶜ.filter (G.Adj (f w)) := by
      intro y ym
      obtain ⟨z,zm,rfl⟩ := mem_map.mp ym
      refine mem_filter.mpr ⟨mem_compl.mpr ?_,((ff _ _).mp (mem_filter.mp zm).2).1⟩
      intro h
      obtain ⟨a,am,eq⟩ := mem_map.mp h
      exact mem_compl.mp am (f.injective eq ▸ (mem_filter.mp zm).1)
    have c := card_le_card sub
    rw [card_map] at c
    exact (dom _ (mem_compl.mp wm)).trans c)
  have omitted : O.card=10-D.card := by rw [show O=Dᶜ.map f from rfl,card_map,card_compl,Fintype.card_fin]
  have N := card_le_univ O
  unfold bound at bad
  omega

#print axioms exact_of_upper_ten_certificate
end Graffiti384b.DiversityEleven
