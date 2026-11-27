import ThetaSevenFaithfulRefill
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulSplice
open SquareCap (FactorOn IsTile)
open ThetaSevenFaithfulRefill (In Shape inner inner_iff out_not_inner Allowed refills)
noncomputable section

abbrev Dead {V : Type*} : V⊕Fin 3 := .inr 0
abbrev Live {V : Type*} : V⊕Fin 3 := .inr 1
abbrev Faith {V : Type*} : V⊕Fin 3 := .inr 2

private theorem factor_map_on {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {S : Finset V}
    (f : V ↪ W) (mono : ∀ x ∈ S, ∀ y ∈ S,G.Adj x y → H.Adj (f x) (f y))
    (h : FactorOn G S) : FactorOn H (S.map f) := by
  classical
  obtain ⟨P,tiles,disj,cover⟩ := h
  refine ⟨P.image (Finset.map f),?_,?_,?_⟩
  · intro U Uin
    obtain ⟨A,ha,rfl⟩ := mem_image.mp Uin
    obtain ⟨n,c,hc,eb⟩ := tiles A ha
    refine ⟨(card_map f).trans n,f c,mem_map.mpr ⟨c,hc,rfl⟩,?_⟩
    intro y hy ne
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
    have cov (z : V) (hz : z ∈ A) : z ∈ S := cover ▸ mem_biUnion.mpr ⟨A,ha,hz⟩
    exact mono c (cov c hc) v (cov v hv) (eb v hv (fun e => ne (congrArg f e)))
  · intro A Ains B Bins ne
    obtain ⟨U,hu,rfl⟩ := mem_image.mp Ains
    obtain ⟨W,hw,rfl⟩ := mem_image.mp Bins
    exact (disjoint_map f).mpr (disj U hu W hw (fun e => ne (congrArg (Finset.map f) e)))
  · ext z
    rw [mem_map,←cover]
    constructor
    · intro h
      obtain ⟨T,ht,hz⟩ := mem_biUnion.mp h
      obtain ⟨A,Ain,rfl⟩ := mem_image.mp ht
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hz
      exact ⟨x,mem_biUnion.mpr ⟨A,Ain,hx⟩,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨A,Ain,hxa⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨A.map f,mem_image.mpr ⟨A,Ain,rfl⟩,mem_map.mpr ⟨x,hxa,rfl⟩⟩

private theorem factor_disjUnion {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S T : Finset V} (hs : FactorOn G S) (ht : FactorOn G T)
    (d : Disjoint S T) : FactorOn G (S ∪ T) := by
  obtain ⟨P,p,q,r⟩ := hs
  obtain ⟨Q,u,v,w⟩ := ht
  have pq {A B : Finset V} (ha : A ∈ P) (hb : B ∈ Q) : Disjoint A B := by
    apply disjoint_left.mpr
    intro x xa xb
    exact disjoint_left.mp d (r ▸ mem_biUnion.mpr ⟨A,ha,xa⟩) (w ▸ mem_biUnion.mpr ⟨B,hb,xb⟩)
  refine ⟨P∪Q,?_,?_,?_⟩
  · intro A ha
    exact (mem_union.mp ha).elim (p A) (u A)
  · intro A ha B hb ne
    rcases mem_union.mp ha with hp|hq <;> rcases mem_union.mp hb with kp|kq
    · exact q A hp B kp ne
    · exact pq hp kq
    · exact (pq kp hq).symm
    · exact v A hq B kq ne
  · ext x
    rw [←r,←w,mem_union]
    constructor
    · intro hx
      obtain ⟨A,ha,hax⟩ := mem_biUnion.mp hx
      exact (mem_union.mp ha).elim (fun hp => Or.inl (mem_biUnion.mpr ⟨A,hp,hax⟩))
        (fun hq => Or.inr (mem_biUnion.mpr ⟨A,hq,hax⟩))
    · intro hx
      rcases hx with hp | hq
      · obtain ⟨A,ha,hm⟩ := mem_biUnion.mp hp
        exact mem_biUnion.mpr ⟨A,mem_union.mpr (Or.inl ha),hm⟩
      · obtain ⟨A,ha,hm⟩ := mem_biUnion.mp hq
        exact mem_biUnion.mpr ⟨A,mem_union.mpr (Or.inr ha),hm⟩

private theorem factor_erase_one {T : Type*} [DecidableEq T] {F : Finset T}
    {G : SimpleGraph T} (f : FactorOn G F) {x : T} (xF : x ∈ F) :
    ∃ S, S ⊆ F ∧ x ∈ S ∧ IsTile G S ∧ FactorOn G (F \ S) := by
  obtain ⟨P,p,d,u⟩ := f
  have m : x ∈ P.biUnion id := u ▸ xF
  obtain ⟨s,hs,xs⟩ := mem_biUnion.mp m
  have sub : s ⊆ F := fun a h => u ▸ mem_biUnion.mpr ⟨s,hs,h⟩
  refine ⟨s,sub,xs,p s hs,P.erase s,?_,?_,?_⟩
  · intro t ht
    exact p t (mem_erase.mp ht).2
  · intro a ha b hb
    exact d a (mem_erase.mp ha).2 b (mem_erase.mp hb).2
  · ext v
    constructor
    · intro hv
      obtain ⟨t,ht,vt⟩ := mem_biUnion.mp hv
      refine mem_sdiff.mpr ⟨u ▸ mem_biUnion.mpr ⟨t,(mem_erase.mp ht).2,vt⟩,?_⟩
      exact fun vs => disjoint_left.mp (d t (mem_erase.mp ht).2 s hs (mem_erase.mp ht).1) vt vs
    · intro hv
      have vP : v ∈ P.biUnion id := u ▸ (mem_sdiff.mp hv).1
      obtain ⟨t,ht,vt⟩ := mem_biUnion.mp vP
      have nq : t ≠ s := fun e => (mem_sdiff.mp hv).2 (e ▸ vt)
      exact mem_biUnion.mpr ⟨t,mem_erase.mpr ⟨nq,ht⟩,vt⟩

private theorem triple_card {T : Type*} [DecidableEq T] {a b c : T}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    ({a,b,c} : Finset T).card = 3 := by
  simp [card_insert_of_not_mem,ab,ac,bc]

private theorem third {T : Type*} [DecidableEq T] {S : Finset T} {a b : T}
    (sz : S.card=3) (aS : a∈S) (bS : b∈S) (ab : a≠b) :
    ∃ w,w∈S ∧ w≠a ∧ w≠b ∧ S={a,b,w} := by
  have p : ({a,b}:Finset T).card=2 := by simp [card_insert_of_not_mem,ab]
  obtain ⟨w,hw,hide⟩ := exists_mem_not_mem_of_card_lt_card (by omega :
    ({a,b}:Finset T).card<S.card)
  have wa : w≠a := fun h=>hide (by simp [h])
  have wb : w≠b := fun h=>hide (by simp [h])
  refine ⟨w,hw,wa,wb,?_⟩
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  · rw [sz,triple_card ab wa.symm wb.symm]



variable {V : Type*} [Fintype V] [DecidableEq V]

private def relay (j : Fin 3) : Fin 9 := if j=0 then 6 else if j=1 then 7 else 8
private theorem relay_inj : Function.Injective relay :=
  (by decide : ∀ a b : Fin 3,relay a=relay b→a=b)

def put (V : Type*) : (V⊕Fin 3)↪(V⊕Fin 9) :=
  (Function.Embedding.refl V).sumMap ⟨relay,relay_inj⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem put_old (x : V) : put V (.inl x)=.inl x := rfl
omit [Fintype V] [DecidableEq V] in
@[simp] theorem put_dead : put V Dead = In 6 := rfl
omit [Fintype V] [DecidableEq V] in
@[simp] theorem put_live : put V Live = In 7 := rfl
omit [Fintype V] [DecidableEq V] in
@[simp] theorem put_faith : put V Faith = In 8 := rfl

private theorem tag : ∀ i : Fin 3,i=0∨i=1∨i=2 := by decide

omit [Fintype V] in
private theorem notinner {x : V⊕Fin 3} (a : x≠Dead) (b : x≠Live) :
    put V x∉inner V := by
  cases x with
  | inl y => exact out_not_inner y
  | inr i =>
    rcases tag i with rfl|rfl|rfl
    · exact (a rfl).elim
    · exact (b rfl).elim
    · exact fun h=>(inner_iff 8).mp h |>.2 rfl

omit [Fintype V] in
private theorem profile {C : SimpleGraph (V⊕Fin 3)} {p q : V}
    (diff : p≠q)
    (layout : ∀ x,x≠Dead → C.Adj Live x → x=.inl p∨x=.inl q)
    {T : Finset (V⊕Fin 3)} (tile : IsTile C T) (has : Live∈T) (dead : Dead∉T) :
    ∃ x y : V⊕Fin 3,∃ m : Fin 3,
      x≠y ∧ x≠Live ∧ y≠Live ∧ T={Live,x,y} ∧
      ((m=0 ∧ x=.inl p ∧ y=.inl q) ∨
        (m=1 ∧ x=.inl p ∧ C.Adj x y) ∨
        (m=2 ∧ x=.inl q ∧ C.Adj x y)) := by
  obtain ⟨sz,c,hc,star⟩ := tile
  have nd (u) (hu : u∈T) : u≠Dead := fun e=>dead (e ▸ hu)
  by_cases cl : c=Live
  · subst c
    have eq : T={Live,.inl p,.inl q} := by
      apply eq_of_subset_of_card_le
      · intro u hu
        by_cases e : u=Live
        · simp [e]
        · rcases layout u (nd u hu) (star u hu e) with h|h
          · simp [h]
          · simp [h]
      · rw [sz,triple_card (by simp) (by simp) (by simp [diff])]
    exact ⟨.inl p,.inl q,0,fun e=>diff (Sum.inl_injective e),
      by simp,by simp,eq,Or.inl ⟨rfl,rfl,rfl⟩⟩
  have src := layout c (nd c hc) (star Live has (fun e=>cl e.symm)).symm
  obtain ⟨y,yT,yL,yC,eq⟩ := third sz has hc (fun e=>cl e.symm)
  have cy := star y yT yC
  exact ⟨c,y,if c=.inl p then 1 else 2,fun e=>yC e.symm,cl,yL,eq,by
    rcases src with e|e
    · exact Or.inr (Or.inl ⟨by simp [e],e,cy⟩)
    · have d : c≠Sum.inl p := fun e'=>diff (Sum.inl_injective (e'.symm.trans e))
      exact Or.inr (Or.inr ⟨by simp [d],e,cy⟩)⟩

/-- The faithful cap vertex may occur either in its own tile or
as the third vertex of the live tile. Both cases stitch exactly. -/
theorem splice
    {C : SimpleGraph (V⊕Fin 3)} {H : SimpleGraph (V⊕Fin 9)}
    {p q : V} (diff : p≠q) (sh : Shape H)
    (w2 : H.Adj (In 2) (.inl p)) (w5 : H.Adj (In 5) (.inl q))
    (layout : ∀ x,x≠Dead → C.Adj Live x → x=.inl p∨x=.inl q)
    (keep : ∀ x y : V⊕Fin 3,x≠Dead → x≠Live → y≠Dead → y≠Live →
      C.Adj x y → H.Adj (put V x) (put V y))
    (cap : FactorOn C (univ.erase Dead)) :
    FactorOn H (univ.erase (In 6)) := by
  let O : Finset (V⊕Fin 3) := univ.erase Dead
  obtain ⟨T,sub,L,tile,rest⟩ := factor_erase_one cap
    (show (Live : V⊕Fin 3)∈O from by simp [O])
  obtain ⟨x,y,m,xy,xl,yl,shape,mode⟩ := profile diff layout tile L (fun h=>(mem_erase.mp (sub h)).1 rfl)
  have xT : x∈T := by rw [shape]; simp
  have yT : y∈T := by rw [shape]; simp
  have xd : x≠Dead := (mem_erase.mp (sub xT)).1
  have yd : y≠Dead := (mem_erase.mp (sub yT)).1
  let f := put V
  have rule : Allowed H m (f x) (f y) := by
    rcases mode with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,e⟩|⟨rfl,rfl,e⟩
    · exact Or.inl ⟨rfl,w2,w5⟩
    · exact Or.inr (Or.inl ⟨rfl,w2,keep _ _ xd xl yd yl e⟩)
    · exact Or.inr (Or.inr ⟨rfl,w5,keep _ _ xd xl yd yl e⟩)
  have patch := refills sh (fun e=>xy (f.injective e)) (notinner xd xl) (notinner yd yl) m rule
  have eqT : (T.erase Live).map f={f x,f y} := by
    have base : T.erase Live={x,y} := by
      ext z
      rw [shape,mem_erase]
      simp only [mem_insert,mem_singleton]
      constructor
      · rintro ⟨n,rfl|rfl|rfl⟩
        · exact (n rfl).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl|rfl)
        · exact ⟨xl,Or.inr (Or.inl rfl)⟩
        · exact ⟨yl,Or.inr (Or.inr rfl)⟩
    rw [base]
    simp
  have fill : FactorOn H (inner V ∪ (T.erase Live).map f) := eqT.symm ▸ patch
  have adj (u v : V⊕Fin 3) (hu : u∈O\T) (hv : v∈O\T) (a : C.Adj u v) :
      H.Adj (f u) (f v) :=
    keep u v (mem_erase.mp (mem_sdiff.mp hu).1).1
      (fun e=>(mem_sdiff.mp hu).2 (e.symm ▸ L))
      (mem_erase.mp (mem_sdiff.mp hv).1).1
      (fun e=>(mem_sdiff.mp hv).2 (e.symm ▸ L)) a
  have mapped := factor_map_on (H:=H) f (fun u hu v hv e=>adj u v hu hv e) rest
  have apart : Disjoint ((O\T).map f) (inner V ∪ (T.erase Live).map f) := by
    rw [disjoint_left]
    intro z hz g
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hz
    rcases mem_union.mp g with hi|hc
    · exact notinner (mem_erase.mp (mem_sdiff.mp hu).1).1
        (fun e=>(mem_sdiff.mp hu).2 (e.symm ▸ L)) hi
    · obtain ⟨w,hw,e⟩ := mem_map.mp hc
      exact (mem_sdiff.mp hu).2 ((f.injective e) ▸ (mem_erase.mp hw).2)
  have coveredSource : (O\T)∪(T.erase Live)=O.erase Live := by
    ext z
    simp only [mem_union,mem_sdiff,mem_erase]
    constructor
    · rintro (⟨zo,nt⟩|⟨nl,zt⟩)
      · exact ⟨fun h=>nt (h.symm ▸ L),zo⟩
      · exact ⟨nl,sub zt⟩
    · rintro ⟨nl,zo⟩
      by_cases hh : z∈T
      · exact Or.inr ⟨nl,hh⟩
      · exact Or.inl ⟨zo,hh⟩
  have cover : inner V ∪ (O.erase Live).map f=(univ : Finset (V⊕Fin 9)).erase (In 6) := by
    ext z
    cases z with
    | inl u =>
      constructor
      · simp
      · intro _
        exact mem_union_right _ (mem_map.mpr ⟨.inl u,by simp [O],rfl⟩)
    | inr i =>
      rw [mem_union,inner_iff,mem_erase]
      have hf : (Sum.inr i : V⊕Fin 9)∈(O.erase Live).map f ↔ i=8 := by
        constructor
        · intro h
          obtain ⟨u,hu,eq⟩ := mem_map.mp h
          cases u with
          | inl y => exact Sum.noConfusion eq
          | inr j =>
            rcases tag j with rfl|rfl|rfl
            · simp [O] at hu
            · simp [O] at hu
            · exact (Sum.inr_injective eq).symm
        · rintro rfl
          exact mem_map.mpr ⟨Faith,by simp [O],rfl⟩
      rw [hf]
      simp only [In,Sum.inr.injEq,mem_univ,and_true]
      constructor
      · rintro (⟨n,_⟩|rfl)
        · exact fun h=>n (Sum.inr_injective h)
        · exact fun h=>(by decide : (8:Fin 9)≠6) (Sum.inr_injective h)
      · intro n
        by_cases e : i=8
        · exact Or.inr e
        · exact Or.inl ⟨fun h=>n (congrArg Sum.inr h),e⟩
  have K := factor_disjUnion mapped fill apart
  rwa [union_left_comm,←map_union,coveredSource,cover] at K

#print axioms splice
end
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulSplice
