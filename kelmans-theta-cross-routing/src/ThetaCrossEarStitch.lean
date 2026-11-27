import ThetaCrossEarRefill
import ThetaAdjacentEarLeafModes

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaCrossEarStitch
open SquareCap (FactorOn IsTile)
open ThetaFiveModes (Lane mid leaf)
open ThetaAdjacentEarRefill (Shape In Out liveFin mem_live)
open ThetaCrossEarRefill (Allowed firstSite nextSite refill)
open ThetaAdjacentEarLeafModes (WeakLayout actual_leaf_profile leaves_separate)
noncomputable section

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



variable {V : Type*} [Fintype V] [DecidableEq V]

private def put (V : Type*) : (V⊕Fin 3) ↪ (V⊕Fin 9) :=
  (Function.Embedding.refl V).sumMap ⟨fun i=>⟨i.val,by have h:=i.isLt; omega⟩,
    fun i j eq=>Fin.ext (congrArg (fun z : Fin 9=>z.val) eq)⟩

private def gone (S : Finset (V⊕Fin 3)) : Finset (V⊕Fin 9) :=
  ((univ : Finset V).filter (fun x=>Sum.inl x∈S)).map ⟨Sum.inl,Sum.inl_injective⟩

private theorem gone_mem {S : Finset (V⊕Fin 3)} (a : V) : Out a∈gone S ↔ Sum.inl a∈S := by
  simp [gone,mem_map]

omit [Fintype V] [DecidableEq V] in
private theorem all_virtual (v : Fin 3) :
    (Sum.inr v : V⊕Fin 3)=mid ∨ Sum.inr v=leaf (V:=V) false ∨ Sum.inr v=leaf (V:=V) true := by
  have k : ∀ j : Fin 3,j=0∨j=1∨j=2 := by decide
  rcases k v with rfl|rfl|rfl <;> simp [mid,leaf]

/-- Stitch a tiling of consumed contacts plus the live ring with
the pullback of the factor on the cap exterior that remains. -/
private theorem stitch {C : SimpleGraph (V⊕Fin 3)} {H : SimpleGraph (V⊕Fin 9)}
    (old : ∀ a b : V,C.Adj (.inl a) (.inl b) → H.Adj (.inl a) (.inl b))
    {S : Finset (V⊕Fin 3)}
    (midIn : mid∈S) (lIn : leaf false∈S) (rIn : leaf true∈S)
    (rem : FactorOn C (univ \ S)) (fill : FactorOn H (liveFin V ∪ gone S)) :
    FactorOn H (univ.erase (Sum.inr 6)) := by
  let f := put V
  have virtual (i : Fin 3) : (Sum.inr i : V⊕Fin 3)∈S := by
    rcases all_virtual i with e|e|e
    · exact e.symm ▸ midIn
    · exact e.symm ▸ lIn
    · exact e.symm ▸ rIn
  have stay : FactorOn H ((univ \ S).map f) :=
    factor_map_on f (by
      intro x xx y yy a
      cases x with
      | inr i => exact ((mem_sdiff.mp xx).2 (virtual i)).elim
      | inl u =>
        cases y with
        | inr i => exact ((mem_sdiff.mp yy).2 (virtual i)).elim
        | inl v => exact old u v a) rem
  have leftIn (a : V) : Out a∈((univ \ S).map f) ↔ Sum.inl a∉S := by
    simp [f,put,mem_map]
  have innerNo (i : Fin 9) : (Sum.inr i : V⊕Fin 9)∉((univ \ S).map f) := by
    intro h
    obtain ⟨x,m,h⟩ := mem_map.mp h
    cases x with
    | inr j => exact (mem_sdiff.mp m).2 (virtual j)
    | inl j => exact Sum.noConfusion (show (Sum.inl j : V⊕Fin 9)=Sum.inr i from h)
  have innerGone (i : Fin 9) : (Sum.inr i : V⊕Fin 9)∉gone S := by
    simp [gone,mem_map]
  have OutRing (a : V) : Out a∉liveFin V := by
    simp [liveFin,mem_map]
  have apart : Disjoint ((univ \ S).map f) (liveFin V ∪ gone S) := by
    rw [disjoint_left]
    intro x h g
    cases x with
    | inr i => exact innerNo i h
    | inl a =>
      rcases mem_union.mp g with ring|gone
      · exact OutRing a ring
      · exact (leftIn a).mp h ((gone_mem a).mp gone)
  have cover : ((univ \ S).map f) ∪ (liveFin V ∪ gone S) =
      (univ : Finset (V⊕Fin 9)).erase (Sum.inr 6) := by
    ext x
    cases x with
    | inr i => simp [innerNo i,innerGone i,mem_live]
    | inl a =>
      have t : (Sum.inl a : V⊕Fin 9) ≠ Sum.inr 6 := by simp
      simp only [mem_union,leftIn,OutRing,gone_mem,mem_erase,mem_univ,and_true,t]
      tauto
  exact cover ▸ factor_disjUnion stay fill apart



private def tuple (a b c d : V) (i : Fin 4) : V :=
  if i=0 then a else if i=1 then b else if i=2 then c else d

omit [Fintype V] [DecidableEq V] in
private theorem tuple_inj {a b c d : V} (ab : a≠b) (cd : c≠d)
    (sep : ∀ v,v=a∨v=b → v=c∨v=d → False) :
    Function.Injective (tuple a b c d) := by
  have ac : a≠c := fun h=>sep a (Or.inl rfl) (Or.inl h)
  have ad : a≠d := fun h=>sep a (Or.inl rfl) (Or.inr h)
  have bc : b≠c := fun h=>sep b (Or.inr rfl) (Or.inl h)
  have bd : b≠d := fun h=>sep b (Or.inr rfl) (Or.inr h)
  intro i j e
  fin_cases i <;> fin_cases j <;> simp_all [tuple,Ne.symm ab,Ne.symm ac,Ne.symm ad,
    Ne.symm bc,Ne.symm bd,Ne.symm cd]

omit [Fintype V] in
private theorem to_mode {C : SimpleGraph (V⊕Fin 3)} {H : SimpleGraph (V⊕Fin 9)}
    {p : Lane↪V} (layout : WeakLayout C p)
    (old : ∀ a b : V,C.Adj (.inl a) (.inl b) → H.Adj (Out a) (Out b))
    (wire : ∀ s i : Bool,C.Adj (leaf s) (.inl (p (s,i))) →
      H.Adj (In (if i then nextSite s else firstSite s)) (Out (p (s,i))))
    {T : Finset (V⊕Fin 3)} (tile : IsTile C T) (s : Bool)
    (has : leaf s∈T) (noMid : mid∉T) (noOther : leaf (!s)∉T) :
    ∃ (m : Fin 3) (a b : V),a≠b ∧ Allowed H p s m a b ∧ T={leaf s,.inl a,.inl b} := by
  rcases actual_leaf_profile layout tile s has noMid noOther with ⟨eq,p0,p1⟩|⟨i,w,wd,ext,eq⟩
  · have distinct : p (s,false)≠p (s,true) := fun h=>
      Bool.false_ne_true (congrArg Prod.snd (p.injective h))
    exact ⟨0,_,_,distinct,Or.inl ⟨rfl,rfl,rfl,wire s false p0,wire s true p1⟩,eq⟩
  · cases i
    · exact ⟨1,_,w,fun h=>ext.ne (congrArg Sum.inl h),
        Or.inr (Or.inl ⟨rfl,rfl,wire s false wd,old _ _ ext⟩),eq⟩
    · exact ⟨2,_,w,fun h=>ext.ne (congrArg Sum.inl h),
        Or.inr (Or.inr ⟨rfl,rfl,wire s true wd,old _ _ ext⟩),eq⟩

/-- The smaller graph's factor with midpoint deleted lifts through the
cross routing. Only cap wires actually used are required; the two
cross edges and absorbed edge must be genuine and retained. -/
theorem factor_of_two_leaves
    {C : SimpleGraph (V⊕Fin 3)} {H : SimpleGraph (V⊕Fin 9)} {p : Lane↪V}
    (layout : WeakLayout C p) (sh : Shape H)
    (ear : H.Adj (In 7) (In 8))
    (cross : ∀ i : Bool,H.Adj (Out (p (false,i))) (Out (p (true,i))))
    (old : ∀ a b : V,C.Adj (.inl a) (.inl b) → H.Adj (Out a) (Out b))
    (wire : ∀ s i : Bool,C.Adj (leaf s) (.inl (p (s,i))) →
      H.Adj (In (if i then nextSite s else firstSite s)) (Out (p (s,i))))
    (cap : FactorOn C (univ.erase mid)) :
    FactorOn H (univ.erase (Sum.inr 6)) := by
  let O : Finset (V⊕Fin 3) := univ.erase mid
  have lo : (leaf false : V⊕Fin 3)∈O := by simp [O,mid,leaf]
  have hi : (leaf true : V⊕Fin 3)∈O := by simp [O,mid,leaf]
  have noM : mid∉O := by simp [O]
  obtain ⟨A,aSub,al,tA,ra⟩ := factor_erase_one cap lo
  have na : mid∉A := fun m=>noM (aSub m)
  have nr : leaf true∉A := leaves_separate layout tA na al
  obtain ⟨B,bSub,bl,bt,rb⟩ := factor_erase_one ra (mem_sdiff.mpr ⟨hi,nr⟩)
  have nb : mid∉B := fun m=>noM (mem_sdiff.mp (bSub m)).1
  have nl : leaf false∉B := fun m=>(mem_sdiff.mp (bSub m)).2 al
  obtain ⟨i,a,b,ab,L,aShape⟩ := to_mode layout old wire tA false al na nr
  obtain ⟨j,c,d,cd,R,bShape⟩ := to_mode layout old wire bt true bl nb nl
  have separation (v : V) (ha : v=a∨v=b) (hb : v=c∨v=d) : False := by
    have s1 : Sum.inl v∈A := by rw [aShape]; rcases ha with rfl|rfl <;> simp
    have s2 : Sum.inl v∈B := by rw [bShape]; rcases hb with rfl|rfl <;> simp
    exact (mem_sdiff.mp (bSub s2)).2 s1
  let v : Fin 4↪V := ⟨tuple a b c d,tuple_inj ab cd separation⟩
  have packed : FactorOn H (liveFin V ∪ {Out a,Out b,Out c,Out d}) :=
    refill sh ear cross v L R
  let used : Finset (V⊕Fin 3) := insert mid (A∪B)
  have shape : gone used={Out a,Out b,Out c,Out d} := by
    ext z
    cases z with
    | inr z => simp [gone,mem_map]
    | inl z =>
      rw [gone_mem z]
      simp [used,aShape,bShape,mid,leaf,or_assoc,or_left_comm,or_comm]
  have rem : FactorOn C (univ \ used) := by
    have eq : ((O\A)\B) = univ\used := by
      ext z
      simp [O,used,not_or,and_assoc,and_left_comm,and_comm]
    exact eq ▸ rb
  refine stitch old (S:=used) (by simp [used]) (by simp [used,al])
    (by simp [used,bl]) rem ?_
  exact shape.symm ▸ packed

#print axioms factor_of_two_leaves
end
end KelmansCactus.AtomicBridge.ThetaCrossEarStitch
