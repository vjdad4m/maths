import ThetaFiveRing
import ThetaFiveModes

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaRootContactSplice
open SquareCap (FactorOn IsTile)
open ThetaFiveRing (Shape allRing ring ringMap outer refill_both_contacts refill_neighbor)
open ThetaFiveModes (Lane)
noncomputable section

def stem {V : Type*} : V⊕Unit := .inr ()

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

omit [Fintype V] in
private theorem ring_mem (i : Fin 7) :
    (Sum.inr i : V⊕Fin 7)∈allRing V ↔ i≠6 := by
  simp only [allRing,mem_map,mem_univ,true_and]
  constructor
  · rintro ⟨x,h⟩
    have hh : x.castSucc=i := Sum.inr_injective h
    have lx := x.isLt
    intro ii
    rw [ii] at hh
    have e : x.val=6 := congrArg Fin.val hh
    omega
  · intro h
    have li : i.val<6 := by
      have lb:=i.isLt
      have j : i.val ≠ 6 := fun e => h (Fin.ext e)
      omega
    exact ⟨⟨i.val,li⟩,rfl⟩

private def put (V : Type*) : (V⊕Unit) ↪ (V⊕Fin 7) :=
  (Function.Embedding.refl V).sumMap ⟨fun _=>6,fun _ _ _=>Subsingleton.elim _ _⟩

private def gone (S : Finset (V⊕Unit)) : Finset (V⊕Fin 7) :=
  ((univ : Finset V).filter (fun x=>Sum.inl x∈S)).map ⟨Sum.inl,Sum.inl_injective⟩

private theorem gone_mem {S : Finset (V⊕Unit)} (a : V) :
    outer a∈gone S ↔ Sum.inl a∈S := by simp [gone,mem_map]

/-- Stitch a tiling of consumed contacts plus the live ring with
the pullback of the factor on the cap exterior that remains. -/
private theorem stitch {C : SimpleGraph (V⊕Unit)} {H : SimpleGraph (V⊕Fin 7)}
    {S : Finset (V⊕Unit)}
    (old : ∀ a b : V,Sum.inl a∉S → Sum.inl b∉S →
      C.Adj (.inl a) (.inl b) → H.Adj (.inl a) (.inl b))
    (midIn : stem∈S)
    (rem : FactorOn C (univ \ S)) (fill : FactorOn H (allRing V ∪ gone S)) :
    FactorOn H (univ.erase (Sum.inr 6)) := by
  let f := put V
  have virtual (i : Unit) : (Sum.inr i : V⊕Unit)∈S := by cases i; exact midIn
  have stay : FactorOn H ((univ \ S).map f) :=
    factor_map_on f (by
      intro x xx y yy a
      cases x with
      | inr i => exact ((mem_sdiff.mp xx).2 (virtual i)).elim
      | inl u =>
        cases y with
        | inr i => exact ((mem_sdiff.mp yy).2 (virtual i)).elim
        | inl v => exact old u v (mem_sdiff.mp xx).2 (mem_sdiff.mp yy).2 a) rem
  have leftIn (a : V) : outer a∈((univ \ S).map f) ↔ Sum.inl a∉S := by
    simp [f,put,mem_map]
  have innerNo (i : Fin 7) : (Sum.inr i : V⊕Fin 7)∉((univ \ S).map f) := by
    intro h
    obtain ⟨x,m,h⟩ := mem_map.mp h
    cases x with
    | inr j => exact (mem_sdiff.mp m).2 (virtual j)
    | inl j => exact Sum.noConfusion (show (Sum.inl j : V⊕Fin 7)=Sum.inr i from h)
  have innerGone (i : Fin 7) : (Sum.inr i : V⊕Fin 7)∉gone S := by
    simp [gone,mem_map]
  have outerRing (a : V) : outer a∉allRing V := by
    simp [allRing,ringMap,mem_map]
  have apart : Disjoint ((univ \ S).map f) (allRing V ∪ gone S) := by
    rw [disjoint_left]
    intro x h g
    cases x with
    | inr i => exact innerNo i h
    | inl a =>
      rcases mem_union.mp g with ring|gone
      · exact outerRing a ring
      · exact (leftIn a).mp h ((gone_mem a).mp gone)
  have cover : ((univ \ S).map f) ∪ (allRing V ∪ gone S) =
      (univ : Finset (V⊕Fin 7)).erase (Sum.inr 6) := by
    ext x
    cases x with
    | inr i => simp [innerNo i,innerGone i,ring_mem]
    | inl a =>
      have t : (Sum.inl a : V⊕Fin 7) ≠ Sum.inr 6 := by simp
      simp only [mem_union,leftIn,outerRing,gone_mem,mem_erase,mem_univ,and_true,t]
      tauto
  exact cover ▸ factor_disjUnion stay fill apart

omit [Fintype V] in
private theorem stem_profile {C : SimpleGraph (V⊕Unit)} {p : Lane↪V} (s : Bool)
    (layout : ∀ x,C.Adj stem x → x=.inl (p (!s,false)) ∨ x=.inl (p (!s,true)))
    {S : Finset (V⊕Unit)} (tile : IsTile C S) (has : stem∈S) :
    (S={stem,.inl (p (!s,false)),.inl (p (!s,true))}) ∨
      ∃ i : Bool,∃ w : V,C.Adj (.inl (p (!s,i))) (.inl w) ∧
        S={stem,.inl (p (!s,i)),.inl w} := by
  obtain ⟨sz,c,hc,star⟩ := tile
  by_cases cm : c=stem
  · subst c
    left
    apply eq_of_subset_of_card_le
    · intro x hx
      by_cases xm : x=stem
      · simp [xm]
      · rcases layout x (star x hx xm) with h|h
        · simp [h]
        · simp [h]
    · have ne : p (!s,false)≠p (!s,true) := fun e=>
        Bool.false_ne_true (congrArg Prod.snd (p.injective e))
      rw [sz,triple_card (by simp [stem]) (by simp [stem]) (by simp [ne])]
  have where_c := layout c (star stem has (fun e=>cm e.symm)).symm
  have one (i : Bool) (e : c=Sum.inl (p (!s,i))) :
      ∃ w : V,C.Adj (.inl (p (!s,i))) (.inl w) ∧
        S={stem,.inl (p (!s,i)),.inl w} := by
    obtain ⟨z,zs,zm,zc,shape⟩ := third sz has (e ▸ hc) (by simp [stem])
    cases z with
    | inr t =>
      cases t
      exact (zm rfl).elim
    | inl w =>
      exact ⟨w,e ▸ star _ zs (fun h=>zc (h.trans e)),shape⟩
  exact Or.inr (where_c.elim (fun e=>⟨false,one false e⟩) (fun e=>⟨true,one true e⟩))

/-- The artificial edge incident to the removed exterior terminal
never survives to the exterior tiling; put that vertex back solely via
its true live ring wire. -/
theorem lift_after_removed_terminal {C : SimpleGraph (V⊕Unit)} {H : SimpleGraph (V⊕Fin 7)}
    {p : Lane↪V} (s i : Bool) (sh : Shape H p)
    (layout : ∀ x,C.Adj stem x → x=.inl (p (!s,false)) ∨ x=.inl (p (!s,true)))
    (old : ∀ x y : V,x≠p (s,i) → y≠p (s,i) →
      C.Adj (.inl x) (.inl y) → H.Adj (outer x) (outer y))
    (cap : FactorOn C (univ.erase (Sum.inl (p (s,i))))) :
    FactorOn H (univ.erase (Sum.inr 6)) := by
  let a := p (s,i)
  let O : Finset (V⊕Unit) := univ.erase (Sum.inl a)
  obtain ⟨A,sub,has,tile,rest⟩ := factor_erase_one cap
    (show (stem : V⊕Unit)∈O from by simp [O,stem])
  let used : Finset (V⊕Unit) := insert (Sum.inl a) A
  have rem : FactorOn C (univ\used) := by
    have eq : O\A=univ\used := by
      ext x; simp [O,used,not_or,and_assoc,and_left_comm,and_comm]
    exact eq ▸ rest
  refine stitch (S:=used) ?_ (by simp [used,has]) rem ?_
  · intro x y nx ny e
    exact old x y (fun h=>nx (by simp [used,a,h])) (fun h=>ny (by simp [used,a,h])) e
  rcases stem_profile s layout tile has with yes|⟨j,w,e,yes⟩
  · have f := refill_both_contacts sh s i
    have gon : gone used={outer a,outer (p (!s,i)),outer (p (!s,!i))} := by
      ext z
      cases z with
      | inr z => simp [gone,mem_map]
      | inl z =>
        rw [gone_mem z]
        cases i <;> simp [used,a,yes,stem,or_assoc,or_left_comm,or_comm]
    exact gon.symm ▸ f
  · let b := p (!s,j)
    have bA : Sum.inl b∈A := by rw [yes]; simp [b]
    have wA : Sum.inl w∈A := by rw [yes]; simp
    have bn : b≠a := by simpa [O] using (sub bA)
    have wn : w≠a := by simpa [O] using (sub wA)
    have f := refill_neighbor sh s i j wn.symm (old b w bn wn e)
    have gon : gone used={outer a,outer b,outer w} := by
      ext z
      cases z with
      | inr z => simp [gone,mem_map]
      | inl z =>
        rw [gone_mem z]
        simp [used,yes,b,stem,or_assoc,or_left_comm,or_comm]
    exact gon.symm ▸ f

#print axioms stem_profile
#print axioms lift_after_removed_terminal
end
end KelmansCactus.AtomicBridge.ThetaRootContactSplice
