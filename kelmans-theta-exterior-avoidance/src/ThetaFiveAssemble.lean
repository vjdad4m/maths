import ThetaFiveRing
import ThetaFiveModes

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaFiveAssemble
open SquareCap (FactorOn IsTile)
open ThetaFiveRing (Shape allRing ring ringMap outer refill_both_contacts refill_neighbor)
open ThetaFiveModes (Lane Layout mid leaf mid_profile leaf_profile)
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

private theorem factor_single {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} (h : IsTile G S) : FactorOn G S := by
  refine ⟨{S},?_,?_,by simp⟩
  · intro A ha
    obtain rfl := mem_singleton.mp ha
    exact h
  · intro A ha B hb ne
    exact (ne ((mem_singleton.mp ha).trans (mem_singleton.mp hb).symm)).elim

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

private theorem tile_path {T : Type*} [DecidableEq T]
    {G : SimpleGraph T} {x y z : T} (xy : G.Adj x y) (yz : G.Adj y z) (xz : x ≠ z) :
    IsTile G {x,y,z} := by
  refine ⟨triple_card xy.ne xz yz.ne,y,by simp,?_⟩
  intro w hw ne
  simp only [mem_insert,mem_singleton] at hw
  rcases hw with rfl|rfl|rfl
  · exact xy.symm
  · exact (ne rfl).elim
  · exact yz



variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem ring_distinct (a b : Fin 6) (ab : a≠b) :
    ring (V:=V) a ≠ ring b := fun h=>ab ((ringMap V).injective h)

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

omit [Fintype V] in
private theorem ring_only {H : SimpleGraph (V⊕Fin 7)} {p : Lane↪V} (s : Shape H p) :
    FactorOn H (allRing V) := by
  let T : Finset (V⊕Fin 7) := {ring 0,ring 1,ring 2}
  let U : Finset (V⊕Fin 7) := {ring 3,ring 4,ring 5}
  have t : IsTile H T := tile_path (s.cycle 0 1 (by decide)) (s.cycle 1 2 (by decide))
    (ring_distinct _ _ (by decide))
  have u : IsTile H U := tile_path (s.cycle 3 4 (by decide)) (s.cycle 4 5 (by decide))
    (ring_distinct _ _ (by decide))
  have sep : Disjoint T U := by
    simp only [T,U,disjoint_left,mem_insert,mem_singleton]
    intro z a b
    rcases a with rfl|rfl|rfl <;> rcases b with e|e|e
    all_goals exact (ring_distinct _ _ (by decide)) e
  have joined := factor_disjUnion (factor_single t) (factor_single u) sep
  have cover : T∪U = allRing V := by
    ext x
    cases x with
    | inl x => simp [T,U,allRing,ringMap,mem_map]
    | inr i =>
      rw [ring_mem]
      have chk : ∀ j : Fin 7,j=0∨j=1∨j=2∨j=3∨j=4∨j=5 ↔ j≠6 := by decide
      simp [T,U]
      have q := chk i
      tauto
  exact cover ▸ joined

private def put (V : Type*) : (V⊕Fin 3) ↪ (V⊕Fin 7) :=
  (Function.Embedding.refl V).sumMap ⟨fun i=>⟨i.val,by have h:=i.isLt; omega⟩,
    fun i j eq=>Fin.ext (congrArg (fun z : Fin 7=>z.val) eq)⟩

private def gone (S : Finset (V⊕Fin 3)) : Finset (V⊕Fin 7) :=
  ((univ : Finset V).filter (fun x=>Sum.inl x∈S)).map ⟨Sum.inl,Sum.inl_injective⟩

private theorem gone_mem {S : Finset (V⊕Fin 3)} (a : V) : outer a∈gone S ↔ Sum.inl a∈S := by
  simp [gone,mem_map]

omit [Fintype V] [DecidableEq V] in
private theorem all_virtual (v : Fin 3) :
    (Sum.inr v : V⊕Fin 3)=mid ∨ Sum.inr v=leaf (V:=V) false ∨ Sum.inr v=leaf (V:=V) true := by
  have k : ∀ j : Fin 3,j=0∨j=1∨j=2 := by decide
  rcases k v with rfl|rfl|rfl <;> simp [mid,leaf]

/-- Stitch a tiling of consumed contacts plus the live ring with
the pullback of the factor on the cap exterior that remains. -/
private theorem stitch {C : SimpleGraph (V⊕Fin 3)} {H : SimpleGraph (V⊕Fin 7)}
    (old : ∀ a b : V,C.Adj (.inl a) (.inl b) → H.Adj (.inl a) (.inl b))
    {S : Finset (V⊕Fin 3)}
    (midIn : mid∈S) (lIn : leaf false∈S) (rIn : leaf true∈S)
    (rem : FactorOn C (univ \ S)) (fill : FactorOn H (allRing V ∪ gone S)) :
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

omit [Fintype V] [DecidableEq V] in
private theorem others (s : Bool) :
    leaf (V:=V) (!s) ≠ mid ∧ leaf (V:=V) (!s) ≠ leaf s := by
  cases s <;> simp [mid,leaf]

/-- End-to-end exact factor transfer from the cap with its dead
midpoint wire suppressed. The cap's exterior has the forbidden edge
already removed; reassembly never needs another exterior edge. -/
theorem factor_of_blocked_cap
    {C : SimpleGraph (V⊕Fin 3)} {H : SimpleGraph (V⊕Fin 7)} {p : Lane↪V}
    (layout : Layout C p) (shape : Shape H p)
    (old : ∀ a b : V,C.Adj (.inl a) (.inl b) → H.Adj (.inl a) (.inl b))
    (cap : FactorOn C univ) :
    FactorOn H (univ.erase (Sum.inr 6)) := by
  obtain ⟨T,_,inT,tile,rem⟩ := factor_erase_one cap (show mid ∈ (univ : Finset (V⊕Fin 3)) from by simp)
  rcases mid_profile layout tile inT with straight|⟨s,i,hT⟩
  · refine stitch old inT (by simp [straight]) (by simp [straight]) rem ?_
    have e : gone T=∅ := by
      ext a
      cases a <;> simp [gone,mem_map,straight,mid,leaf]
    simpa [e] using ring_only shape
  · have live : leaf (!s)∈(univ \ T) := by
      have h1 := (others (V:=V) s).1
      have h2 := (others (V:=V) s).2
      refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
      rw [hT]
      simp only [mem_insert,mem_singleton]
      rintro (h|h|h)
      · exact h1 h
      · exact h2 h
      · exact Sum.noConfusion (show (leaf (!s) : V⊕Fin 3)=Sum.inl (p (s,i)) from h)
    obtain ⟨U,inc,opp,uTile,rest⟩ := factor_erase_one rem live
    have notMid : mid∉U := fun h=>(mem_sdiff.mp (inc h)).2 inT
    have notS : leaf s∉U := fun h=>(mem_sdiff.mp (inc h)).2 (by simp [hT])
    have notOther : leaf (!(!s))∉U := by simpa using notS
    let S := T ∪ U
    have min : mid∈S := mem_union_left _ inT
    have lIn : leaf false∈S := by
      cases s
      · exact mem_union_left _ (by simp [hT])
      · exact mem_union_right _ opp
    have rIn : leaf true∈S := by
      cases s
      · exact mem_union_right _ opp
      · exact mem_union_left _ (by simp [hT])
    have rr : FactorOn C (univ \ S) := by
      have ee : ((univ \ T) \ U) = (univ \ S) := by
        ext a
        simp [S,not_or,and_assoc]
      exact ee ▸ rest
    rcases leaf_profile layout uTile (!s) opp notMid notOther with hU|⟨j,w,nw,hU⟩
    · refine stitch old min lIn rIn rr ?_
      have eq : gone S = {outer (p (s,i)),outer (p ((!s),i)),outer (p ((!s),(!i)))} := by
        ext a
        cases a with
        | inr a => simp [gone,mem_map]
        | inl a =>
          rw [gone_mem a]
          cases i <;> simp [S,hT,hU,mid,leaf,or_assoc,or_left_comm,or_comm]
      exact eq.symm ▸ refill_both_contacts shape s i
    · have away : p (s,i)≠w := by
        intro eq
        have wU : (Sum.inl w : V⊕Fin 3)∈U := by simp [hU]
        have wT : (Sum.inl w : V⊕Fin 3)∈T := by simp [hT,←eq]
        exact (mem_sdiff.mp (inc wU)).2 wT
      refine stitch old min lIn rIn rr ?_
      have eq : gone S = {outer (p (s,i)),outer (p ((!s),j)),outer w} := by
        ext a
        cases a with
        | inr a => simp [gone,mem_map]
        | inl a =>
          rw [gone_mem a]
          simp [S,hT,hU,mid,leaf,or_assoc,or_left_comm,or_comm]
      exact eq.symm ▸ refill_neighbor shape s i j away (old _ _ nw)

#print axioms factor_of_blocked_cap
end
end KelmansCactus.AtomicBridge.ThetaFiveAssemble
