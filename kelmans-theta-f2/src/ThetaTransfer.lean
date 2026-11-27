import PentagonTransfer

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaTransfer
open SquareCap (FactorOn HasFactor IsTile factor_map)
open PentagonTransfer (stub stubGraph stub_tile_cases)
noncomputable section

variable {V : Type*}

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

private abbrev out (v : V) : V⊕Fin 7 := Sum.inl v
private abbrev ring (v : Fin 7) : V⊕Fin 7 := Sum.inr v

private theorem ring_ne (i j : Fin 7) (h : i ≠ j) : ring (V:=V) i ≠ ring j :=
  fun e => h (Sum.inr_injective e)

/-- Only the path on six surviving vertices and the three specified
wires need exist in the target. The omitted edge (5,0) is not used
in any branch. -/
structure Target (G : SimpleGraph V) (H : SimpleGraph (V ⊕ Fin 7)) (z p q : V) : Prop where
  e01 : H.Adj (ring 0) (ring 1)
  e12 : H.Adj (ring 1) (ring 2)
  e23 : H.Adj (ring 2) (ring 3)
  e34 : H.Adj (ring 3) (ring 4)
  e45 : H.Adj (ring 4) (ring 5)
  bz : H.Adj (out z) (ring 1)
  bp : H.Adj (out p) (ring 2)
  bq : H.Adj (out q) (ring 5)
  old : ∀ v w,G.Adj v w → H.Adj (out v) (out w)

private def embed (V : Type*) : (V⊕Unit) ↪ (V⊕Fin 7) where
  toFun := Sum.elim Sum.inl (fun _ => Sum.inr 6)
  inj' := by
    intro a b e
    cases a with
    | inl x => cases b with
      | inl y => exact congrArg Sum.inl (Sum.inl_injective e)
      | inr y => exact Sum.noConfusion (show Sum.inl x = Sum.inr (6:Fin 7) from e)
    | inr x => cases b with
      | inl y => exact Sum.noConfusion (show Sum.inr (6:Fin 7) = Sum.inl y from e)
      | inr y => cases x; cases y; rfl

private def surviving (V : Type*) [DecidableEq V] : Finset (V ⊕ Fin 7) :=
  {ring 0,ring 1,ring 2,ring 3,ring 4,ring 5}

private theorem mem_surviving [DecidableEq V] (i : Fin 7) :
    ring (V:=V) i ∈ surviving V ↔ i ≠ 6 := by
  have mask : ∀ i : Fin 7,i=0∨i=1∨i=2∨i=3∨i=4∨i=5 ↔ i≠6 := by decide
  simpa [surviving] using mask i

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

private theorem replace_theta_stub [DecidableEq V]
    {G : SimpleGraph V} {H : SimpleGraph (V ⊕ Fin 7)} {z p q : V}
    (shape : Target G H z p q) (pq : p ≠ q)
    {T : Finset (V⊕Unit)} (tile : IsTile (stubGraph G p q) T)
    (stubIn : stub ∈ T) (avoid : Sum.inl z ∉ T) :
    FactorOn H ((((T \ {stub}).map (embed V)) ∪ {out z}) ∪ surviving V) := by
  have ztile : IsTile H {out z,ring 1,ring 0} := tile_path shape.bz shape.e01.symm (by simp)
  have away {v : V} (vt : Sum.inl v ∈ T) : z ≠ v := fun e => avoid (e.symm ▸ vt)
  have rep {a b c d e f : V⊕Fin 7} (x : IsTile H {a,b,c}) (y : IsTile H {d,e,f})
      (apart : Disjoint ({a,b,c} : Finset (V⊕Fin 7)) {d,e,f})
      (avoidZ : Disjoint ({out z,ring 1,ring 0} : Finset (V⊕Fin 7)) ({a,b,c} ∪ {d,e,f})) :
      FactorOn H ({out z,ring 1,ring 0} ∪ ({a,b,c} ∪ {d,e,f})) :=
    factor_disjUnion (factor_single ztile) (factor_disjUnion (factor_single x) (factor_single y) apart) avoidZ
  rcases stub_tile_cases pq tile stubIn with eq | ⟨w,adj,eq⟩ | ⟨w,adj,eq⟩
  · have zp : z ≠ p := away (eq.symm ▸ by simp)
    have zq : z ≠ q := away (eq.symm ▸ by simp)
    let A : Finset (V⊕Fin 7) := {out p,ring 2,ring 3}
    let B : Finset (V⊕Fin 7) := {ring 4,ring 5,out q}
    have apart : Disjoint A B := by simp [A,B,disjoint_left,pq]
    have zsep : Disjoint ({out z,ring 1,ring 0} : Finset (V⊕Fin 7)) (A∪B) := by
      simp [A,B,disjoint_left,zp,zq]
    have final := rep (tile_path shape.bp shape.e23 (by simp))
      (tile_path shape.e45 shape.bq.symm (by simp)) apart zsep
    have sup : ({out z,ring 1,ring 0} : Finset (V⊕Fin 7)) ∪ (A∪B) =
        ((((T \ {stub}).map (embed V)) ∪ {out z}) ∪ surviving V) := by
      rw [eq]
      ext x
      cases x <;> simp [A,B,surviving,embed,mem_map,or_assoc,or_left_comm,or_comm]
    exact sup ▸ final
  · have zp : z ≠ p := away (eq.symm ▸ by simp)
    have zw : z ≠ w := away (eq.symm ▸ by simp)
    let A : Finset (V⊕Fin 7) := {out w,out p,ring 2}
    let B : Finset (V⊕Fin 7) := {ring 3,ring 4,ring 5}
    have apart : Disjoint A B := by simp [A,B,disjoint_left]
    have zsep : Disjoint ({out z,ring 1,ring 0} : Finset (V⊕Fin 7)) (A∪B) := by
      simp [A,B,disjoint_left,zp,zw]
    have final := rep (tile_path (shape.old _ _ adj.symm) shape.bp (by simp))
      (tile_path shape.e34 shape.e45 (ring_ne _ _ (by decide))) apart zsep
    have sup : ({out z,ring 1,ring 0} : Finset (V⊕Fin 7)) ∪ (A∪B) =
        ((((T \ {stub}).map (embed V)) ∪ {out z}) ∪ surviving V) := by
      rw [eq]
      ext x
      cases x <;> simp [A,B,surviving,embed,mem_map,or_assoc,or_left_comm,or_comm]
    exact sup ▸ final
  · have zq : z ≠ q := away (eq.symm ▸ by simp)
    have zw : z ≠ w := away (eq.symm ▸ by simp)
    let A : Finset (V⊕Fin 7) := {ring 2,ring 3,ring 4}
    let B : Finset (V⊕Fin 7) := {ring 5,out q,out w}
    have apart : Disjoint A B := by simp [A,B,disjoint_left]
    have zsep : Disjoint ({out z,ring 1,ring 0} : Finset (V⊕Fin 7)) (A∪B) := by
      simp [A,B,disjoint_left,zq,zw]
    have final := rep (tile_path shape.e23 shape.e34 (ring_ne _ _ (by decide)))
      (tile_path shape.bq.symm (shape.old _ _ adj) (by simp)) apart zsep
    have sup : ({out z,ring 1,ring 0} : Finset (V⊕Fin 7)) ∪ (A∪B) =
        ((((T \ {stub}).map (embed V)) ∪ {out z}) ∪ surviving V) := by
      rw [eq]
      ext x
      cases x <;> simp [A,B,surviving,embed,mem_map,or_assoc,or_left_comm,or_comm]
    exact sup ▸ final

/-- Exact finite-profile transfer at the theta, independent of cap
geometry. Either the ordinary exterior factor or the one-stub
fallback deleting the specified middle contact suffices. -/
theorem theta_factor_of_two_modes [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {H : SimpleGraph (V ⊕ Fin 7)} {z p q : V}
    (shape : Target G H z p q) (pq : p ≠ q)
    (mode : HasFactor G ∨ FactorOn (stubGraph G p q) (univ.erase (Sum.inl z))) :
    FactorOn H (univ.erase (Sum.inr 6)) := by
  rcases mode with straight | via
  · let e : V ↪ V⊕Fin 7 := ⟨Sum.inl,Sum.inl_injective⟩
    have extFactor := factor_map e shape.old straight
    let A : Finset (V ⊕ Fin 7) := {ring 0,ring 1,ring 2}
    let B : Finset (V ⊕ Fin 7) := {ring 3,ring 4,ring 5}
    have a : IsTile H A := tile_path shape.e01 shape.e12 (ring_ne _ _ (by decide))
    have b : IsTile H B := tile_path shape.e34 shape.e45 (ring_ne _ _ (by decide))
    have apart : Disjoint A B := by simp [A,B,disjoint_left]
    have d : Disjoint (univ.map e) (A∪B) := by simp [e,A,B,disjoint_left,mem_map]
    have eq : univ.map e ∪ (A∪B) = (univ : Finset (V⊕Fin 7)).erase (ring 6) := by
      ext x
      cases x with
      | inl v => simp [e,mem_map]
      | inr v =>
        have ee : A∪B=surviving V := by
          ext y
          simp [A,B,surviving,or_assoc,or_left_comm,or_comm]
        rw [ee]
        simp [mem_surviving,e,mem_map]
    exact eq ▸ factor_disjUnion extFactor (factor_disjUnion (factor_single a) (factor_single b) apart) d
  · let F := (univ : Finset (V⊕Unit)).erase (Sum.inl z)
    have st : (stub : V⊕Unit) ∈ F := by simp [F]
    obtain ⟨T,inc,used,tile,rest⟩ := factor_erase_one via st
    have noZ : Sum.inl z ∉ T := fun h => (mem_erase.mp (inc h)).1 rfl
    let e := embed V
    let L := (F \ T).map e
    let R := (((T \ {stub}).map e) ∪ {out z}) ∪ surviving V
    have rem : FactorOn H L := factor_map_on e (by
      intro x hx y hy edge
      have nx := (mem_sdiff.mp hx).2
      have ny := (mem_sdiff.mp hy).2
      cases x with
      | inr a => cases a; exact (nx used).elim
      | inl a => cases y with
        | inr b => cases b; exact (ny used).elim
        | inl b => exact shape.old a b edge) rest
    have refill := replace_theta_stub shape pq tile used noZ
    have apart : Disjoint L R := by
      apply disjoint_left.mpr
      intro x hL hR
      obtain ⟨a,ha,eax⟩ := mem_map.mp hL
      have haT := (mem_sdiff.mp ha).2
      rcases mem_union.mp hR with p|r
      · rcases mem_union.mp p with pin|zz
        · obtain ⟨b,hb,ebx⟩ := mem_map.mp pin
          have eq := e.injective (eax.trans ebx.symm)
          exact haT (eq ▸ (mem_sdiff.mp hb).1)
        · have az : a = Sum.inl z := e.injective (eax.trans (mem_singleton.mp zz))
          exact (mem_erase.mp (mem_sdiff.mp ha).1).1 az
      · cases a with
        | inr a => cases a; exact haT used
        | inl a =>
          rw [←eax] at r
          simp [e,embed,surviving] at r
    have cover : L ∪ R = (univ : Finset (V⊕Fin 7)).erase (ring 6) := by
      ext x
      cases x with
      | inl v =>
        by_cases zz : v=z
        · subst v
          simp [R]
        by_cases vT : Sum.inl v∈T
        · have yes : out v∈(T \ {stub}).map e :=
            mem_map.mpr ⟨_,mem_sdiff.mpr ⟨vT,by simp⟩,rfl⟩
          simp [R,yes]
        · have yes : out v∈L := mem_map.mpr ⟨_,mem_sdiff.mpr
            ⟨mem_erase.mpr ⟨by simpa using zz,mem_univ _⟩,vT⟩,rfl⟩
          simp [yes]
      | inr i =>
        have notL : ring i ∉ L := by
          intro h
          obtain ⟨a,ha,eq⟩ := mem_map.mp h
          cases a with
          | inr a => cases a; exact (mem_sdiff.mp ha).2 used
          | inl a => exact Sum.noConfusion (show out a = ring i from eq)
        have notR : ring i ∉ (T \ {stub}).map e := by
          intro h
          obtain ⟨a,ha,eq⟩ := mem_map.mp h
          cases a with
          | inr a => cases a; exact (mem_sdiff.mp ha).2 (by simp)
          | inl a => exact Sum.noConfusion (show out a = ring i from eq)
        simp [R,notL,notR,mem_surviving]
    exact cover ▸ factor_disjUnion rem refill apart

#print axioms theta_factor_of_two_modes

end
end KelmansCactus.AtomicBridge.ThetaTransfer
