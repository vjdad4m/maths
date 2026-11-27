import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.PentagonTransfer
open SquareCap (IsTile FactorOn HasFactor)
noncomputable section

variable {V : Type*}

def stubAdj (G : SimpleGraph V) (p q : V) : V⊕Unit → V⊕Unit → Prop
  | Sum.inl x, Sum.inl y => G.Adj x y
  | Sum.inl x, Sum.inr _ => x = p ∨ x = q
  | Sum.inr _, Sum.inl x => x = p ∨ x = q
  | Sum.inr _, Sum.inr _ => False

def stubGraph (G : SimpleGraph V) (p q : V) : SimpleGraph (V⊕Unit) where
  Adj := stubAdj G p q
  symm := by intro a b h; cases a <;> cases b <;> first | exact h | exact G.symm h
  loopless := by intro a; cases a; exact G.loopless _; exact id

abbrev stub : V⊕Unit := Sum.inr ()

private theorem triple_card {T : Type*} [DecidableEq T] {a b c : T}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    ({a,b,c} : Finset T).card = 3 := by
  simp [card_insert_of_not_mem,ab,ac,bc]

/-- A tile containing the last virtual cap vertex has precisely
three possibilities: the virtual vertex centers both wires,
or is a leaf through one wire with one further outside vertex. -/
theorem stub_tile_cases [DecidableEq V] {G : SimpleGraph V} {p q : V} (ne : p ≠ q)
    {T : Finset (V⊕Unit)} (tile : IsTile (stubGraph G p q) T) (used : stub ∈ T) :
    T = {stub,Sum.inl p,Sum.inl q} ∨
      (∃ w,G.Adj p w ∧ T = {stub,Sum.inl p,Sum.inl w}) ∨
      (∃ w,G.Adj q w ∧ T = {stub,Sum.inl q,Sum.inl w}) := by
  obtain ⟨cd,o,oin,edges⟩ := tile
  cases o with
  | inr u =>
    cases u
    have all : T ⊆ {stub,Sum.inl p,Sum.inl q} := by
      intro x hx
      cases x with
      | inr xx => cases xx; simp
      | inl xx =>
        have t := edges (Sum.inl xx) hx (by simp)
        change xx=p ∨ xx=q at t
        rcases t with rfl|rfl <;> simp
    left
    apply eq_of_subset_of_card_le all
    rw [cd,triple_card (by simp) (by simp) (by simpa using ne)]
  | inl o =>
    have spq : o = p ∨ o = q := edges stub used (by simp)
    have n : ({stub,Sum.inl o} : Finset (V⊕Unit)).card = 2 := by
      simp [card_insert_of_not_mem]
    obtain ⟨v,hv,miss⟩ := exists_mem_not_mem_of_card_lt_card (by omega :
      ({stub,Sum.inl o} : Finset (V⊕Unit)).card < T.card)
    cases v with
    | inr t => cases t; simp at miss
    | inl v =>
      have vo : v ≠ o := by simpa using miss
      have ov : G.Adj o v := edges (Sum.inl v) hv (by simpa using vo)
      have subset : ({stub,Sum.inl o,Sum.inl v} : Finset (V⊕Unit)) ⊆ T := by
        intro z hz
        simp only [mem_insert,mem_singleton] at hz
        rcases hz with rfl|rfl|rfl <;> assumption
      have equal := (eq_of_subset_of_card_le subset (by
        rw [cd,triple_card (by simp) (by simp) (by simpa using vo.symm)])).symm
      rcases spq with rfl|rfl
      · exact Or.inr (Or.inl ⟨v,ov,equal⟩)
      · exact Or.inr (Or.inr ⟨v,ov,equal⟩)

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

private theorem factor_erase_tile {T : Type*} [DecidableEq T] [Fintype T]
    {G : SimpleGraph T} (f : HasFactor G) (x : T) :
    ∃ S, x ∈ S ∧ IsTile G S ∧ FactorOn G ((univ : Finset T) \ S) := by
  obtain ⟨P,p,d,u⟩ := f
  have m : x ∈ P.biUnion id := u ▸ mem_univ x
  obtain ⟨s,hs,xs⟩ := mem_biUnion.mp m
  refine ⟨s,xs,p s hs,P.erase s,?_,?_,?_⟩
  · intro t ht
    exact p t (mem_erase.mp ht).2
  · intro a ha b hb
    exact d a (mem_erase.mp ha).2 b (mem_erase.mp hb).2
  · ext v
    constructor
    · intro hv
      obtain ⟨t,ht,vt⟩ := mem_biUnion.mp hv
      exact mem_sdiff.mpr ⟨mem_univ _,fun vs =>
        disjoint_left.mp (d t (mem_erase.mp ht).2 s hs (mem_erase.mp ht).1) vt vs⟩
    · intro hv
      have vP : v ∈ P.biUnion id := u ▸ mem_univ _
      obtain ⟨t,ht,vt⟩ := mem_biUnion.mp vP
      have nq : t ≠ s := fun e => (mem_sdiff.mp hv).2 (e ▸ vt)
      exact mem_biUnion.mpr ⟨t,mem_erase.mpr ⟨nq,ht⟩,vt⟩

private def embed (V : Type*) : (V⊕Unit) ↪ (V⊕Fin 5) where
  toFun := Sum.elim Sum.inl (fun _ => Sum.inr 0)
  inj' := by
    intro a b e
    cases a with
    | inl x =>
      cases b with
      | inl y => exact congrArg Sum.inl (Sum.inl_injective e)
      | inr y => exact Sum.noConfusion (show Sum.inl x = Sum.inr (0:Fin 5) from e)
    | inr x =>
      cases b with
      | inl y => exact Sum.noConfusion (show Sum.inr (0:Fin 5) = Sum.inl y from e)
      | inr y => cases x; cases y; rfl

private abbrev out (v : V) : V⊕Fin 5 := Sum.inl v
private abbrev ring (v : Fin 5) : V⊕Fin 5 := Sum.inr v

private def remainingCorners (V : Type*) [DecidableEq V] : Finset (V⊕Fin 5) :=
  {ring 1, ring 2, ring 3, ring 4}

private theorem ring_mem_corners [DecidableEq V] (i : Fin 5) : ring (V:=V) i ∈ remainingCorners V ↔ i ≠ 0 := by
  have listing : ∀ i : Fin 5, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ↔ i ≠ 0 := by decide
  simpa [remainingCorners] using listing i

/-- Every mode of the virtual degree-two vertex can be replaced by
one or two genuine tiles after deleting the pentagon corner 0.
Only the wires at corners 1 and 4 are used. -/
theorem replace_stub_tile [DecidableEq V] {G : SimpleGraph V} {p q : V} (ne : p ≠ q)
    {T : Finset (V⊕Unit)} (tile : IsTile (stubGraph G p q) T) (used : stub ∈ T)
    (H : SimpleGraph (V⊕Fin 5))
    (e12 : H.Adj (ring 1) (ring 2)) (e23 : H.Adj (ring 2) (ring 3))
    (e34 : H.Adj (ring 3) (ring 4))
    (pw : H.Adj (out p) (ring 1)) (qw : H.Adj (out q) (ring 4))
    (old : ∀ v w,G.Adj v w → H.Adj (out v) (out w)) :
    FactorOn H (((T \ {stub}).map (embed V)) ∪ remainingCorners V) := by
  have rep {a b c d e f : V⊕Fin 5} (x : IsTile H {a,b,c}) (y : IsTile H {d,e,f})
      (apart : Disjoint ({a,b,c} : Finset (V⊕Fin 5)) {d,e,f}) :
      FactorOn H ({a,b,c} ∪ {d,e,f}) :=
    factor_disjUnion (factor_single x) (factor_single y) apart
  rcases stub_tile_cases ne tile used with eq | ⟨w,adj,eq⟩ | ⟨w,adj,eq⟩
  · let L : Finset (V⊕Fin 5) := {out p,ring 1,ring 2}
    let R : Finset (V⊕Fin 5) := {ring 3,ring 4,out q}
    have apart : Disjoint L R := by simp [L,R,disjoint_left,ne]
    have repl := rep (tile_path pw e12 (by simp)) (tile_path e34 qw.symm (by simp)) apart
    have support : L ∪ R = ((T \ {stub}).map (embed V)) ∪ remainingCorners V := by
      rw [eq]
      ext z
      cases z <;> simp [L,R,remainingCorners,embed,mem_map,or_assoc,or_left_comm,or_comm]
    exact support ▸ repl
  · let L : Finset (V⊕Fin 5) := {out w,out p,ring 1}
    let R : Finset (V⊕Fin 5) := {ring 2,ring 3,ring 4}
    have apart : Disjoint L R := by simp [L,R,disjoint_left]
    have repl := rep (tile_path (old _ _ adj.symm) pw (by simp))
      (tile_path e23 e34 (fun h => (by decide : (2:Fin 5) ≠ 4) (Sum.inr_injective h))) apart
    have support : L ∪ R = ((T \ {stub}).map (embed V)) ∪ remainingCorners V := by
      rw [eq]
      ext z
      cases z <;> simp [L,R,remainingCorners,embed,mem_map,or_assoc,or_left_comm,or_comm]
    exact support ▸ repl
  · let L : Finset (V⊕Fin 5) := {ring 1,ring 2,ring 3}
    let R : Finset (V⊕Fin 5) := {ring 4,out q,out w}
    have apart : Disjoint L R := by simp [L,R,disjoint_left]
    have repl := rep (tile_path e12 e23 (fun h => (by decide : (1:Fin 5) ≠ 3) (Sum.inr_injective h)))
      (tile_path qw.symm (old _ _ adj) (by simp)) apart
    have support : L ∪ R = ((T \ {stub}).map (embed V)) ∪ remainingCorners V := by
      rw [eq]
      ext z
      cases z <;> simp [L,R,remainingCorners,embed,mem_map,or_assoc,or_left_comm,or_comm]
    exact support ▸ repl

/-- Sound global transfer from the one-stub exterior factor. The
target may omit every non-used wire and every edge incident to the
deleted vertex. No assumption on the other three wires is needed. -/
theorem close_pentagon_at_zero [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {p q : V} (ne : p ≠ q) (f : HasFactor (stubGraph G p q))
    (H : SimpleGraph (V⊕Fin 5))
    (e12 : H.Adj (ring 1) (ring 2)) (e23 : H.Adj (ring 2) (ring 3))
    (e34 : H.Adj (ring 3) (ring 4))
    (pw : H.Adj (out p) (ring 1)) (qw : H.Adj (out q) (ring 4))
    (old : ∀ v w,G.Adj v w → H.Adj (out v) (out w)) :
    FactorOn H (univ.erase (ring 0)) := by
  obtain ⟨T,used,tile,remaining⟩ := factor_erase_tile f stub
  let e := embed V
  let S := ((univ : Finset (V⊕Unit)) \ T).map e
  let R := ((T \ {stub}).map e) ∪ remainingCorners V
  have partition : FactorOn H S := factor_map_on e (by
    intro x hx y hy edge
    have nx := (mem_sdiff.mp hx).2
    have ny := (mem_sdiff.mp hy).2
    cases x with
    | inr x => cases x; exact (nx used).elim
    | inl x =>
      cases y with
      | inr y => cases y; exact (ny used).elim
      | inl y => exact old x y edge) remaining
  have others := replace_stub_tile ne tile used H e12 e23 e34 pw qw old
  have disjoint : Disjoint S R := by
    apply disjoint_left.mpr
    intro z hz hl
    obtain ⟨x,xs,xe⟩ := mem_map.mp hz
    rcases mem_union.mp hl with inward|ringw
    · obtain ⟨y,yt,ye⟩ := mem_map.mp inward
      have xy := e.injective (xe.trans ye.symm)
      exact (mem_sdiff.mp xs).2 (xy ▸ (mem_sdiff.mp yt).1)
    · cases x with
      | inr t => cases t; exact (mem_sdiff.mp xs).2 used
      | inl t =>
        rw [←xe] at ringw
        simp [e,embed,remainingCorners] at ringw
  have cover : S ∪ R = univ.erase (ring 0) := by
    ext z
    cases z with
    | inl v =>
      have back : (embed V) (Sum.inl v) = out v := rfl
      by_cases hi : Sum.inl v ∈ T
      · have h : out v ∈ (T \ {stub}).map e :=
          mem_map.mpr ⟨_,mem_sdiff.mpr ⟨hi,by simp⟩,back⟩
        simp [S,R,h]
      · have h : out v ∈ S := mem_map.mpr ⟨_,mem_sdiff.mpr ⟨mem_univ _,hi⟩,back⟩
        simp [h]
    | inr i =>
      have emptyLeft : ring i ∉ S := by
        intro h
        obtain ⟨x,xs,equal⟩ := mem_map.mp h
        cases x with
        | inr t => cases t; exact (mem_sdiff.mp xs).2 used
        | inl t => exact Sum.noConfusion (show out t = ring i from equal)
      have emptyMid : ring i ∉ ((T \ {stub}).map e) := by
        intro h
        obtain ⟨x,xs,equal⟩ := mem_map.mp h
        cases x with
        | inr t => cases t; exact (mem_sdiff.mp xs).2 (by simp)
        | inl t => exact Sum.noConfusion (show out t = ring i from equal)
      simp [S,R,emptyLeft,emptyMid,ring_mem_corners]
  exact cover ▸ factor_disjUnion partition others disjoint

#print axioms replace_stub_tile
#print axioms close_pentagon_at_zero

#print axioms stub_tile_cases

end
end KelmansCactus.AtomicBridge.PentagonTransfer
