import SquareCapGeometry

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.SquareCap
noncomputable section

universe u

/-- The same center-and-leaves tile used in KelmansStarter.IsTile. -/
def IsTile {W : Type*} (G : SimpleGraph W) (S : Finset W) : Prop :=
  S.card = 3 ∧ ∃ c ∈ S, ∀ x ∈ S, x ≠ c → G.Adj c x

def FactorOn {W : Type*} [DecidableEq W] (G : SimpleGraph W) (S : Finset W) : Prop :=
  ∃ P : Finset (Finset W),
    (∀ A ∈ P, IsTile G A) ∧
    (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
    P.biUnion id = S

abbrev HasFactor {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) :=
  FactorOn G univ

theorem factor_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {S : Finset V}
    (f : V ↪ W) (mono : ∀ x y,G.Adj x y → H.Adj (f x) (f y))
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
    exact mono c v (eb v hv (fun e => ne (congrArg f e)))
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

abbrev PairRest {W : Type*} (r : Bool → W) :=
  {x : W // x ≠ r false ∧ x ≠ r true}

abbrev pairMinor {W : Type*} (G : SimpleGraph W) (r : Bool → W) :
    SimpleGraph (PairRest r) := G.induce {x | x ≠ r false ∧ x ≠ r true}

/-- Exact input obtained from the published cyclic adjacent-pair
deletion theorem. This definition keeps the standalone replay short. -/
def CyclicT2Promise : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    (∀ x, G.degree x = 3) → ThreeConnected G → SmallTrivial G →
    Fintype.card W % 6 = 2 →
    ∀ r : Bool → W, G.Adj (r false) (r true) → HasFactor (pairMinor G r)

private def outsideMinorIso {V : Type u} (G : SimpleGraph V) (p : Port ↪ V) (k : Bool) :
    G ≃g pairMinor (cap G p k) Sum.inr := by
  let fn (x : V) : PairRest (Sum.inr : Bool→V⊕Bool) := ⟨Sum.inl x,by simp⟩
  have bij : Function.Bijective fn := by
    constructor
    · intro a b e
      exact Sum.inl_injective (congrArg Subtype.val e)
    · rintro ⟨v,h⟩
      cases v with
      | inl x => exact ⟨x,rfl⟩
      | inr y => cases y
                 · exact (h.1 rfl).elim
                 · exact (h.2 rfl).elim
  refine { toEquiv := Equiv.ofBijective fn bij, map_rel_iff' := ?_ }
  intro a b
  change G.Adj a b ↔ G.Adj a b
  rfl

/-- With the cyclic pair-deletion theorem, a square-residue host
factors on its entire exterior. In particular no tile needs to use
a port edge. The fourth-order gadget need not be assumed a square
for this exterior conclusion. -/
theorem exterior_factors_of_t2 (t2 : CyclicT2Promise.{u})
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Type*} [Fintype T] [DecidableEq T]
    {P : SimpleGraph T} {p : Port ↪ V} {r : Port → T} [DecidableRel (attach G P p r).Adj]
    (gadget_order : Fintype.card T = 4)
    (order : Fintype.card (V ⊕ T) % 6 = 4)
    (large : 4 < Fintype.card V)
    (cub : ∀ x,(attach G P p r).degree x = 3) (small : SmallTrivial (attach G P p r)) :
    HasFactor G := by
  classical
  obtain ⟨k,ks,_⟩ := cubic_good_cap (by omega) large cub small
  let A := cap G p k
  have deg (v : V ⊕ Bool) : A.degree v = 3 := by
    exact cap_cubic (fun w => cub (Sum.inl w)) k v
  have nA : Fintype.card (V ⊕ Bool) = Fintype.card V + 2 := by simp
  have vc := three_connected_of_small_trivial A deg (by omega) ks
  have rem : Fintype.card (V ⊕ Bool) % 6 = 2 := by
    rw [Fintype.card_sum,gadget_order] at order
    omega
  have edge : A.Adj (Sum.inr false) (Sum.inr true) := by
    change (⊤ : SimpleGraph Bool).Adj false true
    decide
  have ff := t2 (V ⊕ Bool) A deg vc ks rem Sum.inr edge
  let f := (outsideMinorIso G p k).symm
  have mapped := factor_map f.toEquiv.toEmbedding (H:=G)
    (fun _ _ e => f.map_adj_iff.mpr e) ff
  rwa [map_univ_equiv] at mapped

/-- If the gadget minus its specified root is a tile, the exterior
factor and this tile combine without using any port wire. In fact
the conclusion holds for any target graph keeping only the
within-exterior and within-gadget edges. -/
theorem square_root_deletion_avoids_all_wires (t2 : CyclicT2Promise.{u})
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Type*} [Fintype T] [DecidableEq T]
    {P : SimpleGraph T} {p : Port ↪ V} {r : Port → T} [DecidableRel (attach G P p r).Adj]
    (gadget_order : Fintype.card T = 4)
    (order : Fintype.card (V ⊕ T) % 6 = 4)
    (large : 4 < Fintype.card V)
    (cub : ∀ x,(attach G P p r).degree x = 3) (small : SmallTrivial (attach G P p r))
    (x : T) (tile : IsTile P (univ.erase x))
    (H : SimpleGraph (V ⊕ T))
    (gkeep : ∀ v w,G.Adj v w → H.Adj (Sum.inl v) (Sum.inl w))
    (pkeep : ∀ v w,P.Adj v w → H.Adj (Sum.inr v) (Sum.inr w)) :
    FactorOn H (univ.erase (Sum.inr x)) := by
  let l : V ↪ V⊕T := ⟨Sum.inl,Sum.inl_injective⟩
  let j : T ↪ V⊕T := ⟨Sum.inr,Sum.inr_injective⟩
  have out := factor_map l gkeep (exterior_factors_of_t2 t2 gadget_order order large cub small)
  have inside := factor_map j pkeep (factor_single tile)
  have d : Disjoint (univ.map l) ((univ.erase x).map j) := by
    apply disjoint_left.mpr
    intro z zl zr
    obtain ⟨u,_,rfl⟩ := mem_map.mp zl
    obtain ⟨v,_,e⟩ := mem_map.mp zr
    change Sum.inr v = Sum.inl u at e
    exact Sum.noConfusion e
  have eq : (univ.map l) ∪ ((univ.erase x).map j) = univ.erase (Sum.inr x) := by
    ext z
    cases z
    · simp [l,j,mem_map]
    · simp [l,j,mem_map]
  exact eq ▸ factor_disjUnion out inside d

def square : SimpleGraph Port where
  Adj a b := (a.1 ≠ b.1 ∧ a.2 = b.2) ∨ (a.1 = b.1 ∧ a.2 ≠ b.2)
  symm := by
    intro a b h
    rcases h with ⟨d,e⟩ | ⟨e,d⟩
    · exact Or.inl ⟨d.symm,e.symm⟩
    · exact Or.inr ⟨e.symm,d.symm⟩
  loopless := by intro a; simp

instance : DecidableRel square.Adj := by
  intro a b
  change Decidable ((a.1 ≠ b.1 ∧ a.2 = b.2) ∨ (a.1 = b.1 ∧ a.2 ≠ b.2))
  infer_instance

private instance (x : Port) : Decidable (IsTile square (univ.erase x)) := by
  unfold IsTile
  infer_instance

theorem square_root_tile : ∀ x : Port, IsTile square (univ.erase x) := by decide

/-- This is the same edge omission used by the published F2 module. -/
def omitEdge {W : Type*} (G : SimpleGraph W) (a b : W) : SimpleGraph W where
  Adj p q := G.Adj p q ∧ ¬ ((p = a ∧ q = b) ∨ (p = b ∧ q = a))
  symm := by
    intro p q h
    exact ⟨h.1.symm,fun x => h.2 (x.elim (fun y => Or.inr ⟨y.2,y.1⟩) (fun y => Or.inl ⟨y.2,y.1⟩))⟩
  loopless := fun p h => G.loopless p h.1

/-- The order-four-mod-six F2 problem holds for an attached square
at any square root and any one of the square's exterior wires
as the omitted edge. In fact the proof avoids every wire. -/
theorem square_f2_explicit (t2 : CyclicT2Promise.{u})
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {p : Port ↪ V} [DecidableRel (attach G square p id).Adj]
    (order : Fintype.card (V ⊕ Port) % 6 = 4)
    (large : 4 < Fintype.card V)
    (cub : ∀ x,(attach G square p id).degree x = 3) (small : SmallTrivial (attach G square p id))
    (x j : Port) :
    FactorOn (omitEdge (attach G square p id) (Sum.inr j) (Sum.inl (p j)))
      (univ.erase (Sum.inr x)) := by
  apply square_root_deletion_avoids_all_wires t2 (by decide) order large cub small x (square_root_tile x)
  · intro v w h
    exact ⟨h,by simp⟩
  · intro v w h
    exact ⟨h,by simp⟩

#print axioms square_root_tile
#print axioms square_f2_explicit

#print axioms exterior_factors_of_t2
#print axioms square_root_deletion_avoids_all_wires

end
end KelmansCactus.AtomicBridge.SquareCap
