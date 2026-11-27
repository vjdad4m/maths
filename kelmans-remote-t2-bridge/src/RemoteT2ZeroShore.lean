import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2ZeroShore
open SquareCap (cap attach Port SmallTrivial ThreeConnected FactorOn HasFactor PairRest pairMinor factor_map)
universe u

/-- The order-bounded adjacent-pair promise. The cut shore is capped by
two new adjacent cubic vertices, so this is a genuinely smaller input
whenever the opposite shore has more than two vertices. -/
def SmallerT2 (n : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    Fintype.card W<n → (∀ x,G.degree x=3) → ThreeConnected G → SmallTrivial G →
    Fintype.card W%6=2 →
    ∀ r : Bool→W,G.Adj (r false) (r true) → HasFactor (pairMinor G r)

private noncomputable def interiorIso {V : Type u} (G : SimpleGraph V) (p : Port ↪ V) (k : Bool) :
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

/-- A width-four shore of order divisible by six is internally factorable
under the strictly smaller cyclic T2 promise. The four distinct attachment
vertices and original cubic cyclic-four decomposition are explicit input.
No intervening cut wire, and no edge outside the shore, is used. -/
theorem zero_shore_factors {V : Type u} [Fintype V] [DecidableEq V]
    {O : Type u} [Fintype O] [DecidableEq O]
    {G : SimpleGraph V} [DecidableRel G.Adj] {J : SimpleGraph O}
    {p : Port ↪ V} {r : Port→O} [DecidableRel (attach G J p r).Adj]
    (order : Fintype.card V%6=0) (large : 4<Fintype.card V) (outside : 2<Fintype.card O)
    (cub : ∀ x,(attach G J p r).degree x=3) (cyc4 : SmallTrivial (attach G J p r))
    (t2 : SmallerT2.{u} (Fintype.card (V⊕O))) : HasFactor G := by
  classical
  obtain ⟨k,ks,_⟩ := SquareCap.cubic_good_cap (by omega) large cub cyc4
  let A := cap G p k
  have deg (v : V⊕Bool) : A.degree v=3 := SquareCap.cap_cubic (fun w => cub (Sum.inl w)) k v
  have cardA : Fintype.card (V⊕Bool)=Fintype.card V+2 := by simp
  have vc := SquareCap.three_connected_of_small_trivial A deg (by omega) ks
  have lim : Fintype.card (V⊕Bool)<Fintype.card (V⊕O) := by rw [cardA,Fintype.card_sum]; omega
  have rem : Fintype.card (V⊕Bool)%6=2 := by rw [cardA]; omega
  have edge : A.Adj (Sum.inr false) (Sum.inr true) := by
    change (⊤ : SimpleGraph Bool).Adj false true
    decide
  have ff := t2 (V⊕Bool) A lim deg vc ks rem Sum.inr edge
  let f := (interiorIso G p k).symm
  have mapped := factor_map f.toEquiv.toEmbedding (H:=G)
    (fun _ _ e => f.map_adj_iff.mpr e) ff
  rwa [map_univ_equiv] at mapped

/-- Two disjoint internal shore factors suffice for a factor after
gluing, regardless of whether any seam edges survive. -/
theorem factor_two_shores {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {G : SimpleGraph L} {H : SimpleGraph R} {X : SimpleGraph (L⊕R)}
    (LG : ∀ a b,G.Adj a b → X.Adj (Sum.inl a) (Sum.inl b))
    (RH : ∀ a b,H.Adj a b → X.Adj (Sum.inr a) (Sum.inr b))
    (left : HasFactor G) (right : HasFactor H) : HasFactor X := by
  classical
  let l : L ↪ L⊕R := ⟨Sum.inl,Sum.inl_injective⟩
  let r : R ↪ L⊕R := ⟨Sum.inr,Sum.inr_injective⟩
  obtain ⟨P,pt,pd,pc⟩ := factor_map l LG left
  obtain ⟨Q,qt,qd,qc⟩ := factor_map r RH right
  have between {A B : Finset (L⊕R)} (a : A∈P) (b : B∈Q) : Disjoint A B := by
    apply disjoint_left.mpr
    intro z za zb
    have zl : z∈univ.map l := pc ▸ mem_biUnion.mpr ⟨A,a,za⟩
    have zr : z∈univ.map r := qc ▸ mem_biUnion.mpr ⟨B,b,zb⟩
    obtain ⟨v,_,rfl⟩ := mem_map.mp zl
    obtain ⟨w,_,eq⟩ := mem_map.mp zr
    change Sum.inr w=Sum.inl v at eq
    exact Sum.noConfusion eq
  refine ⟨P∪Q,?_,?_,?_⟩
  · intro A hA
    exact (mem_union.mp hA).elim (pt A) (qt A)
  · intro A Ains B Bins ne
    rcases mem_union.mp Ains with ap|aq <;> rcases mem_union.mp Bins with bp|bq
    · exact pd A ap B bp ne
    · exact between ap bq
    · exact (between bp aq).symm
    · exact qd A aq B bq ne
  · ext z
    simp only [mem_univ,iff_true]
    cases z with
    | inl v =>
      have mem : Sum.inl v∈univ.map l := mem_map.mpr ⟨v,mem_univ _,rfl⟩
      obtain ⟨A,ap,zA⟩ := mem_biUnion.mp (pc.symm ▸ mem)
      exact mem_biUnion.mpr ⟨A,mem_union_left _ ap,zA⟩
    | inr v =>
      have mem : Sum.inr v∈univ.map r := mem_map.mpr ⟨v,mem_univ _,rfl⟩
      obtain ⟨A,ap,zA⟩ := mem_biUnion.mp (qc.symm ▸ mem)
      exact mem_biUnion.mpr ⟨A,mem_union_right _ ap,zA⟩

/-- Conditional full coverage of the (0,0) bridge branch once the two
actual shore attachment decompositions are supplied. The two possible
cappings may use different port pairings. -/
theorem zero_zero_bridge_factors {L R OL OR : Type u}
    [Fintype L] [Fintype R] [Fintype OL] [Fintype OR]
    [DecidableEq L] [DecidableEq R] [DecidableEq OL] [DecidableEq OR]
    {G : SimpleGraph L} {H : SimpleGraph R} {JL : SimpleGraph OL} {JR : SimpleGraph OR}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    {pL : Port ↪ L} {rL : Port→OL} {pR : Port ↪ R} {rR : Port→OR}
    [DecidableRel (attach G JL pL rL).Adj] [DecidableRel (attach H JR pR rR).Adj]
    (cL : ∀ x,(attach G JL pL rL).degree x=3)
    (cR : ∀ x,(attach H JR pR rR).degree x=3)
    (sL : SmallTrivial (attach G JL pL rL)) (sR : SmallTrivial (attach H JR pR rR))
    (oL : Fintype.card L%6=0) (oR : Fintype.card R%6=0)
    (lL : 4<Fintype.card L) (lR : 4<Fintype.card R)
    (outL : 2<Fintype.card OL) (outR : 2<Fintype.card OR)
    (size : Fintype.card (L⊕OL)=Fintype.card (R⊕OR))
    (t2 : SmallerT2.{u} (Fintype.card (L⊕OL)))
    (X : SimpleGraph (L⊕R))
    (LG : ∀ a b,G.Adj a b → X.Adj (Sum.inl a) (Sum.inl b))
    (RH : ∀ a b,H.Adj a b → X.Adj (Sum.inr a) (Sum.inr b)) :
    HasFactor X :=
  factor_two_shores LG RH (zero_shore_factors oL lL outL cL sL t2)
    (zero_shore_factors oR lR outR cR sR (size ▸ t2))

#print axioms zero_zero_bridge_factors
#print axioms zero_shore_factors
#print axioms factor_two_shores
end KelmansCactus.AtomicBridge.RemoteT2ZeroShore
