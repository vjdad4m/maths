import TriangleTerminal
import HandleFactor
import DominoF1
import AdjacentVacancyHelpers

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open Substitute HandleExtension FourRingCyclicEquivalence FourRingCutAux DominoGadget
noncomputable section
universe u
variable {V : Type u} [DecidableEq V]

/-- Lift a graph on a finite vertex region to its original vertex labels,
without creating edges having an endpoint outside that region. -/
private def liftRegion {S : Finset V} (H : SimpleGraph (↑S : Type u)) : SimpleGraph V where
  Adj x y := ∃ (hx : x∈S) (hy : y∈S),H.Adj ⟨x,hx⟩ ⟨y,hy⟩
  symm := by
    rintro x y ⟨hx,hy,e⟩
    exact ⟨hy,hx,e.symm⟩
  loopless := by rintro x ⟨hx,hy,xx⟩; exact xx.ne rfl

private theorem closed_lift {S : Finset V} {H : SimpleGraph (↑S : Type u)}
    (f : KelmansStarter.HasP3Factor H) : Closed (liftRegion H) S := by
  obtain ⟨P,tile,ne,cover⟩ := f
  let e := Function.Embedding.subtype (fun x=>x∈S)
  let F : Finset (↑S : Type u)↪Finset V := ⟨Finset.map e,Finset.map_injective _⟩
  refine ⟨P.map F,⟨?_,?_,?_⟩⟩
  · intro s sm
    obtain ⟨t,tm,rfl⟩ := mem_map.mp sm
    obtain ⟨sz,c,cm,star⟩ := tile t tm
    exact ⟨(card_map _).trans sz,c.val,mem_map.mpr ⟨c,cm,rfl⟩,
      fun y ym no=>
        let ⟨v,vm,eq⟩ := mem_map.mp ym
        eq ▸ (show (liftRegion H).Adj c.val v.val from
          ⟨c.property,v.property,star _ vm (fun h=>no (eq.symm.trans (congrArg Subtype.val h)))⟩)⟩
  · intro s sm t tm sep
    obtain ⟨a,am,rfl⟩ := mem_map.mp sm
    obtain ⟨b,bm,rfl⟩ := mem_map.mp tm
    apply disjoint_left.mpr
    intro x xa xb
    obtain ⟨y,ya,rfl⟩ := mem_map.mp xa
    obtain ⟨z,zb,eq⟩ := mem_map.mp xb
    exact disjoint_left.mp (ne a am b bm (fun h=>sep (congrArg F h))) ya ((e.injective eq) ▸ zb)
  · ext x
    constructor
    · intro hx
      obtain ⟨t,tm,xt⟩ := mem_biUnion.mp hx
      obtain ⟨r,rm,rfl⟩ := mem_map.mp tm
      obtain ⟨z,_,rfl⟩ := mem_map.mp xt
      exact z.property
    · intro xs
      let z : (↑S : Type u) := ⟨x,xs⟩
      obtain ⟨t,tm,zt⟩ := mem_biUnion.mp (cover.symm ▸ mem_univ z)
      exact mem_biUnion.mpr ⟨F t,mem_map.mpr ⟨t,tm,rfl⟩,mem_map.mpr ⟨z,zt,rfl⟩⟩

private theorem exists_disjoint_from_edge {U : Type u} [Fintype U] [DecidableEq U]
    {H : SimpleGraph U} [DecidableRel H.Adj] (cub : ∀v,H.degree v=3)
    (big : 4≤Fintype.card U) {a b : U} (ab : H.Adj a b) :
    ∃ E : Edges H,E.a false=a ∧ E.b false=b := by
  classical
  let S : Finset U := {a,b}
  have s2 : S.card=2 := by simp [S,ab.ne]
  have ssmall : S.card < (univ : Finset U).card := by rw [s2,card_univ]; omega
  obtain ⟨c,_,hc⟩ := exists_mem_not_mem_of_card_lt_card ssmall
  have cdeg : (H.neighborFinset c).card=3 := by rw [H.card_neighborFinset_eq_degree,cub]
  have csmall : S.card < (H.neighborFinset c).card := by rw [s2,cdeg]; decide
  obtain ⟨d,hd,hdS⟩ := exists_mem_not_mem_of_card_lt_card csmall
  have f := (H.mem_neighborFinset c d).mp hd
  have nc : c≠a ∧ c≠b := by simpa [S,not_or] using hc
  have nd : d≠a ∧ d≠b := by simpa [S,not_or] using hdS
  let p : Bool→U := fun s=>if s then c else a
  let q : Bool→U := fun s=>if s then d else b
  refine ⟨⟨p,q,?_,?_⟩,rfl,rfl⟩
  · intro s; cases s <;> assumption
  · intro s t x hs ht
    cases s <;> cases t
    · rfl
    · simp only [p,q,Bool.false_eq_true,if_false,if_true] at hs ht
      rcases hs with h|h <;> rcases ht with h'|h'
      · exact (nc.1 (h'.symm.trans h)).elim
      · exact (nd.1 (h'.symm.trans h)).elim
      · exact (nc.2 (h'.symm.trans h)).elim
      · exact (nd.2 (h'.symm.trans h)).elim
    · simp only [p,q,Bool.false_eq_true,if_false,if_true] at hs ht
      rcases hs with h|h <;> rcases ht with h'|h'
      · exact (nc.1 (h.symm.trans h')).elim
      · exact (nc.2 (h.symm.trans h')).elim
      · exact (nd.1 (h.symm.trans h')).elim
      · exact (nd.2 (h.symm.trans h')).elim
    · rfl

/-- The nonzero-residue cap's single forbidden link is available from
cyclic-four ordinary Kelmans, using one other disjoint edge. -/
theorem triangle_junction_from_cyclic_cap
    (promise : CyclicUniversal.{u}) {G : SimpleGraph V}
    {C : Finset V} {x a b c d e f : V}
    (xC : x∉C) (aC : a∉C) (bC : b∉C) (cC : c∉C)
    (xa : x≠a) (xc : x≠c)
    (xb : G.Adj x b) (ab : G.Adj a b) (bc : G.Adj b c) (ac : G.Adj a c)
    (xd : G.Adj x d) (ae : G.Adj a e)
    (fC : f∈C)
    (H : SimpleGraph (↑(insert x C):Type u)) [DecidableRel H.Adj]
    (dom : CyclicDomain H)
    (xf : H.Adj ⟨x,mem_insert_self _ _⟩ ⟨f,mem_insert_of_mem fC⟩)
    (nbr : ∀ v (hv : v∈C),H.Adj ⟨x,mem_insert_self _ _⟩ ⟨v,mem_insert_of_mem hv⟩ →
      v=d ∨ v=e ∨ v=f)
    (keep : ∀ v w (hv : v∈C) (hw : w∈C),
      H.Adj ⟨v,mem_insert_of_mem hv⟩ ⟨w,mem_insert_of_mem hw⟩→G.Adj v w) :
    Closed G (C∪{x,a,b,c}) := by
  classical
  obtain ⟨E,ea,eb⟩ := exists_disjoint_from_edge dom.1.1 dom.1.2.1.1 xf
  have cap := closed_lift (factor_avoids_two_disjoint promise dom E)
  apply triangle_and_singleton_absorb_cap xC aC bC cC xa xc xb ab bc ac xd ae cap
  · intro v hv link
    obtain ⟨hx,hv',ed,no⟩ := link
    change H.Adj ⟨x,mem_insert_self _ _⟩ ⟨v,mem_insert_of_mem hv⟩ at ed
    rcases nbr v hv ed with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · subst v
      exact (no ⟨false,Or.inl ⟨ea.symm,eb.symm⟩⟩).elim
  · intro v hv w hw link
    obtain ⟨hv',hw',ed,_⟩ := link
    exact keep v w hv hw ed

/-- The root-free shore of a cyclic-four order-four cap is closed,
with only original internal edges used. -/
theorem closed_atom_without_root (promise : CyclicUniversal.{u})
    {G : SimpleGraph V} {A : Finset V} {x : V} (xA : x∉A)
    (H : SimpleGraph (↑(insert x A):Type u)) [DecidableRel H.Adj]
    (cub : ∀ v,H.degree v=3) (conn : KelmansStarter.ThreeConnected H)
    (small : SmallTrivial H) (res : Fintype.card (↑(insert x A):Type u)%6=4)
    (keep : ∀ u v (hu : u∈A) (hv : v∈A),
      H.Adj ⟨u,mem_insert_of_mem hu⟩ ⟨v,mem_insert_of_mem hv⟩→G.Adj u v) :
    Closed G A := by
  let Root : (↑(insert x A) : Type u) := ⟨x,mem_insert_self _ _⟩
  let e : (↑A : Type u) → Rest Root := fun a=>
    ⟨⟨a.val,mem_insert_of_mem a.property⟩,by
      intro eq
      have same : a.val=x := congrArg (fun u : (↑(insert x A):Type u)=>u.val) eq
      exact xA (same ▸ a.property)⟩
  have bij : Function.Bijective e := by
    constructor
    · intro p q eq
      exact Subtype.ext (congrArg (fun u : Rest Root=>u.val.val) eq)
    · rintro ⟨⟨u,hu⟩,ne⟩
      have uA : u∈A := by
        rcases mem_insert.mp hu with same|inside
        · exact (ne (Subtype.ext same)).elim
        · exact inside
      exact ⟨⟨u,uA⟩,rfl⟩
  let K : SimpleGraph (↑A : Type u) := (oldGraph H Root).comap e
  have f := cyclic4_factor_implies_f1 promise cub conn small res Root
  have localFactor : KelmansStarter.HasP3Factor K :=
    factor_pullback (H:=oldGraph H Root) (G:=K) (Equiv.ofBijective e bij) (fun _ _ h=>h) f
  obtain ⟨P,ok⟩ := closed_lift localFactor
  refine ⟨P,change_edges (G:=G) ok ?_⟩
  intro u hu v hv e
  rcases e with ⟨_,_,edge⟩
  exact keep u v hu hv edge

/-- Exact conditional factor for a three-terminal singleton junction
with one triangle shore, one order-four capped shore and one
order-zero capped shore. In K4 terminology this is the (0,0,2)
shore-residue case with one triangle. -/
theorem triangle_two_caps_factor_if_cyclic_four
    [Fintype V] (promise : CyclicUniversal.{u}) {G : SimpleGraph V}
    {B C : Finset V} {x a b c d e f : V}
    (xC : x∉C) (aC : a∉C) (bC : b∉C) (cC : c∉C)
    (xB : x∉B) (xa : x≠a) (xc : x≠c)
    (xb : G.Adj x b) (ab : G.Adj a b) (bc : G.Adj b c) (ac : G.Adj a c)
    (xd : G.Adj x d) (ae : G.Adj a e)
    (fC : f∈C)
    (HC : SimpleGraph (↑(insert x C):Type u)) [DecidableRel HC.Adj]
    (domC : CyclicDomain HC)
    (xf : HC.Adj ⟨x,mem_insert_self _ _⟩ ⟨f,mem_insert_of_mem fC⟩)
    (nbr : ∀ v (hv : v∈C),HC.Adj ⟨x,mem_insert_self _ _⟩ ⟨v,mem_insert_of_mem hv⟩ →
      v=d ∨ v=e ∨ v=f)
    (keepC : ∀ v w (hv : v∈C) (hw : w∈C),
      HC.Adj ⟨v,mem_insert_of_mem hv⟩ ⟨w,mem_insert_of_mem hw⟩→G.Adj v w)
    (HB : SimpleGraph (↑(insert x B):Type u)) [DecidableRel HB.Adj]
    (cubB : ∀ v,HB.degree v=3) (conB : KelmansStarter.ThreeConnected HB)
    (c4B : SmallTrivial HB) (resB : Fintype.card (↑(insert x B):Type u)%6=4)
    (keepB : ∀ v w (hv : v∈B) (hw : w∈B),
      HB.Adj ⟨v,mem_insert_of_mem hv⟩ ⟨w,mem_insert_of_mem hw⟩→G.Adj v w)
    (sep : Disjoint (C∪{x,a,b,c}) B) (whole : (C∪{x,a,b,c})∪B=univ) :
    KelmansStarter.HasP3Factor G := by
  have nonzero := triangle_junction_from_cyclic_cap promise xC aC bC cC xa xc xb ab bc ac
    xd ae fC HC domC xf nbr keepC
  have zero := closed_atom_without_root promise xB HB cubB conB c4B resB keepB
  obtain ⟨P,hP⟩ := add_closed nonzero zero sep
  exact ⟨P,hP.tile,hP.disj,hP.cover.trans whole⟩

/-- The root and a prescribed neighbor of an order-two cyclic-four
cap can both be dropped, with only old internal edges used. -/
theorem closed_atom_without_root_and_port (promise : CyclicUniversal.{u})
    {G : SimpleGraph V} {A : Finset V} {x a : V} (xA : x∉A) (aA : a∈A)
    (H : SimpleGraph (↑(insert x A):Type u)) [DecidableRel H.Adj]
    (cub : ∀ v,H.degree v=3) (conn : KelmansStarter.ThreeConnected H)
    (small : SmallTrivial H) (res : Fintype.card (↑(insert x A):Type u)%6=2)
    (adj : H.Adj ⟨x,mem_insert_self _ _⟩ ⟨a,mem_insert_of_mem aA⟩)
    (keep : ∀ u v (hu : u∈A) (hv : v∈A),
      H.Adj ⟨u,mem_insert_of_mem hu⟩ ⟨v,mem_insert_of_mem hv⟩→G.Adj u v) :
    Closed G (A.erase a) := by
  let R : Bool→(↑(insert x A):Type u) := fun b=>
    if b then ⟨a,mem_insert_of_mem aA⟩ else ⟨x,mem_insert_self _ _⟩
  let S := A.erase a
  let E : (↑S : Type u)→FourRingReplica.Piece R := fun y=>
    ⟨⟨y.val,mem_insert_of_mem (mem_erase.mp y.property).2⟩,
      by
        intro eq
        have yx : y.val=x := congrArg (fun z : (↑(insert x A):Type u)=>z.val) eq
        exact xA (yx ▸ (mem_erase.mp y.property).2),
      by
        intro eq
        have ya : y.val=a := congrArg (fun z : (↑(insert x A):Type u)=>z.val) eq
        exact (mem_erase.mp y.property).1 ya⟩
  have bij : Function.Bijective E := by
    constructor
    · intro p q eq
      exact Subtype.ext (congrArg (fun u : FourRingReplica.Piece R=>u.val.val) eq)
    · rintro ⟨⟨v,vm⟩,nx,na⟩
      have vA : v∈A := by
        rcases mem_insert.mp vm with yes|no
        · exact (nx (Subtype.ext yes)).elim
        · exact no
      let w : (↑S : Type u) := ⟨v,mem_erase.mpr ⟨fun e=>na (Subtype.ext e),vA⟩⟩
      exact ⟨w,rfl⟩
  let K := (FourRingReplica.Layout.minor H R).comap E
  have original := cyclic4_factor_implies_t2 promise cub conn small res R adj
  have f : KelmansStarter.HasP3Factor K :=
    factor_pullback (H:=FourRingReplica.Layout.minor H R) (G:=K) (Equiv.ofBijective E bij)
      (fun _ _ h=>h) original
  obtain ⟨P,p⟩ := closed_lift f
  refine ⟨P,change_edges (G:=G) p ?_⟩
  intro u hu v hv h
  obtain ⟨_,_,edge⟩ := h
  exact keep u v (mem_erase.mp hu).2 (mem_erase.mp hv).2 edge

/-- Exact (1,1,0) shore-residue case of a singleton junction. Two cyclic
order-two caps supply forced one-vertex fragments to the singleton.
The remaining shore can be a triangle or any closed region. -/
theorem singleton_two_order_two_caps_factor_if_cyclic_four
    [Fintype V] (promise : CyclicUniversal.{u}) {G : SimpleGraph V}
    {A B C : Finset V} {a b x : V}
    (ad : a∈A) (bd : b∈B) (xA : x∉A) (xB : x∉B) (xC : x∉C)
    (disAB : Disjoint A B) (disAC : Disjoint A C) (disBC : Disjoint B C)
    (ax : G.Adj a x) (xb : G.Adj x b) (cCl : Closed G C)
    (HA : SimpleGraph (↑(insert x A):Type u)) [DecidableRel HA.Adj]
    (cubA : ∀ v,HA.degree v=3) (connA : KelmansStarter.ThreeConnected HA)
    (smallA : SmallTrivial HA) (resA : Fintype.card (↑(insert x A):Type u)%6=2)
    (xAc : HA.Adj ⟨x,mem_insert_self _ _⟩ ⟨a,mem_insert_of_mem ad⟩)
    (keepA : ∀ v w (hv : v∈A) (hw : w∈A),
      HA.Adj ⟨v,mem_insert_of_mem hv⟩ ⟨w,mem_insert_of_mem hw⟩→G.Adj v w)
    (HB : SimpleGraph (↑(insert x B):Type u)) [DecidableRel HB.Adj]
    (cubB : ∀ v,HB.degree v=3) (connB : KelmansStarter.ThreeConnected HB)
    (smallB : SmallTrivial HB) (resB : Fintype.card (↑(insert x B):Type u)%6=2)
    (xBc : HB.Adj ⟨x,mem_insert_self _ _⟩ ⟨b,mem_insert_of_mem bd⟩)
    (keepB : ∀ v w (hv : v∈B) (hw : w∈B),
      HB.Adj ⟨v,mem_insert_of_mem hv⟩ ⟨w,mem_insert_of_mem hw⟩→G.Adj v w)
    (whole : insert x (A∪B∪C)=univ) : KelmansStarter.HasP3Factor G := by
  have aCl := closed_atom_without_root_and_port promise xA ad HA cubA connA smallA resA xAc keepA
  have bCl := closed_atom_without_root_and_port promise xB bd HB cubB connB smallB resB xBc keepB
  obtain ⟨P,p⟩ := singleton_joins_two_leaf_shores ad bd disAB disAC disBC xA xB xC ax xb aCl bCl cCl
  exact ⟨P,p.tile,p.disj,p.cover.trans whole⟩

#print axioms triangle_junction_from_cyclic_cap
#print axioms closed_atom_without_root
#print axioms triangle_two_caps_factor_if_cyclic_four
#print axioms closed_atom_without_root_and_port
#print axioms singleton_two_order_two_caps_factor_if_cyclic_four
end
end KelmansCactus.AtomicBridge
