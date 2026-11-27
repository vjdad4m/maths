import HandleExtension
import CyclicT2

namespace KelmansCactus.AtomicBridge.HandleExtension
open SimpleGraph Finset KelmansStarter
noncomputable section
universe u

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Transfer the exact path-factor predicate along a graph isomorphism.
A tile needs the two center edges and is not required to be induced. -/
theorem factor_iso (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (fac : HasP3Factor G) : HasP3Factor H := by
  classical
  obtain ⟨P,hTile,hDis,hCover⟩ := fac
  let E := e.toEquiv.toEmbedding
  let rename : Finset V ↪ Finset W := ⟨fun s => s.map E, Finset.map_injective _⟩
  refine ⟨P.map rename,?_,?_,?_⟩
  · intro t ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨hcard,c,hc,hAdj⟩ := hTile s hs
    change IsTile H (s.map E)
    refine ⟨(Finset.card_map _).trans hcard,e c,Finset.mem_map.mpr ⟨c,hc,rfl⟩,?_⟩
    intro w hw hwc
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
    exact e.toHom.map_adj (hAdj v hv (fun he => hwc (congrArg E he)))
  · intro s hs t ht hne
    obtain ⟨S,hS,rfl⟩ := Finset.mem_map.mp hs
    obtain ⟨T,hT,rfl⟩ := Finset.mem_map.mp ht
    apply Finset.disjoint_left.mpr
    intro w hSw hTw
    change w ∈ S.map E at hSw
    change w ∈ T.map E at hTw
    obtain ⟨a,ha,ea⟩ := Finset.mem_map.mp hSw
    obtain ⟨b,hb,eb⟩ := Finset.mem_map.mp hTw
    have same : a=b := E.injective (ea.trans eb.symm)
    exact Finset.disjoint_left.mp
      (hDis S hS T hT (fun h => hne (congrArg rename h))) ha (same.symm ▸ hb)
  · apply Finset.eq_univ_of_forall
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    have hv : v ∈ P.biUnion id := by rw [hCover]; exact Finset.mem_univ _
    obtain ⟨s,hs,hm⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨rename s,Finset.mem_map.mpr ⟨s,hs,rfl⟩,
      Finset.mem_map.mpr ⟨v,hm,rfl⟩⟩

theorem factor_mono {G H : SimpleGraph V} (h : H ≤ G)
    (f : HasP3Factor H) : HasP3Factor G := by
  obtain ⟨P,hT,hD,hC⟩ := f
  refine ⟨P,?_,hD,hC⟩
  intro s hs
  obtain ⟨hCard,c,hc,hAdj⟩ := hT s hs
  exact ⟨hCard,c,hc,fun x hx hxc => h (hAdj x hx hxc)⟩

open FourRingCyclicEquivalence FourRingCutAux FourRingReplica.Layout

/-- The conditioned two-edge avoidance conclusion uses the very same
vertex type, with only the two chosen edges removed. -/
theorem factor_avoids_two_disjoint (promise : CyclicUniversal.{u})
    {U : Type u} [Fintype U] [DecidableEq U] {G : SimpleGraph U} [DecidableRel G.Adj]
    (dom : CyclicDomain G) (E : Edges G) :
    HasP3Factor E.deleteChosen := by
  classical
  let r : Bool → U ⊕ Bool := Sum.inr
  have hres : Fintype.card (U ⊕ Bool) % 6 = 2 := by
    rw [Edges.host_order]
    obtain ⟨k,hk⟩ := dom.1.2.2
    omega
  have edge : E.host.Adj (r false) (r true) := by change false ≠ true; decide
  have f := cyclic4_factor_implies_t2 promise (E.cubic dom.1.1)
    (E.three_connected dom.1.1 dom.2) (E.preserves_small_trivial dom.1.1 dom.2) hres r edge
  have f' : HasP3Factor (E.host.induce {x | x ≠ Sum.inr false ∧ x ≠ Sum.inr true}) := f
  exact factor_iso _ _ E.deleted_two_iso.symm f'

/-- Every finite simple cubic graph of order at least four has two
vertex-disjoint edges. Only cubicity and the order bound are used. -/
theorem exists_two_disjoint_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (cub : ∀ x,G.degree x=3) (big : 4≤Fintype.card V) : Nonempty (Edges G) := by
  classical
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp (by omega : 0<Fintype.card V)
  have ha : 0<(G.neighborFinset a).card := by
    rw [G.card_neighborFinset_eq_degree,cub]
    decide
  obtain ⟨b,hb⟩ := Finset.card_pos.mp ha
  have e := (G.mem_neighborFinset a b).mp hb
  let S : Finset V := {a,b}
  have s2 : S.card=2 := by simp [S,e.ne]
  have ssmall : S.card < (Finset.univ : Finset V).card := by rw [s2,Finset.card_univ]; omega
  obtain ⟨c,_,hc⟩ := Finset.exists_mem_not_mem_of_card_lt_card ssmall
  have cdeg : (G.neighborFinset c).card=3 := by rw [G.card_neighborFinset_eq_degree,cub]
  have csmall : S.card < (G.neighborFinset c).card := by rw [s2,cdeg]; decide
  obtain ⟨d,hd,hdS⟩ := Finset.exists_mem_not_mem_of_card_lt_card csmall
  have f := (G.mem_neighborFinset c d).mp hd
  have nc : c≠a ∧ c≠b := by simpa [S,not_or] using hc
  have nd : d≠a ∧ d≠b := by simpa [S,not_or] using hdS
  let p : Bool→V := fun s => if s then c else a
  let q : Bool→V := fun s => if s then d else b
  refine ⟨⟨p,q,?_,?_⟩⟩
  · intro s
    cases s <;> assumption
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

/-- Exact universal two-vertex-disjoint-edge-avoidance strengthening. -/
def CyclicTwoEdgeAvoidance : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    CyclicDomain G → ∀ E : Edges G, HasP3Factor E.deleteChosen

theorem cyclic_two_edge_avoidance_iff :
    CyclicUniversal.{u} ↔ CyclicTwoEdgeAvoidance.{u} := by
  constructor
  · intro h V _ _ G _ dom E
    exact factor_avoids_two_disjoint h dom E
  · intro h V _ _ G _ dom
    obtain ⟨E⟩ := exists_two_disjoint_edges G dom.1.1 dom.1.2.1.1
    have sub : E.deleteChosen ≤ G := by intro a b he; exact he.1
    exact factor_mono sub (h V G dom E)

#print axioms factor_iso
#print axioms factor_avoids_two_disjoint
#print axioms exists_two_disjoint_edges
#print axioms cyclic_two_edge_avoidance_iff
end
end KelmansCactus.AtomicBridge.HandleExtension
