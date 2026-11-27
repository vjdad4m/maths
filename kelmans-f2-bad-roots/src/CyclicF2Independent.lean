import CenteredCapZ5
import ClosedPullback
import DominoF1

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open Substitute FourRingCutAux FourRingCyclicEquivalence HandleExtension CopyMimic
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Omit one edge from an ambient graph without changing the vertex type. -/
def omitEdge (G : SimpleGraph V) (a b : V) : SimpleGraph V where
  Adj p q := G.Adj p q ∧ ¬((p=a ∧ q=b) ∨ (p=b ∧ q=a))
  symm := by
    intro p q h
    exact ⟨h.1.symm,fun x=>h.2 (x.elim (fun y=>Or.inr ⟨y.2,y.1⟩) (fun y=>Or.inl ⟨y.2,y.1⟩))⟩
  loopless := fun p h=>G.loopless p h.1

/-- In an order-four cap, fix two independent handled edges. After
omitting the first edge, at least one endpoint of the second may be
deleted without losing a P3 factor. -/
theorem cyclic4_f2_one_endpoint_of_handle (promise : CyclicUniversal.{u})
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀ v,G.degree v=3) (small : SmallTrivial G)
    (order : Fintype.card V%6=4) (E : Edges G) :
    ∃ z,E.Ends true z ∧
      Closed (omitEdge G (E.a false) (E.b false)) (univ.erase z) := by
  have div : 6∣Fintype.card V+2 := by omega
  have dom := E.cyclic_domain cub small div
  have turn : E.host.Adj (Sum.inr true) (Sum.inr false) := by change true≠false; decide
  obtain ⟨w,ne,_,adj,rem⟩ := cyclic4_centered_pair_at_neighbor promise dom turn
  cases w with
  | inr t =>
    cases t
    · exact (ne rfl).elim
    · exact (adj.ne rfl).elim
  | inl z =>
    let e : V ↪ V⊕Bool := ⟨Sum.inl,Sum.inl_injective⟩
    have eq :
        ((univ:Finset V).erase z).map e =
        (univ : Finset (V⊕Bool))\{Sum.inr true,Sum.inr false,Sum.inl z} := by
      ext p
      cases p with
      | inl y =>
        have ymap : Sum.inl y∈((univ:Finset V).erase z).map e ↔
            y∈(univ:Finset V).erase z := mem_map' e
        rw [ymap]
        simp
      | inr t =>
        have out : Sum.inr t∉((univ:Finset V).erase z).map e := by
          intro h
          obtain ⟨q,_,eq⟩ := mem_map.mp h
          exact Sum.noConfusion eq
        cases t <;> simp [out]
    rw [←eq] at rem
    refine ⟨z,adj,closed_pullback e ?_ rem⟩
    intro u _ v _ h
    change E.deleteChosen.Adj u v at h
    exact ⟨h.1,fun used=>h.2 ⟨false,used⟩⟩

private theorem f2_at_omitted_endpoint (promise : CyclicUniversal.{u})
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀ v,G.degree v=3) (conn : KelmansStarter.ThreeConnected G)
    (small : SmallTrivial G) (order : Fintype.card V%6=4)
    {a b x : V} (which : x=a ∨ x=b) :
    Closed (omitEdge G a b) (univ.erase x) := by
  classical
  let e := Function.Embedding.subtype (fun v : V=>v≠x)
  obtain ⟨P,tiles,sep,all⟩ := cyclic4_factor_implies_f1 promise cub conn small order x
  have part : Assemble.LocalPart (DominoGadget.oldGraph G x) P univ := ⟨tiles,sep,all⟩
  have mapped := local_map e (G:=DominoGadget.oldGraph G x) (H:=omitEdge G a b) (fun u _ v _ h=>by
    change G.Adj u.val v.val at h
    refine ⟨h,?_⟩
    intro flag
    rcases flag with ⟨p,q⟩|⟨p,q⟩
    · rcases which with ex|ex
      · exact u.property (p.trans ex.symm)
      · exact v.property (q.trans ex.symm)
    · rcases which with ex|ex
      · exact v.property (q.trans ex.symm)
      · exact u.property (p.trans ex.symm)) part
  have eq : (univ : Finset (DominoGadget.Rest x)).map e = (univ:Finset V).erase x := by
    ext v
    constructor
    · intro h
      obtain ⟨w,_,rfl⟩ := mem_map.mp h
      exact mem_erase.mpr ⟨w.property,mem_univ _⟩
    · intro h
      exact mem_map.mpr ⟨⟨v,(mem_erase.mp h).1⟩,mem_univ _,rfl⟩
  rw [eq] at mapped
  exact ⟨_,mapped⟩

/-- For any fixed omitted edge in a cyclically four-edge-connected cubic
graph of order 4 modulo 6, the vertices whose simultaneous deletion
blocks a P3 factor form an independent set, conditionally on ordinary
cyclic-four factoring. This is weaker than F2 (which says there are none). -/
theorem cyclic4_f2_bad_roots_independent (promise : CyclicUniversal.{u})
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀ v,G.degree v=3) (conn : KelmansStarter.ThreeConnected G)
    (small : SmallTrivial G) (order : Fintype.card V%6=4)
    {a b : V} (ab : G.Adj a b) :
    ({x | ¬ Closed (omitEdge G a b) (univ.erase x)}:Set V).Pairwise (fun u v=> ¬G.Adj u v) := by
  intro u badu v badv _ uv
  have uout : ¬ (u=a ∨ u=b) :=
    fun h=>badu (f2_at_omitted_endpoint promise cub conn small order h)
  have vout : ¬ (v=a ∨ v=b) :=
    fun h=>badv (f2_at_omitted_endpoint promise cub conn small order h)
  let E : Edges G := {
    a := fun k=>if k then u else a
    b := fun k=>if k then v else b
    edge := by intro k; cases k <;> assumption
    separated := by
      intro r s q qr qs
      cases r <;> cases s
      · rfl
      · change q=a ∨ q=b at qr
        change q=u ∨ q=v at qs
        rcases qs with rfl|rfl
        · exact (uout qr).elim
        · exact (vout qr).elim
      · change q=u ∨ q=v at qr
        change q=a ∨ q=b at qs
        rcases qr with rfl|rfl
        · exact (uout qs).elim
        · exact (vout qs).elim
      · rfl }
  obtain ⟨z,e,h⟩ := cyclic4_f2_one_endpoint_of_handle promise cub small order E
  change z=u ∨ z=v at e
  rcases e with rfl|rfl
  · exact badu h
  · exact badv h

#print axioms cyclic4_f2_one_endpoint_of_handle
#print axioms cyclic4_f2_bad_roots_independent
end
end KelmansCactus.AtomicBridge
