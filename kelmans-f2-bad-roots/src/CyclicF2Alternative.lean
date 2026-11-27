import CyclicF2Independent

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open Substitute FourRingCutAux FourRingCyclicEquivalence HandleExtension
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- In the handle host, tiling off the two subdivision vertices and one
specified old vertex certifies an original omitted-edge/vertex factor. -/
theorem handle_residue_closes_omit_edge
    {G : SimpleGraph V} (E : Edges G) (z : V)
    (rem : Closed E.host (univ\{Sum.inr true,Sum.inr false,Sum.inl z})) :
    Closed (omitEdge G (E.a false) (E.b false)) (univ.erase z) := by
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
  refine closed_pullback e ?_ rem
  intro u _ v _ h
  change E.deleteChosen.Adj u v at h
  exact ⟨h.1,fun bad=>h.2 ⟨false,bad⟩⟩

/-- If a vertex is bad for the fixed omitted edge (disjoint from the
second handled edge), the other admissible pair at its subdivision is
forced: the original two endpoints of the latter edge. Equivalently,
delete those two old endpoints but *retain* the subdivision of the
omitted edge. This alternate factor is guaranteed even if the desired
F2 factor is absent. -/
theorem cyclic4_f2_bad_forces_subdivided_pair_factor
    (promise : CyclicUniversal.{u})
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (cub : ∀ v,G.degree v=3) (small : SmallTrivial G)
    (order : Fintype.card V%6=4) (E : Edges G)
    (bad : ¬ Closed (omitEdge G (E.a false) (E.b false)) (univ.erase (E.a true))) :
    Closed E.host (univ\{Sum.inr true,Sum.inl (E.a true),Sum.inl (E.b true)}) := by
  have div : 6∣Fintype.card V+2 := by omega
  have dom := E.cyclic_domain cub small div
  have turn : E.host.Adj (Sum.inr true) (Sum.inl (E.a true)) := Or.inl rfl
  obtain ⟨w,ne,_,adj,rem⟩ := cyclic4_centered_pair_at_neighbor promise dom turn
  cases w with
  | inr t =>
    cases t
    · apply (bad (handle_residue_closes_omit_edge E (E.a true) ?_)).elim
      have sh : ({Sum.inr true,Sum.inl (E.a true),Sum.inr false}:Finset (V⊕Bool)) =
          {Sum.inr true,Sum.inr false,Sum.inl (E.a true)} := by
        ext p
        simp only [mem_insert,mem_singleton]
        tauto
      simpa only [sh] using rem
    · exact (adj.ne rfl).elim
  | inl z =>
    have ep : z=E.a true ∨ z=E.b true := adj
    rcases ep with same|same
    · exact (ne (congrArg Sum.inl same.symm)).elim
    · simpa only [same] using rem

#print axioms handle_residue_closes_omit_edge
#print axioms cyclic4_f2_bad_forces_subdivided_pair_factor
end
end KelmansCactus.AtomicBridge
