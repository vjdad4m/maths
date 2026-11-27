import PentagonCap
import PentagonTransfer

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.PentagonCap
open PentagonProfile (Port)
open PentagonTransfer (stubGraph)
open SquareCap (SmallTrivial CyclicT2Promise PairRest pairMinor HasFactor FactorOn)
noncomputable section

universe u
variable {V : Type u}

private def roots : Bool → V ⊕ Fin 3 := fun b => Sum.inr (if b then 1 else 0)

private theorem remaining_inside_label : ∀ j : Fin 3, j ≠ 0 → j ≠ 1 → j = 2 := by decide

private theorem port2_audit : ∀ i : Port,pathRoot i=2 ↔ i=1∨i=4 := by decide

private def stub_iso (G : SimpleGraph V) (p : Port ↪ V) :
    stubGraph G (p 1) (p 4) ≃g pairMinor (pathCap G p) roots := by
  let fn (x : V ⊕ Unit) : PairRest (roots (V:=V)) :=
    match x with
    | .inl v => ⟨Sum.inl v,by simp [roots]⟩
    | .inr _ => ⟨Sum.inr 2,⟨
        fun h => (by decide : (2:Fin 3) ≠ 0) (Sum.inr_injective h),
        fun h => (by decide : (2:Fin 3) ≠ 1) (Sum.inr_injective h)⟩⟩
  have bij : Function.Bijective fn := by
    constructor
    · intro a b h
      have eq := congrArg Subtype.val h
      cases a with
      | inl x => cases b with
        | inl y => exact congrArg Sum.inl (Sum.inl_injective eq)
        | inr y => exact Sum.noConfusion (show Sum.inl x = Sum.inr (2:Fin 3) from eq)
      | inr x => cases b with
        | inl y => exact Sum.noConfusion (show Sum.inr (2:Fin 3) = Sum.inl y from eq)
        | inr y => cases x; cases y; rfl
    · rintro ⟨y,h⟩
      cases y with
      | inl x => exact ⟨Sum.inl x,rfl⟩
      | inr j =>
        have j0 : j ≠ 0 := fun eq=>h.1 (congrArg Sum.inr eq)
        have j1 : j ≠ 1 := fun eq=>h.2 (congrArg Sum.inr eq)
        have e := remaining_inside_label j j0 j1
        subst j
        exact ⟨Sum.inr (),rfl⟩
  have wires (x : V) : (∃ i : Port, p i=x ∧ pathRoot i=2) ↔ x=p 1 ∨ x=p 4 := by
    constructor
    · rintro ⟨i,e,hi⟩
      rcases (port2_audit i).mp hi with rfl|rfl
      · exact Or.inl e.symm
      · exact Or.inr e.symm
    · rintro (rfl|rfl)
      · exact ⟨1,rfl,(port2_audit 1).mpr (Or.inl rfl)⟩
      · exact ⟨4,rfl,(port2_audit 4).mpr (Or.inr rfl)⟩
  refine {toEquiv := Equiv.ofBijective fn bij, map_rel_iff' := ?_}
  intro x y
  cases x <;> cases y
  · rfl
  · exact wires _
  · exact wires _
  · change path3.Adj (2:Fin 3) 2 ↔ False
    exact ⟨path3.loopless 2,False.elim⟩

/-- Cyclic T2 yields the desired one-stub factor for a good
3-vertex path completion. -/
theorem stub_factor_of_good_path_cap (t2 : CyclicT2Promise.{u})
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {p : Port ↪ V}
    [DecidableRel (pathCap G p).Adj] (cute : SmallTrivial (pathCap G p))
    (cub : ∀ x,(pathCap G p).degree x=3)
    (order : Fintype.card (V⊕Fin 5)%6=4) :
    HasFactor (stubGraph G (p 1) (p 4)) := by
  classical
  let H := pathCap G p
  have n : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have v5 : 5≤Fintype.card V := by
    have a := Fintype.card_le_of_injective p p.injective
    simpa using a
  have capOrder : Fintype.card (V⊕Fin 3)%6=2 := by
    rw [Fintype.card_sum,Fintype.card_fin] at order
    omega
  have connected := SquareCap.three_connected_of_small_trivial H cub (by omega) cute
  have edge : H.Adj (roots false) (roots true) := by
    change path3.Adj (0:Fin 3) 1
    decide
  have part := t2 (V⊕Fin 3) H cub connected cute capOrder roots edge
  let e := (stub_iso G p).symm
  have mapped := SquareCap.factor_map e.toEquiv.toEmbedding
    (fun _ _ h => e.map_adj_iff.mpr h) part
  rwa [map_univ_equiv] at mapped

/-- No simple four-cycle in the ambient graph. Adjacent equalities
are already excluded by simple-graph looplessness. -/
def NoFourCycle {W : Type*} (G : SimpleGraph W) : Prop :=
  ∀ a b c d,G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d

theorem adjoining_contacts_nonadjacent {G : SimpleGraph V} {p : Port ↪ V}
    {P : SimpleGraph (Fin 5)}
    (clean : NoFourCycle (attach G P p id)) {i j : Port}
    (ij : P.Adj i j) : ¬G.Adj (p i) (p j) := by
  intro pq
  have e1 : (attach G P p id).Adj (Sum.inr i) (Sum.inr j) := ij
  have e2 : (attach G P p id).Adj (Sum.inr j) (Sum.inl (p j)) := ⟨j,rfl,rfl⟩
  have e3 : (attach G P p id).Adj (Sum.inl (p j)) (Sum.inl (p i)) := pq.symm
  have e4 : (attach G P p id).Adj (Sum.inl (p i)) (Sum.inr i) := ⟨i,rfl,rfl⟩
  have h := clean _ _ _ _ e1 e2 e3 e4
  simp at h

/-- Conditional five-port analogue of square reattachment for the
labeled pentagon. Ambient may be any explicit four-free attachment
with the relevant pentagon path. The returned factor needs only
the two endpoint wires p1,p4, and no other crossing edge. -/
theorem pentagon_root_case_of_cyclic5 (t2 : CyclicT2Promise.{u})
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : SimpleGraph (Fin 5)} {p : Port ↪ V} [DecidableRel (attach G P p id).Adj]
    (small : SmallTrivial (attach G P p id))
    (small4 : SmallFourTrivial (attach G P p id))
    (clean : NoFourCycle (attach G P p id))
    (cub : ∀ x,(attach G P p id).degree x = 3)
    (order : Fintype.card (V⊕Fin 5)%6=4)
    (p14 : ¬ G.Adj (p 1) (p 4)) (e23 : P.Adj 2 3)
    (H : SimpleGraph (V⊕Fin 5))
    (h12 : H.Adj (Sum.inr 1) (Sum.inr 2))
    (h23 : H.Adj (Sum.inr 2) (Sum.inr 3))
    (h34 : H.Adj (Sum.inr 3) (Sum.inr 4))
    (h1 : H.Adj (Sum.inl (p 1)) (Sum.inr 1))
    (h4 : H.Adj (Sum.inl (p 4)) (Sum.inr 4))
    (keep : ∀ v w,G.Adj v w → H.Adj (Sum.inl v) (Sum.inl w)) :
    FactorOn H (univ.erase (Sum.inr 0)) := by
  classical
  have p23 := adjoining_contacts_nonadjacent clean e23
  have closed := good_pentagon_cap_of_cyclic5 small small4 cub p14 p23
  have capCub := path_cap_cubic (fun v=>cub (Sum.inl v)) (G:=G) (p:=p)
  have f := stub_factor_of_good_path_cap t2 closed capCub order
  exact PentagonTransfer.close_pentagon_at_zero
    (fun h=> (by decide : (1:Port) ≠ 4) (p.injective h)) f H h12 h23 h34 h1 h4 keep

#print axioms stub_factor_of_good_path_cap
#print axioms adjoining_contacts_nonadjacent
#print axioms pentagon_root_case_of_cyclic5

end
end KelmansCactus.AtomicBridge.PentagonCap
