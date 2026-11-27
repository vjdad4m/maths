import P5CliqueIndependentPureAnchor133
import P5CliqueIndependentTripleAnchor133
import P5CliqueIndependentLowExcess133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133 Graffiti133Camby
open scoped BigOperators Classical
set_option maxHeartbeats 2800000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

/-- Independent four-port density closure with up to three extra inward
attachments, with no relay, stem, order or multiplicity subtype restrictions. -/
theorem independent_four_ports_excess_at_most_three_ambient_mean_four
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (few : let Q := (Finset.univ : Finset V)\D
      (∑ q∈Q,((D.filter (G.Adj q)).card-1))≤3) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let d (q : V) := (D.filter (G.Adj q)).card
  let E := ∑ q∈Q,(d q-1)
  have qout (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  by_cases four : ∃ x∈D,∀ j : Fin 4,G.Adj (p j) x
  · obtain ⟨x,xd,full⟩ := four
    have eq (q : V) (qm : q∈Q) : d q=1 := by
      obtain ⟨i,qi⟩ := attach q (qout _ qm)
      have y : D.filter (G.Adj q)={p i} := by
        ext b
        rw [Finset.mem_filter,Finset.mem_singleton]
        constructor
        · rintro ⟨bd,qb⟩
          obtain ⟨j,rfl⟩ := palette q (qout _ qm) b bd qb
          by_cases same : p j=p i
          · exact same
          exact (qout q qm ((h4 (p j) (p i) q x same qb.symm qi.symm (full j) (full i)).symm ▸ xd)).elim
        · rintro rfl
          exact ⟨pm _,qi⟩
      unfold d
      rw [y,Finset.card_singleton]
    have ez : E=0 := by
      unfold E
      apply Finset.sum_eq_zero
      intro q qm
      rw [eq q qm,Nat.sub_self]
    exact independent_four_ports_low_excess_ambient_mean_four h4 h9 D p pm pi ind attach palette hc h7
      (Or.inl (show E≤2 by omega))
  have noFour (u : V) (ud : u∈D) : ¬∀ j : Fin 4,G.Adj (p j) u := fun h=>four ⟨u,ud,h⟩
  obtain ⟨a,good⟩ := four_ports_exists_anchor_without_triple_neighbor h4 D p pi noFour
  have pureCap := four_port_pure_highs_at_most_six_of_good_anchor h4 h9 D p pm pi ind attach palette hc h7 a good
  let P := Q.filter (fun q=>3<localIndependence G q ∧ d q=1)
  let IsB (q : V) := 3<localIndependence G q ∧ 2≤d q ∧ d q≠3
  let B := Q.filter IsB
  change P.card≤6 at pureCap
  have bE : B.card≤E := by
    change (Q.filter IsB).card≤E
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro q _
    by_cases h : IsB q
    · rw [if_pos h]
      have e := h.2.1
      omega
    · rw [if_neg h]
      exact Nat.zero_le _
  apply independent_four_port_ambient_of_signed_exterior_cost h4 D p pm pi ind attach palette hc h7
  change E≤3 at few
  change E+P.card+B.card≤12 ∧ (E=0→E+P.card+B.card≤10)
  constructor <;> omega

#print axioms independent_four_ports_excess_at_most_three_ambient_mean_four
end Graffiti133P5CliqueArms
