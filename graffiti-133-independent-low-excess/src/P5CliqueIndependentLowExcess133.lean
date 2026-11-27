import P5CliqueIndependentFanBudget133
import P5CliqueIndependentSignedCore133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133 Graffiti133Camby
open scoped BigOperators Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

/-- Extends the low-excess case to two excess attachments, and to three
when at least one vertex has three or more core attachments. -/
theorem independent_four_ports_low_excess_ambient_mean_four
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (low : let Q := (Finset.univ : Finset V)\D
      let d (q : V) := (D.filter (G.Adj q)).card
      let E := ∑ q∈Q,(d q-1)
      E≤2 ∨ (E=3 ∧ ∃ q∈Q,3≤d q)) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let d (q : V) := (D.filter (G.Adj q)).card
  let E := ∑ q∈Q,(d q-1)
  let high (q : V) := 3<localIndependence G q
  let H := Q.filter high
  let P := Q.filter (fun q=>high q ∧ d q=1)
  let M := Q.filter (fun q=>high q ∧ 2≤d q)
  let B := Q.filter (fun q=>high q ∧ 2≤d q ∧ d q≠3)
  have positive (q : V) (qm : q∈Q) : 0<d q := by
    obtain ⟨i,qa⟩ := attach q (Finset.mem_sdiff.mp qm).2
    exact Finset.card_pos.mpr ⟨p i,Finset.mem_filter.mpr ⟨pm i,qa⟩⟩
  have partition : P∪M=H := by
    ext q
    simp only [P,M,H,Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro (h|h) <;> exact ⟨h.1,h.2.1⟩
    rintro ⟨qm,qh⟩
    have h := positive q qm
    by_cases one : d q=1
    · exact Or.inl ⟨qm,qh,one⟩
    · exact Or.inr ⟨qm,qh,by omega⟩
  have dis : Disjoint P M := by
    apply Finset.disjoint_left.mpr
    intro q qp qm
    have a := (Finset.mem_filter.mp qp).2.2
    have b := (Finset.mem_filter.mp qm).2.2
    omega
  have cd := Finset.card_union_of_disjoint dis
  rw [partition] at cd
  have cap := independent_four_port_high_mixed_exact h4 h9 D p pm pi ind attach palette
  change H.card≤8+M.card at cap
  have pu : P.card≤8 := by omega
  let IsB (q : V) := high q ∧ 2≤d q ∧ d q≠3
  have point (q : V) : (if IsB q then 1 else 0 : Nat)≤d q-1 := by
    by_cases b : IsB q
    · rw [if_pos b]
      have z := b.2.1
      omega
    · rw [if_neg b]
      exact Nat.zero_le _
  have be : B.card≤E := by
    change (Q.filter IsB).card≤E
    rw [Finset.card_filter]
    exact Finset.sum_le_sum (fun q _=>point q)
  have bdef (s : V) (sm : s∈Q) (s3 : 3≤d s) : B.card+2≤E := by
    have refined (q : V) (_ : q∈Q) :
        (if IsB q then 1 else 0 : Nat)+(if q=s then 2 else 0)≤d q-1 := by
      by_cases eq : q=s
      · subst q
        rw [if_pos rfl]
        by_cases b : IsB s
        · rw [if_pos b]
          have ne := b.2.2
          omega
        · rw [if_neg b]
          omega
      · rw [if_neg eq,Nat.add_zero]
        exact point q
    have f : (∑ q∈Q,(if q=s then 2 else 0 : Nat))=2 := by simp [sm]
    have h := Finset.sum_le_sum refined
    rw [Finset.sum_add_distrib,f,←Finset.card_filter] at h
    exact h
  apply independent_four_port_ambient_of_signed_exterior_cost h4 D p pm pi ind attach palette hc h7
  change E+P.card+B.card≤12 ∧ (E=0→E+P.card+B.card≤10)
  change E≤2 ∨ (E=3 ∧ ∃ q∈Q,3≤d q) at low
  constructor
  · rcases low with l|⟨ee,q,qm,q3⟩
    · omega
    · have a := bdef q qm q3
      omega
  · omega

#print axioms independent_four_ports_low_excess_ambient_mean_four
end Graffiti133P5CliqueArms
