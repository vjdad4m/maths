import P5CliqueMixedHighReserves133
import P5CliqueMultiPortBudget133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133 Graffiti133Camby
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem independent_four_port_ambient_of_signed_high_counts
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (slack : let Q := (Finset.univ : Finset V)\D
      (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+
        (∑ q∈Q,((D.filter (G.Adj q)).card-1))+
        (Q.filter (fun q=>3<localIndependence G q ∧ (D.filter (G.Adj q)).card=1)).card+
        (Q.filter (fun q=>3<localIndependence G q ∧ 2≤(D.filter (G.Adj q)).card ∧
          (D.filter (G.Adj q)).card≠3)).card≤4*D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let d (q : V) := (D.filter (G.Adj q)).card
  let H := Q.filter (fun q=>3<localIndependence G q)
  let P := H.filter (fun q=>d q=1)
  let B := H.filter (fun q=>2≤d q ∧ d q≠3)
  let W := H.filter (fun q=>d q=3)
  let E := ∑ q∈Q,(d q-1)
  have qout (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have copy := attach
  choose tag htag using copy
  let f (q : V) := if h:q∉D then p (tag q h) else q
  have pick (q : V) (qo : q∉D) : f q∈D ∧ G.Adj q (f q) := by
    rw [show f q=p (tag q qo) from dif_pos qo]
    exact ⟨pm _,htag q qo⟩
  have hpart : H⊆P∪B∪W := by
    intro q qm
    obtain ⟨qQ,qh⟩ := Finset.mem_filter.mp qm
    have positive : 0<d q := Finset.card_pos.mpr
      ⟨f q,Finset.mem_filter.mpr (pick q (qout q qQ))⟩
    by_cases one : d q=1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨qm,one⟩))))
    by_cases three : d q=3
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨qm,three⟩))
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
      (Finset.mem_filter.mpr ⟨qm,by omega,three⟩))))
  have part := (Finset.card_le_card hpart).trans (Finset.card_union_le _ _)
  have part' := Finset.card_union_le P B
  have charge := exterior_high_triples_supply_distinct_signed_deficits h4 D p pm pi attach palette
  have eqW : Q.filter (fun q=>3<localIndependence G q ∧ d q=3)=W := by
    ext q
    simp only [W,H,Finset.mem_filter,and_assoc]
  have eqP : Q.filter (fun q=>3<localIndependence G q ∧ d q=1)=P := by
    ext q
    simp only [P,H,Finset.mem_filter,and_assoc]
  have eqB : Q.filter (fun q=>3<localIndependence G q ∧ 2≤d q ∧ d q≠3)=B := by
    ext q
    simp only [B,H,Finset.mem_filter,and_assoc]
  change (∑ q∈Q,localIndependence G q)+
    (Q.filter (fun q=>3<localIndependence G q ∧ d q=3)).card≤3*Q.card+H.card at charge
  rw [eqW] at charge
  change (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+E+
    (Q.filter (fun q=>3<localIndependence G q ∧ d q=1)).card+
    (Q.filter (fun q=>3<localIndependence G q ∧ 2≤d q ∧ d q≠3)).card≤4*D.card at slack
  rw [eqP,eqB] at slack
  have sum := core_and_exterior_independence_sum (G:=G) D
  change (∑ v : V,localIndependence G v)≤
    (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+
    (∑ q∈Q,localIndependence G q)+(∑ q∈Q,d q) at sum
  have crossings := core_crossings_eq_card_add_extra D f pick
  change (∑ q∈Q,d q)=Q.card+E at crossings
  have cc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cc
  change Q.card+D.card=Fintype.card V at cc
  omega

#print axioms independent_four_port_ambient_of_signed_high_counts
end Graffiti133P5CliqueArms
