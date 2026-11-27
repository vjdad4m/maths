import P5CliqueIndependentSaturationDensity133
import P5CliqueFiveDoubleHighCap133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133 Graffiti133Camby Graffiti133FourPortPacking
open scoped BigOperators Classical
set_option maxHeartbeats 3500000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

/-- All independent four-port cores have ambient mean at most four when
the exact total excess is five, even with arbitrary individual masks. -/
theorem independent_four_ports_excess_exactly_five_ambient_mean_four
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (five : let Q := (Finset.univ : Finset V)\D
      (∑ q∈Q,((D.filter (G.Adj q)).card-1))=5) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P := (Finset.univ : Finset (Fin 4)).image p
  let d (q : V) := (D.filter (G.Adj q)).card
  let E := ∑ q∈Q,(d q-1)
  change E=5 at five
  by_cases mega : ∃ q∈Q,3≤d q
  · apply independent_four_ports_mean_four_of_size_or_large_contact h4 h9 D p pm pi ind attach palette hc h7
    exact Or.inr (Or.inr mega)
  have qout (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have cap (q : V) (qo : q∉D) : d q≤2 := by
    have z : ¬3≤d q := fun h=>mega ⟨q,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,qo⟩,h⟩
    omega
  have mix := five_double_pair_high_count_at_most_three h4 h9 D p pm pi ind attach palette five cap
  let A := Q.filter (fun q=>3<localIndependence G q ∧ d q=1)
  let B := Q.filter (fun q=>3<localIndependence G q ∧ 2≤d q ∧ d q≠3)
  let C := Q.filter (fun q=>3<localIndependence G q ∧ d q=2)
  change C.card≤3 at mix
  have bsub : B⊆C := by
    intro q qm
    obtain ⟨qQ,high,degree,_⟩ := Finset.mem_filter.mp qm
    have le := cap q (qout q qQ)
    exact Finset.mem_filter.mpr ⟨qQ,high,by omega⟩
  have b3 := (Finset.card_le_card bsub).trans mix
  have contact (q : V) (qm : q∈Q) : D.filter (G.Adj q)=portMask G P q := by
    ext x
    rw [Finset.mem_filter,mem_portMask]
    constructor
    · rintro ⟨xd,ad⟩
      obtain ⟨i,rfl⟩ := palette q (qout _ qm) x xd ad
      exact ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,ad⟩
    · rintro ⟨xp,ad⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xp
      exact ⟨pm i,ad⟩
  have em : E=portExcess G P Q :=
    Finset.sum_congr rfl (fun q qm=>congrArg (fun T=>T.card-1) (contact q qm))
  have large : 5≤portExcess G P Q := by rw [←em,five]
  have dis : Disjoint Q D := Finset.disjoint_left.mpr qout
  have good := high_excess_every_anchor_without_triple_neighbor h4 p pi Q D dis large
  have pure4 : A.card≤4 := by
    apply four_port_pure_highs_at_most_four_when_pairs_occupied h4 h9 D p pm pi ind attach palette hc h7 good
    intro h
    obtain ⟨a,b,ah,bh,ab,⟨x,xq,xh,xa⟩,⟨y,yq,yh,yb⟩⟩ :=
      high_excess_two_foreign_ports h4 p pi Q large h
    exact ⟨a,b,ah,bh,ab,⟨x,qout _ xq,xh,xa⟩,⟨y,qout _ yq,yh,yb⟩⟩
  apply independent_four_port_ambient_of_signed_exterior_cost h4 D p pm pi ind attach palette hc h7
  change E+A.card+B.card≤12 ∧ (E=0→E+A.card+B.card≤10)
  constructor <;> omega

#print axioms independent_four_ports_excess_exactly_five_ambient_mean_four
end Graffiti133P5CliqueArms
