import P5CliqueIndependentShortCoreSlack133
import P5CliqueIndependentSignedCharge133
import P5CliqueSecondWedgeSlack133
import HexFlattened133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133 Graffiti133Camby
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem mean_core_three (D : Finset V)
    (h4 : FourCycleFree G) (hc : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)≤3*D.card := by
  classical
  let J := G.induce (D : Set V)
  have four : FourCycleFree J := by
    intro a b x y ne ax bx ay by'
    exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
  have eq : Fintype.card (D : Set V)=D.card := Fintype.card_coe _
  change (∑ x : (D : Set V),localIndependence J x)≤3*D.card
  by_contra h
  have high : 3*Fintype.card (D : Set V)<∑ x : (D : Set V),localIndependence J x := by omega
  have mean : 3<averageLocal J := by
    letI := hc.nonempty
    have pos : (0:ℚ)<(Fintype.card (D : Set V):ℚ) := by exact_mod_cast Fintype.card_pos (α:=(D : Set V))
    unfold averageLocal
    apply (lt_div_iff₀ pos).mpr
    rw [← Nat.cast_sum]
    exact_mod_cast high
  exact h7 (Graffiti133Revisit.P7_of_strict_mean_three J hc four mean)

/-- A signed exterior cost of twelve units suffices for an independent four-port
palette. When there is no extra attachment, ten units suffice. All core orders
are covered; the exterior cost itself remains an explicit hypothesis. -/
theorem independent_four_port_ambient_of_signed_exterior_cost
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (caps : let Q := (Finset.univ : Finset V)\D
      let d (q : V) := (D.filter (G.Adj q)).card
      let E := ∑ q∈Q,(d q-1)
      let A := (Q.filter (fun q=>3<localIndependence G q ∧ d q=1)).card
      let B := (Q.filter (fun q=>3<localIndependence G q ∧ 2≤d q ∧ d q≠3)).card
      E+A+B≤12 ∧ (E=0→E+A+B≤10)) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let d (q : V) := (D.filter (G.Adj q)).card
  let E := ∑ q∈Q,(d q-1)
  let AA := (Q.filter (fun q=>3<localIndependence G q ∧ d q=1)).card
  let B := (Q.filter (fun q=>3<localIndependence G q ∧ 2≤d q ∧ d q≠3)).card
  let P := (Finset.univ : Finset (Fin 4)).image p
  let J := G.induce (D : Set V)
  let pj (i : Fin 4) : (D : Set V) := ⟨p i,pm i⟩
  let Pj := (Finset.univ : Finset (Fin 4)).image pj
  letI : DecidableRel J.Adj := Classical.decRel _
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  have ipj : Function.Injective pj := fun i j e=>pi (congrArg Subtype.val e)
  have pj4 : Pj.card=4 := by rw [Finset.card_image_of_injective _ ipj,Finset.card_univ]; decide
  have dj : Fintype.card (D : Set V)=D.card := Fintype.card_coe _
  have d4 : 4≤D.card := by
    have e := Finset.card_le_card (s:=P) (t:=D) (by
      intro x xm
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xm
      exact pm i)
    omega
  have hJ : FourCycleFree J := by
    intro a b x y ne ax bx ay by'
    exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
  have pindj (x : (D : Set V)) (xm : x∈Pj) (y : (D : Set V)) (ym : y∈Pj) : ¬J.Adj x y := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xm
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ym
    exact ind i j
  have outerDom (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  change E+AA+B≤12 ∧ (E=0→E+AA+B≤10) at caps
  have cls := mean_core_three D h4 hc h7
  change (∑ u : (D : Set V),localIndependence J u)≤3*D.card at cls
  have fin : (∑ u : (D : Set V),localIndependence J u)+E+AA+B≤4*D.card := by
    by_cases large : 12≤D.card
    · omega
    by_cases small : D.card≤9
    · have slack : (∑ u : (D : Set V),localIndependence J u)+12≤4*D.card := by
        by_cases n5 : D.card≤5
        · have e := independent_four_ports_small_core_twelve_slack (G:=J) Pj pj4 pindj (by omega)
          rwa [dj] at e
        have e := small_core_twelve_signed_slack J (by omega) (by omega) hJ
        rwa [dj] at e
      omega
    by_cases n11 : D.card=11
    · have xx := SecondWedge.order_eleven_below_three_twelve_signed_slack J (by omega) hJ (by omega)
      omega
    have j10 : Fintype.card (D : Set V)=10 := by omega
    by_cases zero : E=0
    · have a := caps.2 zero
      omega
    have pair : ∃ q∈Q,2≤d q := by
      by_cases existsQ : ∃ q∈Q,2≤d q
      · exact existsQ
      exfalso
      have eo : E=0 := by
        unfold E
        apply Finset.sum_eq_zero
        intro q qm
        have a : ¬2≤d q := fun bad=>existsQ ⟨q,qm,bad⟩
        omega
      omega
    obtain ⟨x,xq,x2⟩ := pair
    obtain ⟨a,am,b,bm,ab⟩ := Finset.one_lt_card.mp x2
    obtain ⟨ad,ax⟩ := Finset.mem_filter.mp am
    obtain ⟨bd,bx⟩ := Finset.mem_filter.mp bm
    let u : (D : Set V) := ⟨a,ad⟩
    let v : (D : Set V) := ⟨b,bd⟩
    have uv : u≠v := fun e=>ab (congrArg Subtype.val e)
    have un : ¬J.Adj u v := by
      obtain ⟨i,e⟩ := palette x (outerDom x xq) a ad ax
      obtain ⟨j,f⟩ := palette x (outerDom x xq) b bd bx
      change ¬G.Adj a b
      rw [e,f]
      exact ind i j
    have noc : ¬∃ w,J.Adj u w ∧ J.Adj v w := by
      rintro ⟨w,uw,vw⟩
      exact outerDom x xq ((h4 a b x w.val ab ax.symm bx.symm uw vw).symm ▸ w.property)
    have raw := SecondWedge.order_ten_with_unrepresented_nonedge_twelve_signed_slack J j10 hJ u v uv un noc
    rw [dj] at raw
    omega
  exact independent_four_port_ambient_of_signed_high_counts h4 D p pm pi attach palette fin

#print axioms independent_four_port_ambient_of_signed_exterior_cost
end Graffiti133P5CliqueArms
