import P5CliqueMixedFivePairActual133
import P5CliqueFiveDoubleProfiles133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133 Graffiti133Camby Graffiti133FourPortPacking
open scoped BigOperators Classical
set_option maxHeartbeats 3500000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- At excess five with only single and double contacts, at most three
external vertices are both doubly attached and score four. -/
theorem five_double_pair_high_count_at_most_three
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ x∉D,∃ i,G.Adj x (p i))
    (palette : ∀ x∉D,∀ w∈D,G.Adj x w→∃ i,w=p i)
    (many : let Q := (Finset.univ : Finset V)\D
      (∑ q∈Q,((D.filter (G.Adj q)).card-1))=5)
    (cap : ∀ x∉D,(D.filter (G.Adj x)).card≤2) :
    let Q := (Finset.univ : Finset V)\D
    (Q.filter (fun x=>3<localIndependence G x ∧ (D.filter (G.Adj x)).card=2)).card≤3 := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P := (Finset.univ : Finset (Fin 4)).image p
  let d (x : V) := (D.filter (G.Adj x)).card
  let E := ∑ x∈Q,(d x-1)
  let B := Q.filter (fun x=>3<localIndependence G x ∧ d x=2)
  have out (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have eq (q : V) (qm : q∈Q) : D.filter (G.Adj q)=portMask G P q := by
    ext x
    rw [Finset.mem_filter,mem_portMask]
    constructor
    · rintro ⟨xd,ad⟩
      obtain ⟨i,rfl⟩ := palette q (out _ qm) x xd ad
      exact ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,ad⟩
    · rintro ⟨xp,ad⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xp
      exact ⟨pm i,ad⟩
  have de (q : V) (qm : q∈Q) : d q=(portMask G P q).card :=
    congrArg Finset.card (eq q qm)
  have em : E=portExcess G P Q :=
    Finset.sum_congr rfl (fun q qm=>congrArg (fun r : Nat=>r-1) (de q qm))
  have high : portExcess G P Q=5 := em.symm.trans many
  have pc (q : V) (qm : q∈Q) : (portMask G P q).card≤2 := de q qm ▸ cap q (out q qm)
  obtain ⟨e,q,qi,qin,last,full⟩ := excess_five_all_double_normalize h4 p pi Q high pc
  let S := (Finset.univ : Finset (Fin 5)).filter (fun i=>3<localIndependence G (q i))
  have bSub : B⊆S.image q := by
    intro x xm
    obtain ⟨xm,high,d2⟩ := Finset.mem_filter.mp xm
    obtain ⟨i,rfl⟩ := full x xm ((de x xm).symm.trans d2)
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,high⟩,rfl⟩
  have bs : B.card≤S.card := by
    have le := Finset.card_le_card bSub
    rwa [Finset.card_image_of_injective _ qi] at le
  change B.card≤3
  by_cases b3 : B.card≤3
  · exact b3
  exfalso
  let M := (Finset.univ : Finset (Fin 5))\S
  have mc : M.card≤1 := by
    have eq := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ] at eq
    change M.card+S.card=5 at eq
    omega
  have select : ∃ b : Fin 5,∀ i≠b,3<localIndependence G (q i) := by
    by_cases mn : M.Nonempty
    · obtain ⟨b,bm⟩ := mn
      refine ⟨b,fun i ib=>?_⟩
      by_cases im : i∈S
      · exact (Finset.mem_filter.mp im).2
      have m : i∈M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,im⟩
      exact (ib (Finset.card_le_one.mp mc i m b bm)).elim
    refine ⟨0,fun i _=>?_⟩
    by_cases im : i∈S
    · exact (Finset.mem_filter.mp im).2
    exact (mn ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,im⟩⟩).elim
  obtain ⟨b,hb⟩ := select
  let t := p∘e
  have atm (x : V) (xo : x∉D) : ∃ i,G.Adj x (t i) := by
    obtain ⟨i,xi⟩ := attach x xo
    exact ⟨e.symm i,by simpa [t] using xi⟩
  have ptr (x : V) (xo : x∉D) (y : V) (yd : y∈D) (ad : G.Adj x y) : ∃ i,y=t i := by
    obtain ⟨i,e'⟩ := palette x xo y yd ad
    exact ⟨e.symm i,by simpa [t] using e'⟩
  exact FivePairFrame.five_pair_four_high_forbidden h4 h9 D t (fun i=>pm (e i)) (pi.comp e.injective)
    (fun i j=>ind (e i) (e j)) atm ptr q (fun i=>out _ (qin i)) last b hb

#print axioms five_double_pair_high_count_at_most_three
end Graffiti133P5CliqueArms
