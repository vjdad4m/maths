import P5CliqueIndependentExcessThree133
import P5CliqueIndependentPureSaturation133
import P5CliqueHighExcessPorts133
import HexFlattened133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133 Graffiti133Camby Graffiti133FourPortPacking
open scoped BigOperators Classical
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem mean_core_three_for_saturation (D : Finset V)
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

/-- Independent four-port density whenever the core has at least sixteen
vertices, the total extra attachment count is at most three, or an exterior
vertex has at least three inward attachments. -/
theorem independent_four_ports_mean_four_of_size_or_large_contact
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (regime : let Q := (Finset.univ : Finset V)\D
      let d (q : V) := (D.filter (G.Adj q)).card
      let E := ∑ q∈Q,(d q-1)
      E≤3 ∨ 16≤D.card ∨ ∃ q∈Q,3≤d q) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let d (q : V) := (D.filter (G.Adj q)).card
  let E := ∑ q∈Q,(d q-1)
  let P := (Finset.univ : Finset (Fin 4)).image p
  let A := Q.filter (fun q=>3<localIndependence G q ∧ d q=1)
  let IsB (q : V) := 3<localIndependence G q ∧ 2≤d q ∧ d q≠3
  let B := Q.filter IsB
  by_cases few : E≤3
  · exact independent_four_ports_excess_at_most_three_ambient_mean_four h4 h9 D p pm pi ind attach palette hc h7 few
  have qout (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  have dis : Disjoint Q D := Finset.disjoint_left.mpr qout
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
  have dm (q : V) (qm : q∈Q) : d q=(portMask G P q).card :=
    congrArg Finset.card (contact q qm)
  have em : E=portExcess G P Q := by
    exact Finset.sum_congr rfl (fun q qm=> congrArg (fun x : Nat=>x-1) (dm q qm))
  have cap (q : V) (qm : q∈Q) : d q≤4 := by
    rw [dm q qm,←p4]
    exact Finset.card_le_card (fun x hx=>(mem_portMask P q x |>.mp hx).1)
  have pp := pair_charge h4 P Q D dis
  rw [p4,show Nat.choose 4 2=6 by decide] at pp
  have totalP : (∑ q∈Q,(d q).choose 2)≤6 := by
    calc
      _ = ∑ q∈Q,(portMask G P q).card.choose 2 := Finset.sum_congr rfl (fun q qm=>by rw [dm q qm])
      _ ≤ 6 := by omega
  have e6 : E≤6 := by
    have b := portExcess_le_pair_weight (G:=G) P Q
    omega
  have noFour (x : V) (xd : x∈D) : ¬∀ j : Fin 4,G.Adj (p j) x := by
    intro full
    apply few
    have ez (q : V) (qm : q∈Q) : d q=1 := by
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
      change (D.filter (G.Adj q)).card=1
      rw [y,Finset.card_singleton]
    have zero : E=0 := by
      unfold E
      exact Finset.sum_eq_zero (fun q qm=>by rw [ez q qm,Nat.sub_self])
    omega
  obtain ⟨a,good⟩ := four_ports_exists_anchor_without_triple_neighbor h4 D p pi noFour
  have pure6 := four_port_pure_highs_at_most_six_of_good_anchor h4 h9 D p pm pi ind attach palette hc h7 a good
  change A.card≤6 at pure6
  have pure4 (hi : 5≤E) : A.card≤4 := by
    have hi' : 5≤portExcess G P Q := em ▸ hi
    have gd := high_excess_every_anchor_without_triple_neighbor h4 p pi Q D dis hi'
    have par (h : Fin 4) := high_excess_two_foreign_ports h4 p pi Q hi' h
    apply four_port_pure_highs_at_most_four_when_pairs_occupied h4 h9 D p pm pi ind attach palette hc h7 gd
    intro h
    obtain ⟨a,b,ah,bh,ab,⟨x,xq,xh,xa⟩,⟨y,yq,yh,yb⟩⟩ := par h
    exact ⟨a,b,ah,bh,ab,⟨x,qout _ xq,xh,xa⟩,⟨y,qout _ yq,yh,yb⟩⟩
  have point (q : V) : (if IsB q then 1 else 0 : Nat)≤d q-1 := by
    by_cases b : IsB q
    · rw [if_pos b]
      have z := b.2.1
      omega
    · rw [if_neg b]
      exact Nat.zero_le _
  have bE : B.card≤E := by
    change (Q.filter IsB).card≤E
    rw [Finset.card_filter]
    exact Finset.sum_le_sum (fun q _=>point q)
  change E≤3 ∨ 16≤D.card ∨ ∃ q∈Q,3≤d q at regime
  rcases regime with bad|large|⟨s,sm,s3⟩
  · exact (few bad).elim
  · have cost : E+A.card+B.card≤16 := by
      by_cases high : 5≤E
      · have c := pure4 high
        omega
      omega
    have budget := mean_core_three_for_saturation D h4 hc h7
    apply independent_four_port_ambient_of_signed_high_counts h4 D p pm pi attach palette
    change (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+E+A.card+B.card≤4*D.card
    omega
  have bRes : B.card+2≤E := by
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
    have e : (∑ q∈Q,(if q=s then 2 else 0 : Nat))=2 := by simp [sm]
    have h := Finset.sum_le_sum refined
    rw [Finset.sum_add_distrib,e,←Finset.card_filter] at h
    exact h
  have e5 : E≤5 := by
    have pointwise (q : V) (qm : q∈Q) :
        (d q-1)+(if q=s then 1 else 0)≤(d q).choose 2 := by
      have cert : ∀ n : Fin 5,n.val-1≤ n.val.choose 2 ∧
          (3≤n.val→n.val-1+1≤n.val.choose 2) := by decide
      have r := cert ⟨d q,by have c:=cap q qm; omega⟩
      by_cases eq : q=s
      · subst q
        rw [if_pos rfl]
        exact r.2 s3
      · rw [if_neg eq,Nat.add_zero]
        exact r.1
    have add : (∑ q∈Q,(if q=s then 1 else 0 : Nat))=1 := by simp [sm]
    have weight := Finset.sum_le_sum pointwise
    rw [Finset.sum_add_distrib,add] at weight
    change E+1≤∑ q∈Q,(d q).choose 2 at weight
    omega
  apply independent_four_port_ambient_of_signed_exterior_cost h4 D p pm pi ind attach palette hc h7
  change E+A.card+B.card≤12 ∧ (E=0→E+A.card+B.card≤10)
  constructor
  · by_cases high : 5≤E
    · have c := pure4 high
      omega
    omega
  · omega

#print axioms independent_four_ports_mean_four_of_size_or_large_contact
end Graffiti133P5CliqueArms
