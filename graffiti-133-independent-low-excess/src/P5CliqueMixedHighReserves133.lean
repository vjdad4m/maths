import P5CliqueMixedHighGeometry133
import P5CliqueMultiPortBudget133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem exterior_high_triples_supply_distinct_signed_deficits
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i) :
    let Q := (Finset.univ : Finset V)\D
    (∑ v∈Q,localIndependence G v) +
      (Q.filter (fun q=>3<localIndependence G q ∧ (D.filter (G.Adj q)).card=3)).card ≤
      3*Q.card+(Q.filter (fun v=>3<localIndependence G v)).card := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let H := Q.filter (fun q=>3<localIndependence G q)
  let W := Q.filter (fun q=>3<localIndependence G q ∧ (D.filter (G.Adj q)).card=3)
  let I (q : V) := (Finset.univ : Finset (Fin 4)).filter (fun j=>G.Adj q (p j))
  have univ4 : (Finset.univ : Finset (Fin 4)).card=4 := by decide
  have out (q : V) (m : q∈Q) : q∉D := (Finset.mem_sdiff.mp m).2
  have eqI (q : V) (oq : q∉D) : (I q).card = (D.filter (G.Adj q)).card := by
    have e : (I q).image p=D.filter (G.Adj q) := by
      ext v
      constructor
      · intro vm
        obtain ⟨i,im,rfl⟩ := Finset.mem_image.mp vm
        exact Finset.mem_filter.mpr ⟨pm _,(Finset.mem_filter.mp im).2⟩
      · intro vm
        obtain ⟨vd,ad⟩ := Finset.mem_filter.mp vm
        obtain ⟨i,rfl⟩ := palette q oq v vd ad
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ad⟩,rfl⟩
    rw [←e,Finset.card_image_of_injective _ pi]
  have representative (q : {v : V // v∈W}) : ∃ (i : Fin 4) (v : V),
      ¬G.Adj q.val (p i) ∧ v∉D ∧ G.Adj q.val v ∧
        ∀ w∈D,G.Adj v w↔w=p i := by
    obtain ⟨qm,qh,q3⟩ := Finset.mem_filter.mp q.property
    have qo := out _ qm
    have i3 : (I q.val).card=3 := (eqI _ qo).trans q3
    have miss : ∃ i : Fin 4,¬G.Adj q.val (p i) := by
      by_contra! a
      have e : I q.val=Finset.univ := by ext i; simp [I,a i]
      rw [e,univ4] at i3
      omega
    obtain ⟨i,mi⟩ := miss
    obtain ⟨v,vo,qv,only⟩ :=
      mixed_high_has_pure_foreign_representatives h4 D p pm pi attach palette _ qo qh i mi
    exact ⟨i,v,mi,vo,qv,only⟩
  choose lab leaf ml ov adj only using representative
  have leaf_inj : Function.Injective leaf := by
    intro a b ab
    apply Subtype.ext
    have labEq : lab a=lab b := by
      apply pi
      exact (only b _ (pm (lab a))).mp (ab ▸ (only a _ (pm (lab a))).mpr rfl)
    have cd (q : {v : V // v∈W}) : 2≤(I q.val).card := by
      rw [eqI _ (out _ (Finset.mem_filter.mp q.property).1),(Finset.mem_filter.mp q.property).2.2]
      decide
    have mb : ¬G.Adj b.val (p (lab a)) := labEq.symm ▸ ml b
    exact unique_mixed_center_at_pure_foreign_leaf h4 D p pm a.val b.val (leaf a) (ov a)
      (adj a) (ab.symm ▸ adj b) (lab a) (ml a) mb (cd a) (cd b)
  let Z := (Finset.univ : Finset {v : V // v∈W}).image leaf
  have zc : Z.card=W.card := by
    rw [Finset.card_image_of_injective _ leaf_inj,Finset.card_univ,Fintype.card_coe]
  have zo (v : V) (vm : v∈Z) : v∈Q ∧ localIndependence G v≤2 := by
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp vm
    obtain ⟨qm,_,q3⟩ := Finset.mem_filter.mp q.property
    have cap := pure_foreign_neighbor_signed_cap h4 D p pm pi attach palette
      (leaf q) q.val (ov q) (out _ qm) (adj q).symm (lab q) (only q) (ml q)
    rw [q3] at cap
    exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ov q⟩,by omega⟩
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  choose tag htag using attach
  let f (q : V) := if h : q∉D then p (tag q h) else q
  have pk (v : V) (vo : v∉D) : f v∈D ∧ f v∈P ∧ G.Adj v (f v) := by
    rw [show f v=p (tag v vo) from dif_pos vo]
    exact ⟨pm _,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,htag v vo⟩
  have pP (v : V) (vo : v∉D) (w : V) (wd : w∈D) (vw : G.Adj v w) : w∈P := by
    obtain ⟨j,e⟩ := palette v vo w wd vw
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e.symm⟩
  have point (v : V) (vm : v∈Q) :
      localIndependence G v+(if v∈Z then 1 else 0)≤3+(if v∈H then 1 else 0) := by
    by_cases vz : v∈Z
    · rw [if_pos vz]
      have s := (zo v vz).2
      omega
    rw [if_neg vz,Nat.add_zero]
    by_cases hi : 3<localIndependence G v
    · rw [if_pos (Finset.mem_filter.mpr ⟨vm,hi⟩)]
      have cap := outside_independence_le_attachment_palette h4 D P f pk pP v (out _ vm)
      rw [p4] at cap
      exact cap
    · have hh : v∉H := fun h=>hi (Finset.mem_filter.mp h).2
      rw [if_neg hh]
      omega
  have sum := Finset.sum_le_sum point
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at sum
  have zs : (∑ v∈Q,(if v∈Z then 1 else 0 : Nat))=Z.card := by
    rw [←Finset.card_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h=>h.2,fun h=>⟨(zo v h).1,h⟩⟩
  have hs : (∑ v∈Q,(if v∈H then 1 else 0 : Nat))=H.card := by
    rw [←Finset.card_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter,H]
    tauto
  have cs : (∑ _v∈Q,(3:Nat))=3*Q.card := by simp [Nat.mul_comm]
  rw [zs,hs,cs,zc] at sum
  exact sum

#print axioms exterior_high_triples_supply_distinct_signed_deficits
end Graffiti133P5CliqueArms
