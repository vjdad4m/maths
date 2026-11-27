import P5CliqueFourPortPacking133
import P5CliqueIndependentPureAnchor133

namespace Graffiti133FourPortPacking
open SimpleGraph Finset Graffiti133
open scoped Classical BigOperators
set_option maxHeartbeats 2000000
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def fiveDoubleTable : Fin 5 → Finset (Fin 4) :=
  ![{0,1}, {0,2}, {0,3}, {1,2}, {1,3}]

private theorem fiveDoubleTable_card : ∀ i, (fiveDoubleTable i).card = 2 := by decide
private theorem fiveDoubleTable_ne_missing : ∀ i, fiveDoubleTable i ≠ {2,3} := by decide
private theorem fiveDoubleTable_injective : Function.Injective fiveDoubleTable := by decide

theorem excess_five_all_double_normalize (h4 : FourCycleFree G)
    (p : Fin 4 → V) (pi : Function.Injective p) (Q : Finset V)
    (E : portExcess G (Finset.univ.image p) Q = 5)
    (cap : ∀x∈Q, (portMask G (Finset.univ.image p) x).card ≤ 2) :
    ∃ (e : Fin 4 ≃ Fin 4) (q : Fin 5 → V),
      Function.Injective q ∧ (∀ i, q i ∈ Q) ∧
      (∀ i j, G.Adj (q i) (p (e j)) ↔ j ∈ fiveDoubleTable i) ∧
      (∀ x∈Q, (portMask G (Finset.univ.image p) x).card = 2 → ∃ i, q i = x) := by
  classical
  let P := Finset.univ.image p
  let U := P.powersetCard 2
  let R := representedPortPairs G P Q
  let A := Q.filter fun x => (portMask G P x).card = 2
  have rcard : R.card = 5 := by
    rw [show R = representedPortPairs G P Q from rfl, represented_card h4, ← E]
    apply Finset.sum_congr rfl
    intro x hx
    have b := cap x hx
    change (portMask G P x).card ≤ 2 at b
    have cases : (portMask G P x).card = 0 ∨ (portMask G P x).card = 1 ∨ (portMask G P x).card = 2 := by omega
    change (portMask G P x).card.choose 2 = (portMask G P x).card - 1
    rcases cases with h | h | h <;> rw [h] <;> decide
  have acard : A.card = 5 := by
    have c := portExcess_counts (G:=G) P Q (fun x hx => (cap x hx).trans (by omega))
    have z : (Q.filter fun x => (portMask G P x).card = 3) = ∅ := by
      apply Finset.subset_empty.mp
      intro x hx
      obtain ⟨hx,h⟩ := Finset.mem_filter.mp hx
      have b := cap x hx
      change (portMask G P x).card ≤ 2 at b
      exfalso
      omega
    change portExcess G P Q = 5 at E
    simpa [A,z,E] using c.symm
  have four : P.card = 4 := by simp [P, Finset.card_image_of_injective, pi]
  have six : U.card = 6 := by rw [show U = P.powersetCard 2 from rfl, Finset.card_powersetCard, four]; decide
  have sub : R ⊆ U := by
    intro s hs
    obtain ⟨c,v,_,info⟩ := (mem_representedPortPairs P Q s).mp hs
    exact Finset.mem_powersetCard.mpr ⟨fun u hu => (info u hu).1, c⟩
  have missing : (U \ R).card = 1 := by rw [Finset.card_sdiff sub, rcard, six]
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp missing
  have sm : s ∈ U \ R := by simp [hs]
  obtain ⟨a,b,ab,eqs⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp sm).1).2
  have as : a ∈ s := by simp [eqs]
  have bs : b ∈ s := by simp [eqs]
  obtain ⟨a', _,ae⟩ := Finset.mem_image.mp ((Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp sm).1).1 as)
  obtain ⟨b', _,be⟩ := Finset.mem_image.mp ((Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp sm).1).1 bs)
  have ab' : a' ≠ b' := by intro h; exact ab (ae.symm.trans ((congrArg p h).trans be))
  let C := ((Finset.univ : Finset (Fin 4)).erase b').erase a'
  have cardC : C.card = 2 := by simp [C, Finset.card_erase_of_mem, ab']
  obtain ⟨c',hc'⟩ := Finset.card_pos.mp (show 0 < C.card by omega)
  have ca' := (Finset.mem_erase.mp hc').1
  have cb' := (Finset.mem_erase.mp (Finset.mem_erase.mp hc').2).1
  obtain ⟨f,f0,f1,_⟩ := Graffiti133P5CliqueArms.put_three_labels a' b' c' ab' (Ne.symm ca') (Ne.symm cb')
  let e := (Equiv.swap (0 : Fin 4) 2).trans ((Equiv.swap (1 : Fin 4) 3).trans f)
  have e2 : e 2 = a' := by
    change f (Equiv.swap (1 : Fin 4) 3 (Equiv.swap 0 2 2)) = a'
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by decide : (0:Fin 4)≠1) (by decide : (0:Fin 4)≠3),f0]
  have e3 : e 3 = b' := by
    change f (Equiv.swap (1 : Fin 4) 3 (Equiv.swap 0 2 3)) = b'
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (3:Fin 4)≠0) (by decide : (3:Fin 4)≠2), Equiv.swap_apply_right,f1]
  let emb : Fin 4 ↪ V := ⟨p ∘ e, pi.comp e.injective⟩
  have se : ({2,3} : Finset (Fin 4)).map emb = s := by
    rw [eqs, Finset.map_insert, Finset.map_singleton]
    change ({p (e 2), p (e 3)} : Finset V) = {a,b}
    rw [e2,e3,ae,be]
  let M (i : Fin 5) := (fiveDoubleTable i).map emb
  have contained (i : Fin 5) : M i ⊆ P := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_image.mpr ⟨e j, Finset.mem_univ _, rfl⟩
  have mcard (i : Fin 5) : (M i).card = 2 := by simp [M, fiveDoubleTable_card]
  have outside (i : Fin 5) : M i ∈ R := by
    by_cases hn : M i ∈ R
    · exact hn
    exfalso
    have mem : M i ∈ U \ R := Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨contained i, mcard i⟩, hn⟩
    have eq : M i = s := by simpa [hs] using mem
    exact fiveDoubleTable_ne_missing i (Finset.map_injective emb (eq.trans se.symm))
  have has (i : Fin 5) : ∃ x∈Q, portMask G P x = M i := by
    obtain ⟨_,x,hx,info⟩ := (mem_representedPortPairs P Q (M i)).mp (outside i)
    have sub : M i ⊆ portMask G P x := fun y hy => (mem_portMask P x y).mpr (info y hy)
    refine ⟨x,hx,(Finset.eq_of_subset_of_card_le sub ?_).symm⟩
    rw [mcard]
    exact cap x hx
  choose q qQ qM using has
  have qinj : Function.Injective q := by
    intro i j eq
    apply fiveDoubleTable_injective
    apply Finset.map_injective (f := emb)
    exact (qM i).symm.trans ((congrArg (portMask G P) eq).trans (qM j))
  have im : Finset.univ.image q = A := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨qQ i, (congrArg Finset.card (qM i)).trans (mcard i)⟩
    · rw [Finset.card_image_of_injective _ qinj, acard]
      simp
  refine ⟨e,q,qinj,qQ,?_,?_⟩
  · intro i j
    have he : p (e j) ∈ P := Finset.mem_image.mpr ⟨e j, Finset.mem_univ _, rfl⟩
    constructor
    · intro hadj
      exact (Finset.mem_map' emb).mp (show emb j ∈ M i from qM i ▸ (mem_portMask P (q i) _).mpr ⟨he,hadj⟩)
    · intro hj
      have h : emb j ∈ M i := (Finset.mem_map' emb).mpr hj
      have hh : p (e j) ∈ portMask G P (q i) := (qM i).symm ▸ h
      exact ((mem_portMask P (q i) _).mp hh).2
  · intro x hx hc
    have h : x ∈ A := Finset.mem_filter.mpr ⟨hx,hc⟩
    rw [← im] at h
    obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
    exact ⟨i,he⟩

end Graffiti133FourPortPacking

#print axioms Graffiti133FourPortPacking.excess_five_all_double_normalize
