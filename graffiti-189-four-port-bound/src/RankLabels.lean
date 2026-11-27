import SingleTwoBounds189
import BFSOrder189
import Bridge251Common
import SingleCage

namespace Graffiti189SingletonCage
open SimpleGraph Finset GraphPathLift
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V]

lemma exists_sorted_equiv (rank : V→ℕ) :
    ∃ e : Fin (Fintype.card V) ≃ V, Monotone (rank ∘ e) := by
  classical
  let rel (v w : V) : Prop := rank v≤rank w
  letI : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))
  letI : IsTotal V rel := ⟨fun x y => Nat.le_total (rank x) (rank y)⟩
  letI : IsTrans V rel := ⟨fun x y z a b => Nat.le_trans a b⟩
  letI : IsRefl V rel := ⟨fun x=>Nat.le_refl (rank x)⟩
  let L₀ := (Finset.univ : Finset V).toList
  let L := L₀.mergeSort (fun x y => decide (rel x y))
  have perm : L.Perm L₀ := List.mergeSort_perm _ _
  have len : L.length = Fintype.card V := perm.length_eq.trans (by simp [L₀])
  have hh : L.Nodup := perm.symm.nodup (Finset.nodup_toList _)
  have hall (v : V) : v∈L := perm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ _))
  have sorted : L.Sorted rel := List.sorted_mergeSort' rel L₀
  let f : Fin L.length ≃ V := hh.getEquivOfForallMemList L hall
  let ec : Fin (Fintype.card V) ≃ Fin L.length :=
    ⟨Fin.cast len.symm, Fin.cast len, fun i => Fin.ext rfl, fun i => Fin.ext rfl⟩
  refine ⟨ec.trans f,?_⟩
  intro i j ij
  change rel (L.get (ec i)) (L.get (ec j))
  exact sorted.rel_get_of_le (show ec i ≤ ec j from ij)

private lemma cutoff_card_iso (rank : V→ℕ) (e : Fin (Fintype.card V) ≃ V) (k : ℕ) :
    (univ.filter (fun i=>rank (e i)<k)).card=(univ.filter (fun v=>rank v<k)).card := by
  classical
  apply card_bij (fun i _=>e i)
  · intro i hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
  · intro i _ j _ eq; exact e.injective eq
  · intro v hv
    obtain ⟨j,rfl⟩ := e.surjective v
    exact ⟨j,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩,rfl⟩

lemma rank_cut_iff (rank : V→ℕ) (e : Fin (Fintype.card V) ≃ V) (mono : Monotone (rank ∘ e))
    (i : Fin (Fintype.card V)) (k : ℕ) :
    rank (e i)<k ↔ i.val<(univ.filter (fun v=>rank v<k)).card := by
  rw [←cutoff_card_iso rank e]
  exact prefix_filter_iff (fun i=>rank (e i)<k) (fun i j e q=> (mono e).trans_lt q) i

/-- Connectivity after deleting at most one vertex is invariant under relabelling. -/
lemma cut_iso {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (v : Option V)
    (h : (H.induce (fun y=>v.map e≠some y)).Connected) :
    (G.induce (fun x=>v≠some x)).Connected := by
  have key (x : V) : v.map e ≠ some (e x) ↔ v ≠ some x := by
    cases v with
    | none => simp
    | some w => simp [e.injective.ne_iff]
  let f : H.induce (fun y=>v.map e≠some y) →g G.induce (fun x=>v≠some x) :=
    ⟨fun y=>⟨e.symm y.val, (key _).mp (by simpa using y.property)⟩,
     fun {u w} uw => e.symm.toHom.map_adj (show H.Adj u.val w.val from uw)⟩
  refine h.map f ?_
  intro u
  refine ⟨⟨e u.val,(key _).mpr u.property⟩,?_⟩
  apply Subtype.ext
  exact e.symm_apply_apply u.val

#print axioms rank_cut_iff
#print axioms cut_iso
end Graffiti189SingletonCage
