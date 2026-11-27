import FourOffGraphCore189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem order_sixteen_five_off_labeling
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=10)
    (off : ((univ : Finset V)\p.support.toFinset).card=5)
    (xo : x∉p.support) (yo : y∉p.support) (xy : x≠y) :
    ∃ φ : Fin 16→V, Function.Injective φ ∧ Function.Surjective φ ∧ φ 11=x ∧ φ 12=y ∧
      (∀ k : Fin 16,k.val≤10 → φ k=p.getVert k.val) ∧
      (∀ k : Fin 16,11≤k.val → φ k∉p.support) := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  let Q := (O.erase x).erase y
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  have xO := out.mpr xo
  have yO : y∈O.erase x := mem_erase.mpr ⟨xy.symm,out.mpr yo⟩
  have q3 : Q.card=3 := by
    change ((O.erase x).erase y).card=3
    rw [card_erase_of_mem yO,card_erase_of_mem xO,show O.card=5 from off]
  let e : Fin 3 ≃ Q := (Fintype.equivFinOfCardEq (by simpa using q3)).symm
  let φ : Fin 16→V := fun v =>
    if h : v.val≤10 then p.getVert v.val else
    if k : v.val=11 then x else
    if l : v.val=12 then y else
    (e ⟨v.val-13,by have vu := v.isLt; omega⟩).val
  have on (v : Fin 16) (h : v.val≤10) : φ v=p.getVert v.val := by simp [φ,h]
  have ae (v : Fin 16) (h : v.val=11) : φ v=x := by simp [φ,h]
  have be (v : Fin 16) (h : v.val=12) : φ v=y := by simp [φ,h]
  have after (v : Fin 16) (h : 13≤v.val) :
      φ v=(e ⟨v.val-13,by have vu := v.isLt; omega⟩).val := by
    simp [φ,show ¬v.val≤10 by omega,show v.val≠11 by omega,show v.val≠12 by omega]
  have afterQ (v : Fin 16) (hv : 13≤v.val) : φ v∈Q := by
    rw [after v hv]
    exact Subtype.property _
  have offP (v : Fin 16) (h : 11≤v.val) : φ v∉p.support := by
    by_cases h11 : v.val=11
    · rw [ae v h11]
      exact xo
    by_cases h12 : v.val=12
    · rw [be v h12]
      exact yo
    exact out.mp (mem_erase.mp (mem_erase.mp (afterQ v (by omega))).2).2
  have sameE (v : Fin 16) (h : φ v=x) : v.val=11 := by
    by_cases hv : v.val≤10
    · exact (xo (h ▸ ((on v hv).symm ▸ p.getVert_mem_support v.val))).elim
    by_cases ev : v.val=11
    · exact ev
    by_cases fv : v.val=12
    · exact (xy ((be v fv).symm.trans h).symm).elim
    exact ((mem_erase.mp (mem_erase.mp (afterQ v (by omega))).2).1 h).elim
  have sameF (v : Fin 16) (h : φ v=y) : v.val=12 := by
    by_cases hv : v.val≤10
    · exact (yo (h ▸ ((on v hv).symm ▸ p.getVert_mem_support v.val))).elim
    by_cases ev : v.val=11
    · exact (xy ((ae v ev).symm.trans h)).elim
    by_cases fv : v.val=12
    · exact fv
    exact ((mem_erase.mp (afterQ v (by omega))).1 h).elim
  have inj : Function.Injective φ := by
    intro u v h
    apply Fin.ext
    by_cases uo : u.val≤10 <;> by_cases vo : v.val≤10
    · exact hp.1.getVert_injOn (show u.val≤p.length by omega) (show v.val≤p.length by omega)
        ((on u uo).symm.trans (h.trans (on v vo)))
    · exact False.elim (offP v (by omega) (h ▸ ((on u uo).symm ▸ p.getVert_mem_support u.val)))
    · exact False.elim (offP u (by omega) (h.symm ▸ ((on v vo).symm ▸ p.getVert_mem_support v.val)))
    by_cases u11 : u.val=11
    · exact u11.trans (sameE v (h.symm.trans (ae u u11))).symm
    by_cases v11 : v.val=11
    · exact (sameE u (h.trans (ae v v11))).trans v11.symm
    by_cases u12 : u.val=12
    · exact u12.trans (sameF v (h.symm.trans (be u u12))).symm
    by_cases v12 : v.val=12
    · exact (sameF u (h.trans (be v v12))).trans v12.symm
    rw [after u (by omega),after v (by omega)] at h
    have q := congrArg Fin.val (e.injective (Subtype.ext h))
    change u.val-13=v.val-13 at q
    omega
  have cardV : Fintype.card V=16 := by
    have q := card_sdiff_add_card_eq_card (subset_univ p.support.toFinset)
    rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support,len,card_univ,off] at q
    exact q.symm
  have onto : Function.Surjective φ := by
    by_contra n
    have s := Fintype.card_lt_of_injective_not_surjective φ inj n
    rw [Fintype.card_fin,cardV] at s
    omega
  exact ⟨φ,inj,onto,ae 11 rfl,be 12 rfl,on,offP⟩
#print axioms order_sixteen_five_off_labeling
end Graffiti189LongestPath.TwoCut.SmallOrderFour
