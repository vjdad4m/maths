import Row188
import TwinFort

namespace CographForcing188.Sharp
open SimpleGraph Finset AutoGraphPowerBurning ForcingDrop711
abbrev V := Bool × Fin 3

/-- The balanced-biclique representation from row 1883. -/
def K : SimpleGraph V where
  Adj u v := u.1 ≠ v.1
  symm := fun _ _ h => Ne.symm h
  loopless := fun _ => not_ne_iff.mpr rfl

instance : DecidableRel K.Adj := fun u v => inferInstanceAs (Decidable (u.1 ≠ v.1))

theorem cograph : CographRadius.Cograph K := by
  rintro ⟨f,edges⟩
  have chain : ∀ a b c d : Bool, a ≠ b → b ≠ c → c ≠ d → a ≠ d := by decide
  have edge (i j : Fin 4) (h : Graffiti137.Consecutive i j) : (f i).1 ≠ (f j).1 := (edges i j).mpr h
  have endEdge : K.Adj (f 0) (f 3) := chain _ _ _ _
    (edge 0 1 (by decide)) (edge 1 2 (by decide)) (edge 2 3 (by decide))
  exact (by decide : ¬ Graffiti137.Consecutive (0 : Fin 4) 3) ((edges 0 3).mp endEdge)

theorem power_lower : 2 ≤ power K := by
  classical
  let sizes := {r : ℕ | ∃ S : Finset V, r = S.card ∧ ∀ v, Observed K S v}
  have existsSet : sizes.Nonempty := ⟨_,univ,rfl,fun _ => .root (mem_univ _)⟩
  obtain ⟨S,cost,see⟩ := Nat.sInf_mem existsSet
  change power K = S.card at cost
  by_contra! small
  obtain ⟨a,ha⟩ := card_le_one_iff_subset_singleton.mp (show S.card ≤ 1 by omega)
  have unused : ∀ i : Fin 3, ∃ j l : Fin 3, j ≠ i ∧ l ≠ i ∧ j ≠ l := by decide
  obtain ⟨j,l,ja,la,jl⟩ := unused a.2
  let b : V := (a.1,j)
  let c : V := (a.1,l)
  have distinct : b ≠ c := fun e => jl (congrArg Prod.snd e)
  obtain ⟨w,hw,hit⟩ := Book567.hit_twins K distinct (fun _ => Iff.rfl) S (see b)
  have wa := mem_singleton.mp (ha hw)
  rcases hit with hb|hc|edge
  · exact ja (congrArg Prod.snd (hb.symm.trans wa))
  · exact la (congrArg Prod.snd (hc.symm.trans wa))
  · exact edge (show a.1 = w.1 from congrArg Prod.fst wa.symm)

private theorem fullAfterTwo (k : ℕ) (S : Finset V) (h : step K k (step K k S) = univ) :
    full K k S := by
  change (step K k)^[Fintype.card V] S = univ
  have size : Fintype.card V = 4+2 := by decide
  rw [size,Function.iterate_add_apply]
  change (step K k)^[4] (step K k (step K k S)) = univ
  rw [h]
  apply Function.iterate_fixed
  exact eq_univ_of_forall (fun _ => Finset.subset_union_left (mem_univ _))

/-- Equality at threshold two, and failure at threshold three, on the same connected cograph. -/
theorem sharp : K.Connected ∧ CographRadius.Cograph K ∧ power K = 2 ∧
    forcing K 2 = 2 ∧ forcing K 3 = 1 := by
  have connected : K.Connected := by
    constructor
    intro a b
    by_cases adj : a.1 ≠ b.1
    · exact (show K.Adj a b from adj).reachable
    · let c : V := (!a.1,0)
      have ac : K.Adj a c := by cases h : a.1 <;> simp [K,c,h]
      have cb : K.Adj c b := by cases h : a.1 <;> simp_all [K,c]
      exact ac.reachable.trans cb.reachable
  let pair : Finset V := {(false,0),(true,0)}
  let single : Finset V := {(false,0)}
  have two : forcing K 2 ≤ 2 :=
    (forcing_le K (fullAfterTwo 2 pair (by decide))).trans (by decide)
  have three : forcing K 3 ≤ 1 :=
    (forcing_le K (fullAfterTwo 3 single (by decide))).trans (by decide)
  obtain ⟨S,sz,success⟩ := attained K 3
  obtain ⟨v,hv,_,_⟩ := active_in_component K success (K.connectedComponentMk (false,0))
  have positive : 0 < S.card := card_pos.mpr ⟨v,hv⟩
  have cmp := row188 K (by decide) cograph
  have lo := power_lower
  exact ⟨connected,cograph,by omega,by omega,by omega⟩

#print axioms sharp
end CographForcing188.Sharp
