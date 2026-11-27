import BicycleCheck133

namespace Graffiti133Bicycle
open SimpleGraph Graffiti133
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V}

private theorem rotate_inj :
    ∀ a b c : Fin 7, a+c=b+c → a=b := by decide

private theorem rotate_iff :
    ∀ a b c : Fin 7, a-c=b ↔ a=b+c := by decide

private theorem rotate_cycle :
    ∀ a b c : Fin 7, cycle (a+c).val (b+c).val = cycle a.val b.val := by decide

private theorem sub_self_seven : ∀ a : Fin 7, a-a=0 := by decide

theorem Numbered.force_of_certificate {rows d2 : List Nat} {n : Nat}
    {s : Nat → Nat} (M : Numbered G rows d2 n s) (h4 : FourCycleFree G) (hn : 1≤n)
    {data : List (List Nat)} (ok : verify rows d2 data (n-1) 0 [0]=true) :
    ∃ p : Fin 9 → V, InducedPath G p := by
  let a : Fin 7 := ⟨s 0,M.siteRange 0 (by omega)⟩
  let ss (i : Nat) : Nat := ((⟨s i % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7)-a).val
  let rotate (i : Nat) : Nat := if hi : i < 7 then ((⟨i,hi⟩ : Fin 7)+a).val else i
  have shift (i : Nat) (hi : i < 7) : rotate i=((⟨i,hi⟩ : Fin 7)+a).val := dif_pos hi
  have fix (i : Nat) (hi : 7 ≤ i) : rotate i=i := dif_neg (Nat.not_lt.mpr hi)
  have small (i : Nat) (hi : i < 7) : rotate i < 7 := by rw [shift i hi]; exact Fin.isLt _
  have ub (i : Nat) (hi : i < 7+n) : rotate i < 7+n := by
    by_cases lt : i < 7
    · have t := small i lt
      omega
    · rwa [fix i (by omega)]
  have Rinj {i j : Nat} (eq : rotate i=rotate j) : i=j := by
    by_cases hi : i < 7
    · by_cases hj : j < 7
      · rw [shift i hi,shift j hj] at eq
        exact congrArg Fin.val (rotate_inj ⟨i,hi⟩ ⟨j,hj⟩ a (Fin.ext eq))
      · have t := small i hi
        rw [fix j (by omega)] at eq
        omega
    · by_cases hj : j < 7
      · have t := small j hj
        rw [fix i (by omega)] at eq
        omega
      · rwa [fix i (by omega),fix j (by omega)] at eq
  let P : Numbered G rows d2 n ss :=
    { f := M.f ∘ rotate
      inj := fun i hi j hj e => Rinj (M.inj _ (ub i hi) _ (ub j hj) e)
      siteRange := fun _ _ => Fin.isLt _
      cycleAdj := by
        intro i hi j hj
        change G.Adj (M.f (rotate i)) (M.f (rotate j)) ↔ _
        rw [M.cycleAdj _ (small i hi) _ (small j hj),shift i hi,shift j hj]
        rw [rotate_cycle]
      exteriorAdj := by
        intro i hi j hj
        change G.Adj (M.f (rotate (7+i))) (M.f (rotate (7+j))) ↔ _
        rw [fix _ (by omega),fix _ (by omega)]
        exact M.exteriorAdj i hi j hj
      joinAdj := by
        intro i hi j hj
        change G.Adj (M.f (rotate (7+i))) (M.f (rotate j)) ↔ _
        have si := M.siteRange i hi
        have p := M.joinAdj i hi (rotate j) (small j hj)
        rw [shift j hj] at p
        rw [fix _ (by omega),shift j hj,p]
        let u : Fin 7 := ⟨s i,si⟩
        have qs : ss i=(u-a).val := by simp [ss,Nat.mod_eq_of_lt si,u]
        rw [qs]
        change u.val=(⟨j,hj⟩+a).val ↔ (u-a).val=j
        exact ⟨fun e => congrArg Fin.val ((rotate_iff u ⟨j,hj⟩ a).mpr (Fin.ext e)),
          fun e => congrArg Fin.val ((rotate_iff u ⟨j,hj⟩ a).mp (Fin.ext e))⟩
      distanceTwo := M.distanceTwo }
  have zero : ss 0=0 := by
    unfold ss
    have eq : (⟨s 0 % 7,Nat.mod_lt _ (by decide)⟩ : Fin 7)=a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
    rw [eq]
    exact congrArg Fin.val (sub_self_seven a)
  exact P.lift (numbered_site_zero_has_path hn (P.legal h4) zero ok)

#print axioms Numbered.force_of_certificate
end Graffiti133Bicycle
