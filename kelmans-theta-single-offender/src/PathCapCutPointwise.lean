import PentagonCap

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.PathCapCutPointwise
open SquareCap (boundary NontrivialSide)
open PentagonCap (pathCap path3 pathRoot attach_boundary)
open PentagonProfile
noncomputable section
variable {V : Type*} [Fintype V]

omit [Fintype V] in
private theorem mismatch_const {T : Type*} (p : Port ↪ V) (r : Port → T) (c : V → Bool) (b : Bool) :
    mismatch p c ((fun _ => !b) ∘ r) = portCount p c b := by
  unfold mismatch portCount
  congr 1
  ext i
  cases b <;> cases h : c (p i) <;> simp [h]

private def pc (s : Fin 3 → Bool) : ℕ :=
  ((univ : Finset (Fin 3 × Fin 3)).filter
    (fun z => s z.1=true ∧ s z.2=false ∧ path3.Adj z.1 z.2)).card

private theorem pc_eq (s : Fin 3 → Bool) : (boundary path3 s).card=pc s := by
  classical
  unfold boundary pc
  congr 1
  ext z
  simp

private theorem path_colour_table (s : Fin 3 → Bool) :
    (∃ b, (∀ i,s i = b) ∧ pc s = 0) ∨
    ∃ t b, (∀ i,s i=b ↔ i=t) ∧
      (t=1 ∧ pc s=2 ∧ portWeight (s ∘ pathRoot) b=1 ∨
       t≠1 ∧ pc s=1 ∧ (∀ z,2≤portWeight (s ∘ pathRoot) z)) := by
  revert s
  decide

private theorem nontriv_of_sum_elim {V T : Type*} (c : V→Bool) (s : T→Bool) (b : Bool)
    (big : NontrivialSide (Sum.elim c s) b) (none : ∀ t,s t ≠ b) :
    NontrivialSide c b := by
  obtain ⟨x,y,hx,hy,xy⟩ := big
  cases x with
  | inr x => exact (none x hx).elim
  | inl x => cases y with
    | inr y => exact (none y hy).elim
    | inl y => exact ⟨x,y,hx,hy,fun e=>xy (congrArg Sum.inl e)⟩

omit [Fintype V] in
private theorem same_exterior_mismatch (p : Port ↪ V) (c : V→Bool) (t : Port→Bool)
    (b : Bool) (all : ∀ x,c x ≠ b) :
    mismatch p c t = portWeight t b := by
  unfold portWeight mismatch
  congr 1
  ext i
  have nd := all (p i)
  cases h : c (p i) <;> cases t i <;> cases b <;> simp_all


/-- Classify the actual low cut, not just the existence of some
bad cut. It has one virtual leaf on one shore, has two exterior
crossings, and no mismatched seam edges. -/
theorem actual_path_cap_cut_profile {G : SimpleGraph V} {p : Port ↪ V}
    (L : OutsideLaw G p) (f : V⊕Fin 3→Bool)
    (budget : (boundary (pathCap G p) f).card≤3)
    (bign : ∀ b,NontrivialSide f b) :
    ∃ (t : Fin 3) (b : Bool), t≠1 ∧
      (boundary G (f ∘ Sum.inl)).card=2 ∧
      (boundary (pathCap G p) f).card=3 ∧
      (∀ j,f (Sum.inr j)=b ↔ j=t) ∧
      (∀ i,f (Sum.inl (p i))=b ↔ pathRoot i=t) := by
  let c : V→Bool := f ∘ Sum.inl
  let s : Fin 3→Bool := f ∘ Sum.inr
  have eb : f = Sum.elim c s := by funext x; cases x <;> rfl
  have big (b : Bool) : NontrivialSide (Sum.elim c s) b := by
    rw [←eb]
    exact bign b
  have capEq : (boundary (pathCap G p) f).card =
      (boundary G c).card + mismatch p c (s ∘ pathRoot) + pc s := by
    rw [eb,pathCap,attach_boundary,pc_eq]
    omega
  have capBudget : (boundary G c).card + mismatch p c (s ∘ pathRoot) + pc s ≤ 3 := by
    exact capEq.symm ▸ budget
  rcases path_colour_table s with ⟨b,all,cut⟩ | ⟨t,b,single,profile⟩
  · have sEq : s = fun _ => !(!b) := by funext x; simp [all]
    have d := L.strong c (!b) (nontriv_of_sum_elim c s (!b) (big (!b))
      (fun x => by simp [all]))
    have mis : mismatch p c (s ∘ pathRoot)=portCount p c (!b) := by
      rw [sEq]
      apply mismatch_const
    omega
  have outside_mixed (z : Bool) : ∃ x,c x=z := by
    by_contra! none
    have sv : z ≠ b := by
      rintro rfl
      obtain ⟨x,y,hx,hy,ne⟩ := big z
      cases x with
      | inl x => exact none x hx
      | inr x => cases y with
        | inl y => exact none y hy
        | inr y => exact ne (congrArg Sum.inr
            ((single x).mp hx |>.trans ((single y).mp hy).symm))
    have mis := same_exterior_mismatch p c (s ∘ pathRoot) z none
    rcases profile with ⟨_,ed,min⟩ | ⟨_,ed,slots⟩
    · have all := portCount_complement (Function.Embedding.refl Port) (s ∘ pathRoot)
      change portWeight (s ∘ pathRoot) true + portWeight (s ∘ pathRoot) false=5 at all
      cases z <;> cases b
      all_goals simp_all
      all_goals omega
    · have pm := slots z
      have pn := slots b
      have all := portCount_complement (Function.Embedding.refl Port) (s ∘ pathRoot)
      change portWeight (s ∘ pathRoot) true + portWeight (s ∘ pathRoot) false=5 at all
      -- The singleton gadget leaf has exactly two ports. Its opposite
      -- color has three, so if z is absent outside the cap budget fails.
      have two : portWeight (s ∘ pathRoot) b=2 := by
        have test : ∀ (s : Fin 3→Bool) (t : Fin 3) (b : Bool),
            t≠1 → (∀ i,s i=b ↔ i=t) → portWeight (s ∘ pathRoot) b=2 := by decide
        exact test _ _ _ (by assumption) single
      cases z <;> cases b
      all_goals simp_all
      all_goals omega
  rcases profile with ⟨_,ct,slots⟩ | ⟨leaf,ct,slots⟩
  · exact (middle_split_impossible L c _ b slots outside_mixed (by omega)).elim
  · obtain ⟨two,agree,big⟩ :=
      leaf_split_is_exact_two L c (s ∘ pathRoot) slots outside_mixed (by omega)
    have mis : mismatch p c (s ∘ pathRoot)=0 := by
      classical
      simp [mismatch,agree]
    refine ⟨t,b,leaf,two,?_ ,?_ ,?_⟩
    · rw [capEq,two,mis,ct]
    · exact single
    · intro i
      change c (p i)=b ↔ pathRoot i=t
      rw [agree i]
      exact single (pathRoot i)


#print axioms actual_path_cap_cut_profile
end
end KelmansCactus.AtomicBridge.PathCapCutPointwise
