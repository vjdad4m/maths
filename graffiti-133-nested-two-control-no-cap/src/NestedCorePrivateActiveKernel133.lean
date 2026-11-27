import NestedCorePrivateGenericKernel133
namespace Graffiti133NestedActive
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V} {n : Nat} {f : Fin n→V}
private theorem findKnown_sound (as : List (Bit n)) (h : BitsOK G f as) {a b : Fin n} {t : Bool}
    (r : findKnown a b as=some t) : G.Adj (f a) (f b) ↔ t=true := by
  induction as with
  | nil => contradiction
  | cons q qs ih =>
    obtain ⟨x,y,tt⟩ := q
    simp only [findKnown] at r
    by_cases yes : unordered a b x y
    · rw [if_pos yes,Option.some.injEq] at r
      subst t
      have u := h (x,y,tt) (by simp)
      rcases yes with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact u
      · rwa [G.adj_comm]
    · rw [if_neg yes] at r
      exact ih (fun q qm=>h q (List.mem_cons_of_mem _ qm)) r

private theorem known_sound {spec : Fin n→Fin n→Option Bool} (model : Fit G f spec)
    {as : List (Bit n)} (h : BitsOK G f as) {a b : Fin n} {t : Bool}
    (r : known spec a b as=some t) : G.Adj (f a) (f b) ↔ t=true := by
  unfold known at r
  cases e : spec a b with
  | none =>
    rw [e] at r
    exact findKnown_sound as h r
  | some k =>
    rw [e] at r
    have tk : k=t := Option.some.inj r
    subst t
    exact model _ _ _ e

def usesOnly (active : Fin n→Bool) : Tree n→Bool
  | .split _ _ a b => usesOnly active a && usesOnly active b
  | .four a b x y => active a && active b && active x && active y
  | .path p => decide (∀ i,active (p i)=true)

theorem checked_active_sound
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (active : Fin n→Bool) (inj : ∀ a b, active a=true → active b=true → f a=f b → a=b) (spec : Fin n→Fin n→Option Bool) (model : Fit G f spec)
    (t : Tree n) (as : List (Bit n)) (meta : BitsOK G f as) (cert : checked spec as t=true) (activeCert : usesOnly active t=true) : False := by
  induction t generalizing as with
  | split a b no yes indec idec =>
    have h : checked spec ((a,b,false)::as) no=true ∧ checked spec ((a,b,true)::as) yes=true := by
      simpa [checked] using cert
    have ac : usesOnly active no=true ∧ usesOnly active yes=true := by simpa [usesOnly] using activeCert
    by_cases ab : G.Adj (f a) (f b)
    · apply idec _ _ h.2 ac.2
      intro e em
      rcases List.mem_cons.mp em with rfl|e
      · exact iff_of_true ab rfl
      · exact meta _ e
    · apply indec _ _ h.1 ac.1
      intro e em
      rcases List.mem_cons.mp em with rfl|e
      · simpa using ab
      · exact meta _ e
  | four a b x y =>
    obtain ⟨ab,xy,ax,bx,ay,byy⟩ := of_decide_eq_true cert
    have hit (a b : Fin n) (ev : known spec a b as=some true) : G.Adj (f a) (f b) :=
      (known_sound model meta ev).mpr rfl
    have ac : ((active a=true ∧ active b=true) ∧ active x=true) ∧ active y=true := by
      simpa only [usesOnly,Bool.and_eq_true] using activeCert
    exact xy (inj x y ac.1.2 ac.2 (h4 _ _ _ _ (fun eq=>ab (inj a b ac.1.1.1 ac.1.1.2 eq))
      (hit _ _ ax) (hit _ _ bx) (hit _ _ ay) (hit _ _ byy)))
  | path p =>
    obtain ⟨pi,pe⟩ := of_decide_eq_true cert
    apply h9
    have ac : ∀ i,active (p i)=true := of_decide_eq_true activeCert
    refine ⟨f∘p,fun a b e=>pi _ _ (inj _ _ (ac a) (ac b) e),?_⟩
    intro a b lt
    exact (known_sound model meta (pe a b lt)).trans ⟨of_decide_eq_true,decide_eq_true⟩


#print axioms checked_active_sound
end Graffiti133NestedActive
