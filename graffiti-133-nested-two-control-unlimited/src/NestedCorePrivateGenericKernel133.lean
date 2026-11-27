import NestedCorePrivateCrossRows133

namespace Graffiti133PrivateGeneric
open SimpleGraph Graffiti133
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

abbrev Bit (n : Nat) := Fin n×Fin n×Bool

inductive Tree (n : Nat) where
  | split (a b : Fin n) (no yes : Tree n)
  | four (a b x y : Fin n)
  | path (f : Fin 9→Fin n)

def unordered {n : Nat} (a b x y : Fin n) : Prop := (a=x ∧ b=y) ∨ (a=y ∧ b=x)
instance {n : Nat} (a b x y : Fin n) : Decidable (unordered a b x y) := by unfold unordered; infer_instance

def findKnown {n : Nat} (a b : Fin n) : List (Bit n)→Option Bool
  | [] => none
  | (x,y,t)::as => if unordered a b x y then some t else findKnown a b as

def known {n : Nat} (spec : Fin n→Fin n→Option Bool) (a b : Fin n) (as : List (Bit n)) : Option Bool :=
  (spec a b).orElse (fun _=>findKnown a b as)

def checked {n : Nat} (spec : Fin n→Fin n→Option Bool) (as : List (Bit n)) : Tree n→Bool
  | .split a b no yes => checked spec ((a,b,false)::as) no && checked spec ((a,b,true)::as) yes
  | .four a b x y => decide (a≠b ∧ x≠y ∧ known spec a x as=some true ∧
      known spec b x as=some true ∧ known spec a y as=some true ∧ known spec b y as=some true)
  | .path f => decide ((∀ a b : Fin 9,f a=f b→a=b) ∧
      (∀ a b : Fin 9,a<b→known spec (f a) (f b) as=some (decide (a.val+1=b.val))))

variable {V : Type*} {G : SimpleGraph V} {n : Nat} {f : Fin n→V}

def BitsOK (G : SimpleGraph V) (f : Fin n→V) (as : List (Bit n)) : Prop :=
  ∀ q∈as, G.Adj (f q.1) (f q.2.1) ↔ q.2.2=true

def Fit (G : SimpleGraph V) (f : Fin n→V) (spec : Fin n→Fin n→Option Bool) : Prop :=
  ∀ a b t, spec a b=some t → (G.Adj (f a) (f b)↔t=true)

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

theorem checked_sound
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (inj : Function.Injective f) (spec : Fin n→Fin n→Option Bool) (model : Fit G f spec)
    (t : Tree n) (as : List (Bit n)) (meta : BitsOK G f as) (cert : checked spec as t=true) : False := by
  induction t generalizing as with
  | split a b no yes indec idec =>
    have h : checked spec ((a,b,false)::as) no=true ∧ checked spec ((a,b,true)::as) yes=true := by
      simpa [checked] using cert
    by_cases ab : G.Adj (f a) (f b)
    · apply idec _ _ h.2
      intro e em
      rcases List.mem_cons.mp em with rfl|e
      · exact iff_of_true ab rfl
      · exact meta _ e
    · apply indec _ _ h.1
      intro e em
      rcases List.mem_cons.mp em with rfl|e
      · simpa using ab
      · exact meta _ e
  | four a b x y =>
    obtain ⟨ab,xy,ax,bx,ay,byy⟩ := of_decide_eq_true cert
    have hit (a b : Fin n) (ev : known spec a b as=some true) : G.Adj (f a) (f b) :=
      (known_sound model meta ev).mpr rfl
    exact xy (inj (h4 _ _ _ _ (fun eq=>ab (inj eq)) (hit _ _ ax) (hit _ _ bx) (hit _ _ ay) (hit _ _ byy)))
  | path p =>
    obtain ⟨pi,pe⟩ := of_decide_eq_true cert
    apply h9
    refine ⟨f∘p,inj.comp (fun _ _ e=>pi _ _ e),?_⟩
    intro a b lt
    exact (known_sound model meta (pe a b lt)).trans ⟨of_decide_eq_true,decide_eq_true⟩

#print axioms checked_sound
end Graffiti133PrivateGeneric
