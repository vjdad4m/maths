import NestedCoreLongGateAtlas133

namespace Graffiti133PrivateCross
open SimpleGraph Graffiti133
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

abbrev Bit := Fin 18×Fin 18×Bool

inductive Tree where
  | split (a b : Fin 18) (no yes : Tree)
  | four (a b x y : Fin 18)
  | path (f : Fin 9→Fin 18)

def base (triple : Bool) (a b : Fin 18) : Bool :=
  let x := min a.val b.val
  let y := max a.val b.val
  if y<7 then decide (y=x+1 ∨ (x=0 ∧ y=6))
  else if y<9 then
    if x<7 then (if y=7 then 9 else if triple then 38 else 18 : Nat).testBit x else false
  else decide (x<9 ∧ y=x+9)

def forcedSite (i : Fin 7) : Fin 18 := ⟨i.val+9,by have := i.isLt; omega⟩
def forcedControl (c : Fin 2) : Fin 18 := ⟨c.val+16,by have := c.isLt; omega⟩

def unordered (a b x y : Fin 18) : Prop := (a=x ∧ b=y) ∨ (a=y ∧ b=x)
instance (a b x y : Fin 18) : Decidable (unordered a b x y) := by unfold unordered; infer_instance

def findKnown (a b : Fin 18) : List Bit→Option Bool
  | [] => none
  | (x,y,t)::as => if unordered a b x y then some t else findKnown a b as

def known (m : Bool) (c : Fin 2) (i : Fin 7) (a b : Fin 18) (as : List Bit) : Option Bool :=
  if a.val < 9 ∨ b.val < 9 then some (base m a b)
  else if unordered a b (forcedSite i) (forcedControl c) then some true
  else findKnown a b as

def checked (m : Bool) (c : Fin 2) (j : Fin 7) (as : List Bit) : Tree→Bool
  | .split a b no yes =>
    checked m c j ((a,b,false)::as) no && checked m c j ((a,b,true)::as) yes
  | .four a b x y =>
    decide (a≠b ∧ x≠y ∧ known m c j a x as=some true ∧ known m c j b x as=some true ∧
      known m c j a y as=some true ∧ known m c j b y as=some true)
  | .path f =>
    decide ((∀ a b : Fin 9,f a=f b→a=b) ∧
      (∀ a b : Fin 9,a<b→known m c j (f a) (f b) as=some (decide (a.val+1=b.val))))

variable {V : Type*} {G : SimpleGraph V} {f : Fin 18→V}

def BitsOK (G : SimpleGraph V) (f : Fin 18→V) (as : List Bit) : Prop :=
  ∀ q∈as, G.Adj (f q.1) (f q.2.1) ↔ q.2.2=true

private theorem findKnown_sound (as : List Bit) (h : BitsOK G f as) {a b : Fin 18} {t : Bool}
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

private theorem known_sound
    {m : Bool} {c : Fin 2} {i : Fin 7}
    (model : ∀ a b : Fin 18,a.val < 9 ∨ b.val < 9 → (G.Adj (f a) (f b)↔base m a b=true))
    (forced : G.Adj (f (forcedSite i)) (f (forcedControl c)))
    {as : List Bit} (h : BitsOK G f as) {a b : Fin 18} {t : Bool}
    (r : known m c i a b as=some t) :
    G.Adj (f a) (f b) ↔ t=true := by
  unfold known at r
  by_cases close : a.val < 9 ∨ b.val < 9
  · rw [if_pos close,Option.some.injEq] at r
    rw [←r]
    exact model _ _ close
  · rw [if_neg close] at r
    by_cases hit : unordered a b (forcedSite i) (forcedControl c)
    · rw [if_pos hit,Option.some.injEq] at r
      subst t
      rcases hit with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact iff_of_true forced rfl
      · exact iff_of_true forced.symm rfl
    · rw [if_neg hit] at r
      exact findKnown_sound as h r

theorem checked_sound
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (inj : Function.Injective f)
    (m : Bool) (c : Fin 2) (i : Fin 7)
    (model : ∀ a b : Fin 18,a.val < 9 ∨ b.val < 9 → (G.Adj (f a) (f b)↔base m a b=true))
    (forced : G.Adj (f (forcedSite i)) (f (forcedControl c)))
    (t : Tree) (as : List Bit) (meta : BitsOK G f as)
    (cert : checked m c i as t=true) : False := by
  induction t generalizing as with
  | split a b no yes indec idec =>
    have h : checked m c i ((a,b,false)::as) no=true ∧ checked m c i ((a,b,true)::as) yes=true := by
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
    have hit (a b : Fin 18) (ev : known m c i a b as=some true) : G.Adj (f a) (f b) :=
      (known_sound model forced meta ev).mpr rfl
    exact xy (inj (h4 _ _ _ _ (fun eq=>ab (inj eq)) (hit _ _ ax) (hit _ _ bx) (hit _ _ ay) (hit _ _ byy)))
  | path p =>
    obtain ⟨pi,pe⟩ := of_decide_eq_true cert
    apply h9
    refine ⟨f∘p,inj.comp (fun _ _ e=>pi _ _ e),?_⟩
    intro a b lt
    exact (known_sound model forced meta (pe a b lt)).trans ⟨of_decide_eq_true,decide_eq_true⟩

#print axioms checked_sound
end Graffiti133PrivateCross
