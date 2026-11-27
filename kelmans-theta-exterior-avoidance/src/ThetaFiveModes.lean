import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaFiveModes
open SquareCap (IsTile)

abbrev Lane := Bool × Bool
variable {V : Type*}

def mid : V⊕Fin 3 := .inr 1
def leaf (side : Bool) : V⊕Fin 3 := .inr (if side then 2 else 0)

/-- A three-vertex path cap with its midpoint-to-exterior wire deleted. -/
structure Layout (C : SimpleGraph (V⊕Fin 3)) (p : Lane↪V) : Prop where
  midAdj : ∀ x,C.Adj mid x ↔ x=leaf false ∨ x=leaf true
  leafAdj : ∀ s x,C.Adj (leaf s) x ↔
    x=mid ∨ x=.inl (p (s,false)) ∨ x=.inl (p (s,true))

private theorem distinct_leaf (b : Bool) : leaf (V:=V) b ≠ leaf (!b) := by
  cases b <;> simp [leaf]

private theorem mid_leaf (b : Bool) : mid (V:=V) ≠ leaf b := by
  cases b <;> simp [mid,leaf]

private theorem three_card {T : Type*} [DecidableEq T] {a b c : T}
    (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    ({a,b,c}:Finset T).card=3 := by
  simp [card_insert_of_not_mem,ab,ac,bc]

private theorem third {T : Type*} [DecidableEq T] {S : Finset T} {a b : T}
    (sz : S.card=3) (aS : a∈S) (bS : b∈S) (ab : a≠b) :
    ∃ w,w∈S ∧ w≠a ∧ w≠b ∧ S={a,b,w} := by
  have p : ({a,b}:Finset T).card=2 := by simp [card_insert_of_not_mem,ab]
  obtain ⟨w,hw,hide⟩ := exists_mem_not_mem_of_card_lt_card (by omega :
    ({a,b}:Finset T).card<S.card)
  have wa : w≠a := fun h=>hide (by simp [h])
  have wb : w≠b := fun h=>hide (by simp [h])
  refine ⟨w,hw,wa,wb,?_⟩
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  · rw [sz,three_card ab wa.symm wb.symm]

variable [DecidableEq V]

/-- The midpoint's tile either consumes both virtual leaves or
consumes one leaf and one contact of that leaf. -/
theorem mid_profile {C : SimpleGraph (V⊕Fin 3)} {p : Lane↪V}
    (g : Layout C p) {S : Finset (V⊕Fin 3)} (t : IsTile C S) (has : mid∈S) :
    S={mid,leaf false,leaf true} ∨
      ∃ s i : Bool,S={mid,leaf s,.inl (p (s,i))} := by
  obtain ⟨sz,c,hc,star⟩ := t
  by_cases cm : c=mid
  · subst c
    left
    apply eq_of_subset_of_card_le
    · intro y hy
      by_cases ym : y=mid
      · simp [ym]
      · have j := (g.midAdj y).mp (star y hy ym)
        simpa only [mem_insert,mem_singleton] using (Or.inr j : y=mid ∨ y=leaf false ∨ y=leaf true)
    · rw [sz,three_card (mid_leaf false) (mid_leaf true) (by simpa using distinct_leaf (V:=V) false)]
  have kind : c=leaf false ∨ c=leaf true :=
    (g.midAdj c).mp (star mid has (fun h=>cm h.symm)).symm
  have aux (s : Bool) (eq : c=leaf s) :
      ∃ i : Bool,S={mid,leaf s,.inl (p (s,i))} := by
    obtain ⟨w,hw,wm,wc,take⟩ := third sz has (eq ▸ hc) (mid_leaf s)
    have adj : C.Adj (leaf s) w := eq ▸ star w hw (fun h=>wc (h.trans eq))
    rcases (g.leafAdj s w).mp adj with om|a|b
    · exact (wm om).elim
    · exact ⟨false,a ▸ take⟩
    · exact ⟨true,b ▸ take⟩
  right
  exact kind.elim (fun h=>⟨false,aux false h⟩) (fun h=>⟨true,aux true h⟩)

/-- Once the other two virtual vertices are occupied, a surviving
leaf either centers its two contacts or uses one as center, with a
real exterior edge from it to the third vertex. -/
theorem leaf_profile {C : SimpleGraph (V⊕Fin 3)} {p : Lane↪V}
    (g : Layout C p) {S : Finset (V⊕Fin 3)} (t : IsTile C S)
    (s : Bool) (has : leaf s∈S) (noMid : mid∉S) (noOther : leaf (!s)∉S) :
    S={leaf s,.inl (p (s,false)),.inl (p (s,true))} ∨
      ∃ i : Bool,∃ w:V,
        C.Adj (.inl (p (s,i))) (.inl w) ∧ S={leaf s,.inl (p (s,i)),.inl w} := by
  obtain ⟨sz,c,hc,star⟩ := t
  by_cases cl : c=leaf s
  · subst c
    left
    apply eq_of_subset_of_card_le
    · intro y hy
      by_cases yl : y=leaf s
      · simp [yl]
      rcases (g.leafAdj s y).mp (star y hy yl) with om|a|b
      · exact (noMid (om ▸ hy)).elim
      · simp [a]
      · simp [b]
    · have pd : p (s,false)≠p (s,true) := fun eq=>by simpa using p.injective eq
      rw [sz,three_card (by simp [leaf]) (by simp [leaf]) (by simp [pd])]
  have casesC := (g.leafAdj s c).mp (star (leaf s) has (fun h=>cl h.symm)).symm
  have aux (i : Bool) (ce : c=.inl (p (s,i))) :
      ∃ w:V,C.Adj (.inl (p (s,i))) (.inl w) ∧ S={leaf s,.inl (p (s,i)),.inl w} := by
    obtain ⟨v,vg,vl,vc,shape⟩ := third sz has (ce ▸ hc) (by simp [leaf])
    cases v with
    | inl w =>
      have e : C.Adj (.inl (p (s,i))) (.inl w) :=
        ce ▸ star (.inl w) vg (fun hh=>vc (hh.trans ce))
      exact ⟨w,e,shape⟩
    | inr k =>
      have tags : ∀ (b : Bool) (j : Fin 3), (Sum.inr j : V⊕Fin 3)=mid ∨ Sum.inr j=leaf (V:=V) b ∨
          Sum.inr j=leaf (V:=V) (!b) := by
        intro b j
        have h : j=0 ∨ j=1 ∨ j=2 := by revert j; decide
        rcases h with rfl|rfl|rfl <;> cases b <;> simp [mid,leaf]
      rcases tags s k with em|el|er
      · exact (noMid (em ▸ vg)).elim
      · exact (vl el).elim
      · exact (noOther (er ▸ vg)).elim
  rcases casesC with hm|a|b
  · exact (noMid (hm ▸ hc)).elim
  · exact Or.inr ⟨false,aux false a⟩
  · exact Or.inr ⟨true,aux true b⟩

#print axioms mid_profile
#print axioms leaf_profile
end KelmansCactus.AtomicBridge.ThetaFiveModes
