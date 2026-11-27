import ThetaFiveModes

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAdjacentEarLeafModes
open SquareCap (IsTile)
open ThetaFiveModes (mid leaf Lane)
noncomputable section

variable {V : Type*}

/-- Mandatory cap edge classification, also valid when one of the
leaf wires was intentionally omitted in the cap. -/
structure WeakLayout (C : SimpleGraph (V⊕Fin 3)) (p : Lane↪V) : Prop where
  leafAdj : ∀ s x,C.Adj (leaf s) x →
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

/-- Once the other two virtual vertices are occupied, a surviving
leaf either centers its two contacts or uses one as center, with a
real exterior edge from it to the third vertex. -/
theorem actual_leaf_profile {C : SimpleGraph (V⊕Fin 3)} {p : Lane↪V}
    (g : WeakLayout C p) {S : Finset (V⊕Fin 3)} (t : IsTile C S)
    (s : Bool) (has : leaf s∈S) (noMid : mid∉S) (noOther : leaf (!s)∉S) :
    (S={leaf s,.inl (p (s,false)),.inl (p (s,true))} ∧
      C.Adj (leaf s) (.inl (p (s,false))) ∧ C.Adj (leaf s) (.inl (p (s,true)))) ∨
      ∃ i : Bool,∃ w:V,
        C.Adj (leaf s) (.inl (p (s,i))) ∧
        C.Adj (.inl (p (s,i))) (.inl w) ∧ S={leaf s,.inl (p (s,i)),.inl w} := by
  obtain ⟨sz,c,hc,star⟩ := t
  by_cases cl : c=leaf s
  · subst c
    left
    have eq : S={leaf s,.inl (p (s,false)),.inl (p (s,true))} := by
      apply eq_of_subset_of_card_le
      · intro y hy
        by_cases yl : y=leaf s
        · simp [yl]
        rcases g.leafAdj s y (star y hy yl) with om|a|b
        · exact (noMid (om ▸ hy)).elim
        · simp [a]
        · simp [b]
      · have pd : p (s,false)≠p (s,true) := fun eq=>by simpa using p.injective eq
        rw [sz,three_card (by simp [leaf]) (by simp [leaf]) (by simp [pd])]
    exact ⟨eq,star _ (eq.symm ▸ by simp) (by simp [leaf]),
      star _ (eq.symm ▸ by simp) (by simp [leaf])⟩
  have wire := (star (leaf s) has (fun h=>cl h.symm)).symm
  have casesC := g.leafAdj s c wire
  have aux (i : Bool) (ce : c=.inl (p (s,i))) :
      ∃ w:V,C.Adj (leaf s) (.inl (p (s,i))) ∧
        C.Adj (.inl (p (s,i))) (.inl w) ∧ S={leaf s,.inl (p (s,i)),.inl w} := by
    obtain ⟨v,vg,vl,vc,shape⟩ := third sz has (ce ▸ hc) (by simp [leaf])
    cases v with
    | inl w =>
      have e : C.Adj (.inl (p (s,i))) (.inl w) :=
        ce ▸ star (.inl w) vg (fun hh=>vc (hh.trans ce))
      exact ⟨w,ce ▸ wire,e,shape⟩
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



/-- The two virtual leaves cannot share a tile after the midpoint
has been deleted: their remaining possible contacts are disjoint. -/
theorem leaves_separate {C : SimpleGraph (V⊕Fin 3)} {p : Lane↪V}
    (g : WeakLayout C p) {S : Finset (V⊕Fin 3)} (t : IsTile C S)
    (noMid : mid∉S) (one : leaf false∈S) (two : leaf true∈S) : False := by
  obtain ⟨_,a,ha,star⟩ := t
  have n0 (x : V⊕Fin 3) (h : x=leaf false) :
      ¬C.Adj (leaf true) x := by
    subst x
    intro e
    rcases g.leafAdj true _ e with ee|ee|ee
    · simp [leaf,mid] at ee
    · simp [leaf] at ee
    · simp [leaf] at ee
  by_cases fa : a=leaf false
  · subst a
    exact n0 _ rfl (star _ two (distinct_leaf true)).symm
  by_cases ta : a=leaf true
  · subst a
    exact n0 _ rfl (star _ one (distinct_leaf false))
  have x := g.leafAdj false a (star _ one (fun h=>fa h.symm)).symm
  have y := g.leafAdj true a (star _ two (fun h=>ta h.symm)).symm
  have notmid : a≠mid := fun e=>noMid (e ▸ ha)
  have pneq (i j : Bool) : p (false,i)≠p (true,j) := fun h=>
    Bool.false_ne_true (congrArg Prod.fst (p.injective h))
  rcases x with h|h|h <;> rcases y with e|e|e
  all_goals first
    | exact notmid h
    | exact notmid e
    | exact (pneq _ _) (Sum.inl_injective (h.symm.trans e))

#print axioms actual_leaf_profile
#print axioms leaves_separate
end
end KelmansCactus.AtomicBridge.ThetaAdjacentEarLeafModes
