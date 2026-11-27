import HandleFactor

namespace KelmansCactus.AtomicBridge.HandleExtension.Edges.AtomicHitting
open SimpleGraph Finset FourRingCutAux
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
universe u
variable {V : Type u} {G : SimpleGraph V} (E : Edges G)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private def lift (c : V ⊕ Bool → Bool) (e : V × V) : (V ⊕ Bool) × (V ⊕ Bool) := by
  classical
  exact if h : E.Removed e.1 e.2 then
    let s := Classical.choose h
    if c (Sum.inr s) then (Sum.inr s,Sum.inl e.2)
    else (Sum.inl e.1,Sum.inr s)
  else (Sum.inl e.1,Sum.inl e.2)

private theorem lift_mem (c : V ⊕ Bool → Bool) {e : V × V}
    (he : e ∈ boundary G (oldColor c)) : lift E c e ∈ boundary E.host c := by
  classical
  obtain ⟨c₁,c₂,ed⟩ := mem_boundary.mp he
  unfold oldColor at c₁ c₂
  by_cases h : E.Removed e.1 e.2
  · rw [lift,dif_pos h]
    have hend := E.pair_ends (Classical.choose_spec h)
    by_cases hs : c (Sum.inr (Classical.choose h)) = true
    · exact mem_boundary.mpr (by simpa [hs] using
        (show c (Sum.inr (Classical.choose h)) = true ∧
          c (Sum.inl e.2) = false ∧
          E.host.Adj (Sum.inr (Classical.choose h)) (Sum.inl e.2) from ⟨hs,c₂,hend.2⟩))
    · have hs' : c (Sum.inr (Classical.choose h)) = false := Bool.eq_false_iff.mpr hs
      apply mem_boundary.mpr
      simp only [hs,if_false]
      exact ⟨c₁,hs',hend.1⟩
  · rw [lift,dif_neg h]
    exact mem_boundary.mpr ⟨c₁,c₂,⟨ed,h⟩⟩

private theorem lift_injective (c : V ⊕ Bool → Bool) : Function.Injective (lift E c) := by
  classical
  rintro ⟨a,b⟩ ⟨d,e⟩ he
  unfold lift at he
  change (if h : E.Removed a b then _ else _) =
    (if h : E.Removed d e then _ else _) at he
  by_cases h₁ : E.Removed a b <;> by_cases h₂ : E.Removed d e
  · rw [dif_pos h₁,dif_pos h₂] at he
    have hp := Classical.choose_spec h₁
    have hq := Classical.choose_spec h₂
    dsimp only at he hp hq
    by_cases h₃ : c (Sum.inr (Classical.choose h₁)) = true <;>
      by_cases h₄ : c (Sum.inr (Classical.choose h₂)) = true
    · rw [if_pos h₃,if_pos h₄] at he
      have hs := Sum.inr.inj (congrArg Prod.fst he)
      have heq := Sum.inl.inj (congrArg Prod.snd he)
      subst e
      rw [← hs] at hq
      exact Prod.ext (E.pair_neighbor_unique (E.pair_symm hp) (E.pair_symm hq)) rfl
    · rw [if_pos h₃,if_neg h₄] at he
      cases he
    · rw [if_neg h₃,if_pos h₄] at he
      cases he
    · rw [if_neg h₃,if_neg h₄] at he
      have hs := Sum.inr.inj (congrArg Prod.snd he)
      have heq := Sum.inl.inj (congrArg Prod.fst he)
      subst d
      rw [← hs] at hq
      exact Prod.ext rfl (E.pair_neighbor_unique hp hq)
  · rw [dif_pos h₁,dif_neg h₂] at he
    dsimp only at he
    split at he <;> cases he
  · rw [dif_neg h₁,dif_pos h₂] at he
    dsimp only at he
    split at he <;> cases he
  · rw [dif_neg h₁,dif_neg h₂] at he
    exact Prod.ext (Sum.inl.inj (congrArg Prod.fst he)) (Sum.inl.inj (congrArg Prod.snd he))

private theorem lifted_subset (c : V ⊕ Bool → Bool) :
    (boundary G (oldColor c)).image (lift E c) ⊆ boundary E.host c := by
  intro e he
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
  exact lift_mem E c ha

private theorem lift_no_new_new (c : V ⊕ Bool → Bool) (e : V × V) (s t : Bool) :
    lift E c e ≠ (Sum.inr s,Sum.inr t) := by
  classical
  unfold lift
  split
  · dsimp only
    split <;> intro h <;> cases h
  · intro h; cases h

private theorem lift_no_inactive_slot (c : V ⊕ Bool → Bool) (s : Bool)
    (off : ∀ x, E.Ends s x → c (Sum.inl x) = false)
    {e : V × V} (he : e ∈ boundary G (oldColor c)) (y : V) :
    lift E c e ≠ (Sum.inr s,Sum.inl y) := by
  classical
  intro h
  unfold lift at h
  split at h
  · rename_i h'
    have hend := (E.pair_ends (Classical.choose_spec h')).1
    dsimp only at h
    split at h
    · have hs := Sum.inr.inj (congrArg Prod.fst h)
      rw [hs] at hend
      have hh := (mem_boundary.mp he).1
      change c (Sum.inl e.1) = true at hh
      rw [off _ hend] at hh
      cases hh
    · cases h
  · cases h

private theorem one_extra (c : V ⊕ Bool → Bool) {p : (V ⊕ Bool) × (V ⊕ Bool)}
    (hp : p ∈ boundary E.host c)
    (hn : ∀ e ∈ boundary G (oldColor c), lift E c e ≠ p) :
    (boundary G (oldColor c)).card + 1 ≤ (boundary E.host c).card := by
  let S := (boundary G (oldColor c)).image (lift E c)
  have hmem : p ∉ S := by
    intro h
    obtain ⟨e,he,hh⟩ := Finset.mem_image.mp h
    exact hn e he hh
  have hh := Finset.card_le_card (Finset.insert_subset hp (lifted_subset E c))
  rw [Finset.card_insert_of_not_mem hmem,Finset.card_image_of_injective _ (lift_injective E c)] at hh
  exact hh

private theorem extra_of_new_different (c : V ⊕ Bool → Bool)
    (h : c (Sum.inr false) ≠ c (Sum.inr true)) :
    (boundary G (oldColor c)).card+1 ≤ (boundary E.host c).card := by
  have ha : E.host.Adj (Sum.inr false) (Sum.inr true)  := by change false ≠ true; decide
  apply one_extra E c (active_edge h ha)
  intro e he
  rcases orientation_cases (c:=c) (x:=Sum.inr false) (y:=Sum.inr true) with h|h
  · rw [h]; exact lift_no_new_new E c e false true
  · rw [h]; exact lift_no_new_new E c e true false

private theorem extra_of_same_true_slot (c : V ⊕ Bool → Bool)
    (s : Bool) (hs : c (Sum.inr s)=true)
    (off : ∀ x, E.Ends s x → c (Sum.inl x) = false) :
    (boundary G (oldColor c)).card+1 ≤ (boundary E.host c).card := by
  have ha : E.Ends s (E.a s) := Or.inl rfl
  apply one_extra E c (p:=(Sum.inr s,Sum.inl (E.a s))) (mem_boundary.mpr ⟨hs,off _ ha,ha⟩)
  intro e he
  exact lift_no_inactive_slot E c s off he _

private theorem two_true_no_old (c : V ⊕ Bool → Bool)
    (oldOff : ∀ x : V, c (Sum.inl x) = false)
    (h₀ : c (Sum.inr false)=true) (h₁ : c (Sum.inr true)=true) :
    4 ≤ (boundary E.host c).card := by
  classical
  let F := (Sum.inr false : V ⊕ Bool)
  let T := (Sum.inr true : V ⊕ Bool)
  let S : Finset ((V ⊕ Bool) × (V ⊕ Bool)) :=
    {(F,Sum.inl (E.a false)),(F,Sum.inl (E.b false)),
      (T,Sum.inl (E.a true)),(T,Sum.inl (E.b true))}
  have hs : S.card = 4 := by
    have hA := (E.edge false).ne
    have hB := (E.edge true).ne
    simp [S,F,T,hA,hB]
  have mem (s : Bool) (h : c (Sum.inr s)=true) (x : V) (hx : E.Ends s x) :
      (Sum.inr s,Sum.inl x) ∈ boundary E.host c :=
    mem_boundary.mpr ⟨h,oldOff x,hx⟩
  have hs' : S ⊆ boundary E.host c := by
    intro p hp
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl|rfl|rfl
    · exact mem false h₀ _ (Or.inl rfl)
    · exact mem false h₀ _ (Or.inr rfl)
    · exact mem true h₁ _ (Or.inl rfl)
    · exact mem true h₁ _ (Or.inr rfl)
  exact hs ▸ Finset.card_le_card hs'

private theorem true_side_subsingleton (cub : ∀ x,G.degree x=3)
    (c : V ⊕ Bool → Bool) (cap : (boundary E.host c).card≤3)
    (small : ∀ x y : V, oldColor c x=true → oldColor c y=true → x=y) :
    ∀ x y : V ⊕ Bool, c x=true → c y=true → x=y := by
  classical
  by_cases ex : ∃ x : V, oldColor c x=true
  · obtain ⟨x,hx⟩ := ex
    have hc := singleton_boundary G (oldColor c) x hx (fun y hy => small y x hy hx)
    rw [cub] at hc
    have same : c (Sum.inr false) = c (Sum.inr true) := by
      by_contra h
      have hh := extra_of_new_different E c h
      omega
    have none : ∀ s : Bool, c (Sum.inr s) = false := by
      have h₀ : c (Sum.inr false)=false := by
        by_cases ht : c (Sum.inr false)=true
        · have ht' := same.symm.trans ht
          have hs : ∃ s : Bool, ¬ E.Ends s x := by
            by_cases hf : E.Ends false x
            · exact ⟨true,fun h => Bool.false_ne_true (E.separated hf h)⟩
            · exact ⟨false,hf⟩
          obtain ⟨s,hs⟩ := hs
          have off (y : V) (hy : E.Ends s y) : c (Sum.inl y)=false := by
            apply Bool.eq_false_iff.mpr
            intro ht
            have h : y=x := small _ _ ht hx
            exact hs (h ▸ hy)
          have tt : c (Sum.inr s)=true := by cases s <;> assumption
          have hh := extra_of_same_true_slot E c s tt off
          omega
        · exact Bool.eq_false_iff.mpr ht
      intro s
      cases s
      · exact h₀
      · exact same.symm.trans h₀
    rintro (a|s) (b|t) ha hb
    · exact congrArg Sum.inl (small a b ha hb)
    · exact (Bool.false_ne_true ((none t).symm.trans hb)).elim
    · exact (Bool.false_ne_true ((none s).symm.trans ha)).elim
    · exact (Bool.false_ne_true ((none s).symm.trans ha)).elim
  · have off (x : V) : c (Sum.inl x)=false :=
      Bool.eq_false_iff.mpr (fun h => ex ⟨x,h⟩)
    have notBoth (h₀ : c (Sum.inr false)=true) (h₁ : c (Sum.inr true)=true) : False := by
      have h := two_true_no_old E c off h₀ h₁
      omega
    rintro (a|s) (b|t) ha hb
    · exact (Bool.false_ne_true ((off a).symm.trans ha)).elim
    · exact (Bool.false_ne_true ((off a).symm.trans ha)).elim
    · exact (Bool.false_ne_true ((off b).symm.trans hb)).elim
    · cases s <;> cases t
      · rfl
      · exact (notBoth ha hb).elim
      · exact (notBoth hb ha).elim
      · rfl


/-- A handle's two old edges hit a small nontrivial cut when they
lie wholly on opposite shores. Such a cut had three edges. -/
def HitsSmallCuts : Prop :=
  ∀ c : V → Bool, (boundary G c).card≤3 →
    ¬((∀ x y,c x=true→c y=true→x=y) ∨ (∀ x y,c x=false→c y=false→x=y)) →
    3≤(boundary G c).card ∧
      ∃ b : Bool,(∀ x,E.Ends false x→c x=b) ∧ (∀ x,E.Ends true x→c x= !b)

theorem cyclic_host_of_hitting (cub : ∀v,G.degree v=3) (hit : HitsSmallCuts E) :
    SmallTrivial E.host := by
  classical
  intro c hc
  have low := (E.boundary_mono c).trans hc
  by_cases triv : (∀ x y,oldColor c x=true→ oldColor c y=true→x=y) ∨
      (∀ x y,oldColor c x=false→ oldColor c y=false→x=y)
  · rcases triv with h|h
    · exact Or.inl (true_side_subsingleton E cub c hc h)
    · right
      have hf : (boundary E.host (fun x=> !(c x))).card≤3 := by
        rw [boundary_flip_card]
        exact hc
      have hm : ∀ x y : V,oldColor (fun z=> !(c z)) x=true →
          oldColor (fun z=> !(c z)) y=true→x=y := by
        intro x y hx hy
        apply h x y
        · cases e : c (Sum.inl x)
          · exact e
          · simp [oldColor,e] at hx
        · cases e : c (Sum.inl y)
          · exact e
          · simp [oldColor,e] at hy
      intro a b ha hb
      exact true_side_subsingleton E cub _ hf hm a b (by simp [ha]) (by simp [hb])
  · obtain ⟨three,b,l,r⟩ := hit (oldColor c) low triv
    have same : c (Sum.inr false)=c (Sum.inr true) := by
      refine Classical.byContradiction ?_
      intro ne
      have q := extra_of_new_different E c ne
      omega
    have false_side (s : Bool) (off : ∀ x,E.Ends s x→ oldColor c x=false) :
        c (Sum.inr s)=false := by
      by_cases yes : c (Sum.inr s)=true
      · have q := extra_of_same_true_slot E c s yes off
        omega
      · exact Bool.eq_false_iff.mpr yes
    have true_side (s : Bool) (on : ∀ x,E.Ends s x→ oldColor c x=true) :
        c (Sum.inr s)=true := by
      by_cases no : c (Sum.inr s)=false
      · have q := extra_of_same_true_slot E (fun x=> !(c x)) s
          (by simp [no]) (fun x hx=>by simpa [oldColor] using on x hx)
        rw [boundary_flip_card] at q
        have q' : (boundary G (fun x=> !(oldColor c x))).card+1≤(boundary E.host c).card := q
        rw [boundary_flip_card] at q'
        omega
      · cases h : c (Sum.inr s)
        · exact (no h).elim
        · rfl
    exfalso
    cases hb : b
    · have off : c (Sum.inr false)=false := false_side false (fun x hx=>(l x hx).trans hb)
      have on : c (Sum.inr true)=true := true_side true (fun x hx=>by simpa only [hb,Bool.not_false] using r x hx)
      exact Bool.false_ne_true (off.symm.trans (same.trans on))
    · have on : c (Sum.inr false)=true := true_side false (fun x hx=>(l x hx).trans hb)
      have off : c (Sum.inr true)=false := false_side true (fun x hx=>by simpa only [hb,Bool.not_true] using r x hx)
      exact Bool.false_ne_true (off.symm.trans (same.symm.trans on))

open FourRingCyclicEquivalence FourRingReplica.Layout

/-- Reduces any graph admitting a pair of independent old edges on
opposite shores of every nontrivial three-edge cut. The resulting
P3-factor can avoid both old edges. -/
theorem factor_avoids_hitting_pair (promise : CyclicUniversal.{u})
    (cub : ∀v,G.degree v=3) (d : 6∣Fintype.card V)
    (hit : HitsSmallCuts E) : KelmansStarter.HasP3Factor E.deleteChosen := by
  classical
  have t : SmallTrivial E.host := cyclic_host_of_hitting E cub hit
  have hc := three_connected_of_small_trivial E.host (E.cubic cub) E.host_order_ge_four t
  have res : Fintype.card (V ⊕ Bool)%6=2 := by
    rw [Edges.host_order]
    obtain ⟨m,m6⟩ := d
    omega
  let y : Bool → V⊕Bool := Sum.inr
  have edge : E.host.Adj (y false) (y true) := Bool.false_ne_true
  have f := cyclic4_factor_implies_t2 (U:=V⊕Bool) (A:=E.host) promise (E.cubic cub) hc t res y edge
  have fp : KelmansStarter.HasP3Factor (E.host.induce {x | x≠Sum.inr false ∧ x≠Sum.inr true}) := f
  exact factor_iso _ _ E.deleted_two_iso.symm fp

#print axioms cyclic_host_of_hitting
#print axioms factor_avoids_hitting_pair
end
end KelmansCactus.AtomicBridge.HandleExtension.Edges.AtomicHitting
