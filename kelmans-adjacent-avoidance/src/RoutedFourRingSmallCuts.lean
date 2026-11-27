import RoutedFourRingHostCuts

open Finset SimpleGraph
namespace KelmansCactus.FourRingReplica.Layout
open FourRingBudget FourRingCutChoices FourRingCutAux FourRingPropagation
noncomputable section
variable {U J : Type*} [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]
variable {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r) (next : Equiv.Perm J) (rev : J→Bool)
variable (c : Host J r→Bool)

private def routed_MixedCell (i : J) : Prop :=
  (∃x : Piece r,c (i,x)=true) ∧ (∃x : Piece r,c (i,x)=false)

private def routed_colour (i : J) : Bool := c (i,L.port (false,false))

omit [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] in
private theorem routed_healthy {i : J} (nm : ¬routed_MixedCell c i) (x : Piece r) :
    c (i,x)=L.routed_colour c i := by
  by_contra ne
  cases h : c (i,x) <;> cases h' : L.routed_colour c i
  · exact ne (h.trans h'.symm)
  · exact nm ⟨⟨L.port (false,false),h'⟩,⟨x,h⟩⟩
  · exact nm ⟨⟨x,h⟩,⟨L.port (false,false),h'⟩⟩
  · exact ne (h.trans h'.symm)

private def routed_bundle (i : J) : Finset (J×Bool) := {(i,false),(i,true)}

omit [Fintype U] [DecidableEq U] in
private theorem routed_pair_active {i : J} (h1 : ¬routed_MixedCell c i) (h2 : ¬routed_MixedCell c (next i))
    (different : L.routed_colour c i≠L.routed_colour c (next i)) :
    routed_bundle i⊆L.routedActiveSeams next rev c := by
  intro z hz
  obtain ⟨j,b⟩ := z
  have ij : j=i := by
    simp only [routed_bundle,mem_insert,mem_singleton,Prod.mk.injEq] at hz
    exact hz.elim And.left And.left
  subst j
  apply (L.routedMemActive next rev c).mpr
  change c (i,L.port (swapSlot (rev i) (true,b)))≠c (next i,L.port (swapSlot (rev (next i)) (false,b)))
  rwa [L.routed_healthy c h1,L.routed_healthy c h2]

omit [Fintype J] in
private theorem routed_bundle_card (i : J) : (routed_bundle i).card=2 := by simp [routed_bundle]

omit [Fintype J] in
private theorem routed_bundles_disj {i j : J} (ne : i≠j) :
    Disjoint (routed_bundle i) (routed_bundle j) := by
  apply disjoint_left.mpr
  intro x xi xj
  have eq (k : J) {v : J×Bool} (vIn : v∈routed_bundle k) : v.1=k := by
    simp only [routed_bundle,mem_insert,mem_singleton] at vIn
    rcases vIn with rfl|rfl <;> rfl
  exact ne ((eq i xi).symm.trans (eq j xj))

omit [Fintype U] [DecidableEq U] in
private theorem routed_active_four {i j : J} (ne : i≠j)
    (a : routed_bundle i⊆L.routedActiveSeams next rev c) (b : routed_bundle j⊆L.routedActiveSeams next rev c) :
    4≤(L.routedActiveSeams next rev c).card := by
  have q := card_le_card (union_subset a b)
  rw [card_union_of_disjoint (routed_bundles_disj ne),routed_bundle_card,routed_bundle_card] at q
  exact q

omit [DecidableEq J] in
private theorem routed_sum_at_point (f : J→ℕ) (i : J) : f i≤∑ j,f j :=
  single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ i)

private theorem routed_sum_at_two (f : J→ℕ) {i j : J} (ne : i≠j) :
    f i+f j≤∑ z,f z := by
  have b : (∑ z∈({i,j}:Finset J),f z)≤∑ z,f z := sum_le_sum_of_subset (subset_univ _)
  simpa [sum_insert,ne] using b

omit [Fintype J] [DecidableEq J] in
private theorem routed_previous_ne (fixed : ∀ i,next i≠i) (i : J) : next.symm i≠i := by
  intro e
  have g := congrArg next e
  exact fixed i (by simpa using g.symm)

private def routed_route (i : J) : Option Slot→J×Bool
  | none => (i,false)
  | some s =>
    let k := swapSlot (rev i) s
    if k.1 then (i,k.2) else (next.symm i,k.2)

omit [Fintype U] in
private theorem routed_outside_uniform_cap_cost (fixed : ∀ i,next i≠i)
    (i : J) (b : Bool) (out : ∀ j≠i,∀ x : Piece r,c (j,x)=b) :
    extensionCost (fun s=>cellColour c i (L.port s)) b b ≤ (L.routedActiveSeams next rev c).card := by
  classical
  let D := L.capActive (cellColour c i) b b
  have no (j : Option Slot) (m : j∈D) : j≠none := by
    rintro rfl
    have k : extend (cellColour c i) b b (r false)≠extend (cellColour c i) b b (r true) :=
      (mem_filter.mp m).2
    rw [extend_false,L.extend_true] at k
    exact k rfl
  have inj : Set.InjOn (routed_route next rev i) D := by
    intro a aD z zD e
    cases a with
    | none => exact (no none aD rfl).elim
    | some a =>
      cases z with
      | none => exact (no none zD rfl).elim
      | some z =>
        suffices swapSlot (rev i) a=swapSlot (rev i) z from
          congrArg some (swapSlot_inj (rev i) this)
        simp only [routed_route] at e
        generalize aa : swapSlot (rev i) a = a' at e ⊢
        generalize zz : swapSlot (rev i) z = z' at e ⊢
        rcases a' with ⟨a,x⟩
        rcases z' with ⟨z,y⟩
        cases a <;> cases z
        · exact Prod.ext rfl (congrArg (fun p : J×Bool=>p.2) e)
        · exact (routed_previous_ne next fixed i (congrArg Prod.fst e)).elim
        · exact (routed_previous_ne next fixed i (congrArg Prod.fst e).symm).elim
        · exact Prod.ext rfl (congrArg (fun p : J×Bool=>p.2) e)
  have incl : D.image (routed_route next rev i)⊆L.routedActiveSeams next rev c := by
    intro q qm
    obtain ⟨s,sm,rfl⟩ := mem_image.mp qm
    cases s with
    | none => exact (no none sm rfl).elim
    | some s =>
      have old : extend (cellColour c i) b b (r s.1)=b := by
        cases d : s.1
        · exact extend_false (cellColour c i) b b
        · exact L.extend_true (cellColour c i) b b
      have odd : b≠c (i,L.port s) := by
        have p := (mem_filter.mp sm).2
        change extend (cellColour c i) b b (r s.1)≠extend (cellColour c i) b b (L.port s).val at p
        rw [extend_piece,old] at p
        exact p
      rcases ss : swapSlot (rev i) s with ⟨d,f⟩
      have back : swapSlot (rev i) (d,f)=s := by
        rw [←ss,swapSlot_twice]
      apply (L.routedMemActive next rev c).mpr
      simp only [routed_route,ss]
      cases d
      · change c (next.symm i,L.port (swapSlot (rev (next.symm i)) (true,f)))≠
            c (next (next.symm i),L.port (swapSlot (rev (next (next.symm i))) (false,f)))
        rw [next.apply_symm_apply,back,out (next.symm i) (routed_previous_ne next fixed i)]
        exact odd
      · change c (i,L.port (swapSlot (rev i) (true,f)))≠
            c (next i,L.port (swapSlot (rev (next i)) (false,f)))
        rw [back,out (next i) (fixed i)]
        exact Ne.symm odd
  have le := card_le_card incl
  rw [card_image_of_injOn inj,L.active_card] at le
  exact le

include L in
omit [Fintype U] [Fintype J] [DecidableEq J] in
private theorem routed_minority_unique (i : J) (b : Bool) (out : ∀ j≠i,∀ x : Piece r,c (j,x)=b)
    (trivial : (∀ x y, extend (cellColour c i) b b x=true →
       extend (cellColour c i) b b y=true→x=y) ∨
     (∀ x y, extend (cellColour c i) b b x=false →
       extend (cellColour c i) b b y=false→x=y)) :
    ∀ x y : Host J r,c x= !b → c y= !b → x=y := by
  intro x y cx cy
  have coords (z : Host J r) (cz : c z= !b) : z.1=i := by
    by_contra! ne
    have eq : c z=b := out z.1 ne z.2
    cases b <;> simp_all
  have cxI : extend (cellColour c i) b b x.2.val= !b := by
    rw [extend_piece]
    change c (i,x.2)= !b
    exact (Prod.ext (coords x cx).symm rfl : (i,x.2)=x).symm ▸ cx
  have cyI : extend (cellColour c i) b b y.2.val= !b := by
    rw [extend_piece]
    change c (i,y.2)= !b
    exact (Prod.ext (coords y cy).symm rfl : (i,y.2)=y).symm ▸ cy
  have rootF := extend_false (cellColour c i) b b
  have rootT := L.extend_true (cellColour c i) b b
  apply Prod.ext ((coords x cx).trans (coords y cy).symm)
  apply Subtype.ext
  rcases trivial with tr|tr <;> cases b
  · exact tr _ _ cxI cyI
  · exact (L.rootEdge.ne (tr _ _ rootF rootT)).elim
  · exact (L.rootEdge.ne (tr _ _ rootF rootT)).elim
  · exact tr _ _ cxI cyI

/-- When the common cap has no small nontrivial cut, neither does
the paired four-port ring. Ambient edge counts and routed_healthy-cell
propagation are both in the proof. -/
theorem routedPreservesSmall (ring : Circular next) [DecidableRel A.Adj]
    (cub : ∀v,A.degree v=3) (small : SmallTrivial A) :
    SmallTrivial (L.routedGraph next rev ring.fixed) := by
  classical
  intro c low
  let f := L.routed_colour c
  have budget := L.routedHostCutLower next rev ring.fixed c
  have mixedTwo {i : J} (m : routed_MixedCell c i) : 2 ≤ insideCount (A:=A) c i :=
    L.mixed_internal_two cub small (cellColour c i) m.1 m.2
  by_cases found : ∃ i,routed_MixedCell c i
  · obtain ⟨i,mix⟩ := found
    have notOther {j : J} (jNot : j≠i) : ¬routed_MixedCell c j := by
      intro mm
      have t := routed_sum_at_two (insideCount (A:=A) c) (Ne.symm jNot)
      have a := mixedTwo mix
      have b := mixedTwo mm
      omega
    have rise (j : J) (jNot : j≠i) (nextNot : next j≠i) : f j=f (next j) := by
      by_contra dn
      have b := L.routed_pair_active next rev c (notOther jNot) (notOther nextNot) dn
      have n := card_le_card b
      rw [routed_bundle_card] at n
      have d := routed_sum_at_point (insideCount (A:=A) c) i
      have q := mixedTwo mix
      omega
    let b := f (next i)
    have out : ∀j≠i,∀ x : Piece r,c (j,x)=b := by
      intro j ne x
      exact (L.routed_healthy c (notOther ne) x).trans
        (ring.afterRemoval i f rise j (next i) ne (ring.fixed i))
    have c1 := L.cap_cut_upper (cellColour c i) b b
    have c2 := L.routed_outside_uniform_cap_cost next rev c ring.fixed i b out
    have n := routed_sum_at_point (insideCount (A:=A) c) i
    change (boundary (minor A r) (cellColour c i)).card≤_ at n
    have capSize : (boundary A (extend (cellColour c i) b b)).card≤3 := by omega
    have minor := L.routed_minority_unique c i b out (small _ capSize)
    cases h : b
    · exact Or.inl (by simpa only [h,Bool.not_false] using minor)
    · exact Or.inr (by simpa only [h,Bool.not_true] using minor)
  · push_neg at found
    have one (i j : J) (a : f i≠f (next i)) (b : f j≠f (next j)) : i=j := by
      refine Classical.byContradiction ?_
      intro ne
      have lb := L.routed_active_four next rev c ne
        (L.routed_pair_active next rev c (found i) (found (next i)) a)
        (L.routed_pair_active next rev c (found j) (found (next j)) b)
      omega
    have global := all_equal_of_one_break next ring f one
    by_cases some : ∃ x : Host J r,c x=true
    · obtain ⟨x,hx⟩ := some
      right
      intro y z hy _
      have eq : c x=c y :=
        (L.routed_healthy c (found x.1) x.2).trans ((global x.1 y.1).trans (L.routed_healthy c (found y.1) y.2).symm)
      rw [hx,hy] at eq
      contradiction
    · left
      intro x _ hx _
      exact (some ⟨x,hx⟩).elim

#print axioms routedPreservesSmall
end
end KelmansCactus.FourRingReplica.Layout
