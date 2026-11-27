import RemoteBudgetComponent

namespace KelmansCactus.AtomicBridge.RemotePairStrip
open SimpleGraph Finset
open scoped BigOperators
open RemoteBudgetComponent (Mate cost)
open RemoteRankUnion (Marking)
variable {V I : Type*} {G : SimpleGraph V}

def Closed (q : Mate G) (S : Set V) : Prop :=
  ∀ x∈S,q.mate x∈S

theorem not_closed_reverse {q : Mate G} {S : Set V} (h : Closed q S)
    {x : V} (outside : x∉S) : q.mate x∉S := by
  intro mem
  exact outside (by simpa only [q.inv x] using h _ mem)

/-- Glue complete restrictions of two matchings on the two sides of a closed
support, without creating a cross-edge or changing the outside restrictions. -/
noncomputable def mix (p q : Mate G) (S : Set V)
    (cp : Closed p S) (cq : Closed q S) : Mate G := by
  classical
  let m (x : V) := if x∈S then p.mate x else q.mate x
  refine ⟨m,?_,?_⟩
  · intro x
    by_cases yes : x∈S
    · simpa only [m,if_pos yes,if_pos (cp x yes)] using p.inv x
    · simpa only [m,if_neg yes,if_neg (not_closed_reverse cq yes)] using q.inv x
  · intro x
    by_cases yes : x∈S
    · simpa only [m,if_pos yes] using p.edge x
    · simpa only [m,if_neg yes] using q.edge x

theorem mix_in (p q : Mate G) (S : Set V) (cp : Closed p S) (cq : Closed q S)
    {x : V} (mem : x∈S) : (mix p q S cp cq).mate x=p.mate x := by
  classical
  simp [mix,mem]

theorem mix_out (p q : Mate G) (S : Set V) (cp : Closed p S) (cq : Closed q S)
    {x : V} (mem : x∉S) : (mix p q S cp cq).mate x=q.mate x := by
  classical
  simp [mix,mem]

/-- An outside alternating strip is specified only by its two exposed
p-contact vertices and exact old/target mate closure on the outside.
The inside square edge joining the corresponding two corners is supplied
separately, so the exterior geometry alone does not select an inside pairing. -/
structure Strip (p q : Mate G) (a b : V) where
  region : Set V
  aOut : a∉region
  bOut : b∉region
  pa : p.mate a∈region
  pb : p.mate b∈region
  p_internal : ∀ x∈region,x≠p.mate a → x≠p.mate b → p.mate x∈region
  q_internal : Closed q region

namespace Strip
variable {p q : Mate G} {a b : V} (T : Strip p q a b)

def support : Set V := {x | x∈T.region ∨ x=a ∨ x=b}

theorem old_closed : Closed p T.support := by
  classical
  intro x h
  rcases h with inside|rfl|rfl
  · by_cases e : x=p.mate a
    · exact Or.inr (Or.inl (e.trans rfl ▸ p.inv a))
    by_cases f : x=p.mate b
    · exact Or.inr (Or.inr (f.trans rfl ▸ p.inv b))
    exact Or.inl (T.p_internal x inside e f)
  · exact Or.inl T.pa
  · exact Or.inl T.pb

/-- Rewire an exterior strip while joining its two exposed interior corners
by a genuine edge of the square. All other mate edges stay unchanged. -/
noncomputable def release (ab : G.Adj a b) : Mate G := by
  classical
  let m (x : V) := if x=a then b else if x=b then a else if x∈T.region then q.mate x else p.mate x
  have nab := G.ne_of_adj ab
  have mba : m b=a := by simp [m,nab.symm]
  have mab : m a=b := by simp [m]
  have inRegion {x : V} (inside : x∈T.region) : m x=q.mate x := by
    have xa : x≠a := fun e=>T.aOut (e ▸ inside)
    have xb : x≠b := fun e=>T.bOut (e ▸ inside)
    simp [m,xa,xb,inside]
  have outRegion {x : V} (outside : x∉T.support) : m x=p.mate x := by
    have xa : x≠a := fun e=>outside (Or.inr (Or.inl e))
    have xb : x≠b := fun e=>outside (Or.inr (Or.inr e))
    have xo : x∉T.region := fun h=>outside (Or.inl h)
    simp [m,xa,xb,xo]
  refine ⟨m,?_,?_⟩
  · intro x
    by_cases xa : x=a
    · subst x
      rw [mab,mba]
    by_cases xb : x=b
    · subst x
      rw [mba,mab]
    by_cases inside : x∈T.region
    · rw [inRegion inside,inRegion (T.q_internal x inside),q.inv x]
    · have out : x∉T.support := fun h=>h.elim inside (fun h=>h.elim xa xb)
      rw [outRegion out,outRegion (not_closed_reverse T.old_closed out),p.inv x]
  · intro x
    by_cases xa : x=a
    · subst x
      rwa [mab]
    by_cases xb : x=b
    · subst x
      rw [mba]
      exact ab.symm
    by_cases inside : x∈T.region
    · rw [inRegion inside]
      exact q.edge x
    · rw [outRegion (fun h=>h.elim inside (fun h=>h.elim xa xb))]
      exact p.edge x

theorem release_a (ab : G.Adj a b) : (T.release ab).mate a=b := by
  classical
  simp [release]
theorem release_b (ab : G.Adj a b) : (T.release ab).mate b=a := by
  classical
  simp [release,(G.ne_of_adj ab).symm]

theorem release_old_out (ab : G.Adj a b) {x : V} (out : x∉T.support) :
    (T.release ab).mate x=p.mate x := by
  classical
  have xa : x≠a := fun e=>out (Or.inr (Or.inl e))
  have xb : x≠b := fun e=>out (Or.inr (Or.inr e))
  have xo : x∉T.region := fun h=>out (Or.inl h)
  simp [release,xa,xb,xo]

theorem release_region (ab : G.Adj a b) {x : V} (inside : x∈T.region) :
    (T.release ab).mate x=q.mate x := by
  classical
  have xa : x≠a := fun e=>T.aOut (e ▸ inside)
  have xb : x≠b := fun e=>T.bOut (e ▸ inside)
  simp [release,xa,xb,inside]

theorem release_changes_a (ab : G.Adj a b) : (T.release ab).mate a≠p.mate a := by
  rw [T.release_a ab]
  intro e
  exact T.bOut (e.symm ▸ T.pa)

theorem release_changes_b (ab : G.Adj a b) : (T.release ab).mate b≠p.mate b := by
  rw [T.release_b ab]
  intro e
  exact T.aOut (e.symm ▸ T.pb)

/-- On marked endpoints the splice copies exactly the target bits in the outside
strip and baseline bits elsewhere, when neither corner is marked. -/
theorem release_indicator [Fintype I] (M : Marking G I) (ab : G.Adj a b)
    (noA : ∀ i,M.a i≠a) (noB : ∀ i,M.a i≠b) (i : I) :
    (M.a i∈T.region → (T.release ab).mate (M.a i)=q.mate (M.a i)) ∧
      (M.a i∉T.region → (T.release ab).mate (M.a i)=p.mate (M.a i)) := by
  exact ⟨fun h=>T.release_region ab h,fun n=>T.release_old_out ab
    (fun m=>m.elim n (fun r=>r.elim (noA i) (noB i)))⟩

end Strip

theorem closed_union (q : Mate G) {S T : Set V} (hS : Closed q S) (hT : Closed q T) :
    Closed q (S∪T) := by
  intro x hx
  exact hx.elim (fun h=>Or.inl (hS _ h)) (fun h=>Or.inr (hT _ h))

/-- Conservation for one strip plus its reciprocal splice. This works when
both matchings preserve the full support enclosing the two corners. -/
theorem one_cost_bound [Fintype I] (M : Marking G I) (p q : Mate G) {a b : V}
    (T : Strip p q a b) (ab : G.Adj a b)
    (close : Closed q T.support)
    (noA : ∀ i,M.a i≠a) (noB : ∀ i,M.a i≠b)
    (min : ∀ r,cost M p≤cost M r) :
    cost M (T.release ab)≤cost M q := by
  classical
  let R := mix p q T.support T.old_closed close
  have real : cost M (T.release ab)+cost M R=cost M p+cost M q := by
    unfold cost
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have bits := T.release_indicator M ab noA noB i
    by_cases h : M.a i∈T.region
    · rw [bits.1 h,mix_in p q T.support T.old_closed close (Or.inl h),Nat.add_comm]
    · have outside : M.a i∉T.support := fun r=>r.elim h (fun z=>z.elim (noA i) (noB i))
      rw [bits.2 h,mix_out p q T.support T.old_closed close outside]
  have lower := min R
  omega

/-- Conservation for two disjoint strips and an unswitched remainder.
The target need preserve only their union, not either pair of corners.
This is why a four-crossing alternating circuit can be split into two
individually legal moves without increasing the total budget charge. -/
theorem two_cost_bound [Fintype I] (M : Marking G I) (p q : Mate G)
    {a b c d : V} (A : Strip p q a b) (B : Strip p q c d)
    (ab : G.Adj a b) (cd : G.Adj c d)
    (apart : ∀ x∈A.region,x∉B.region)
    (close : Closed q (A.support∪B.support))
    (noA : ∀ i,M.a i≠a) (noB : ∀ i,M.a i≠b)
    (noC : ∀ i,M.a i≠c) (noD : ∀ i,M.a i≠d)
    (min : ∀ r,cost M p≤cost M r) :
    (cost M (A.release ab)-cost M p)+(cost M (B.release cd)-cost M p)≤cost M q-cost M p := by
  classical
  let S := A.support∪B.support
  have cp : Closed p S := closed_union p A.old_closed B.old_closed
  let R := mix p q S cp close
  have conservation :
      cost M (A.release ab)+cost M (B.release cd)+cost M R=cost M p+cost M p+cost M q := by
    unfold cost
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have Aread := A.release_indicator M ab noA noB i
    have Bread := B.release_indicator M cd noC noD i
    by_cases hA : M.a i∈A.region
    · rw [Aread.1 hA,Bread.2 (apart _ hA),mix_in p q S cp close
        (Or.inl (Or.inl hA))]
      omega
    by_cases hB : M.a i∈B.region
    · rw [Aread.2 hA,Bread.1 hB,mix_in p q S cp close (Or.inr (Or.inl hB))]
      omega
    · have outside : M.a i∉S := by
        intro t
        rcases t with t|t
        · exact t.elim hA (fun w=>w.elim (noA i) (noB i))
        · exact t.elim hB (fun w=>w.elim (noC i) (noD i))
      rw [Aread.2 hA,Bread.2 hB,mix_out p q S cp close outside]
  have lowerA := min (A.release ab)
  have lowerB := min (B.release cd)
  have lowerR := min R
  have lowerQ := min q
  omega

#print axioms Strip.release_changes_a
#print axioms one_cost_bound
#print axioms two_cost_bound
end KelmansCactus.AtomicBridge.RemotePairStrip
