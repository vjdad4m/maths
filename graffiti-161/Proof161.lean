import Lean

set_option linter.unusedSectionVars false

namespace Graffiti161
universe u
variable {V : Type u} [DecidableEq V]
abbrev Graph (V : Type u) := V → V → Prop

def Add (T : Graph V) (p y : V) : Graph V :=
  fun a b => T a b ∨ (a = p ∧ b = y) ∨ (a = y ∧ b = p)

/-- Trees begin at one vertex and are extended by one pendant vertex. -/
inductive Tree (G : Graph V) : List V → Graph V → Prop
  | single (r : V) : Tree G [r] (fun _ _ => False)
  | grow {xs T p y} : Tree G xs T → p ∈ xs → y ∉ xs → G p y →
      Tree G (y :: xs) (Add T p y)

def Leaf (T : Graph V) (v : V) : Prop :=
  ∃ w, T v w ∧ ∀ z, T v z → z = w

inductive Walk (G : Graph V) (a : V) : V → Prop
  | refl : Walk G a a
  | tail {b c} : Walk G a b → G b c → Walk G a c

def Connected (G : Graph V) := ∀ a b, Walk G a b

def Spanning (G : Graph V) (k : Nat) :=
  ∃ (xs : List V) (T : Graph V) (ls : List V), Tree G xs T ∧ (∀ v : V, v ∈ xs) ∧ ls.Nodup ∧
    (∀ v ∈ ls, Leaf T v) ∧ k ≤ ls.length

theorem supported {G : Graph V} {xs T} (ht : Tree G xs T) :
    ∀ a b, T a b → a ∈ xs ∧ b ∈ xs := by
  induction ht with
  | single => intro a b h; contradiction
  | @grow xs T p y ht hp hy hG ih =>
    intro a b h
    rcases h with h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · obtain ⟨ha,hb⟩ := ih a b h
      exact ⟨List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb⟩
    · exact ⟨List.mem_cons_of_mem _ hp, List.mem_cons_self⟩
    · exact ⟨List.mem_cons_self,List.mem_cons_of_mem _ hp⟩

theorem treeNodup {G : Graph V} {xs T} (ht : Tree G xs T) : xs.Nodup := by
  induction ht with
  | single => simp
  | grow _ _ hy _ ih => exact List.nodup_cons.mpr ⟨hy,ih⟩

theorem newLeaf {G : Graph V} {xs T p y} (ht : Tree G xs T)
    (hp : p ∈ xs) (hy : y ∉ xs) : Leaf (Add T p y) y := by
  refine ⟨p, Or.inr (Or.inr ⟨rfl,rfl⟩), ?_⟩
  intro z h
  rcases h with h | ⟨h,_⟩ | ⟨_,h⟩
  · exact False.elim (hy ((supported ht _ _ h).1))
  · exact False.elim (hy (h ▸ hp))
  · exact h

theorem oldLeaf {T : Graph V} {p y v : V} (hleaf : Leaf T v)
    (hp : v ≠ p) (hy : v ≠ y) : Leaf (Add T p y) v := by
  obtain ⟨w,hw,hu⟩ := hleaf
  exact ⟨w,Or.inl hw,fun z hz => by
    rcases hz with h | ⟨h,_⟩ | ⟨h,_⟩
    · exact hu z h
    · exact False.elim (hp h)
    · exact False.elim (hy h)⟩

theorem cross {G : Graph V} (hc : Connected G) (xs : List V) {a b}
    (ha : a ∈ xs) (hb : b ∉ xs) :
    ∃ p ∈ xs, ∃ y ∉ xs, G p y := by
  have walk := hc a b
  induction walk with
  | refl => exact False.elim (hb ha)
  | @tail j k w hj ih =>
    by_cases hm : j ∈ xs
    · exact ⟨j,hm,k,hb,hj⟩
    · exact ih hm

private theorem eraseKeeps {a b : V} {xs : List V} (hm : a ∈ xs) (h : a ≠ b) :
    a ∈ xs.erase b := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    by_cases hxb : x = b
    · subst x
      simp [h] at hm
      simpa using hm
    · rw [List.erase_cons_tail (by simpa using hxb)]
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hm)

private theorem lenBound (xs all : List V) (hnd : xs.Nodup) (sub : xs ⊆ all) :
    xs.length ≤ all.length := by
  induction xs generalizing all with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hna,hn⟩ := List.nodup_cons.mp hnd
    have ha : a ∈ all := sub List.mem_cons_self
    have hsub : xs ⊆ all.erase a := by
      intro x hx
      refine eraseKeeps (sub (List.mem_cons_of_mem _ hx)) ?_
      exact fun h => hna (h ▸ hx)
    have hh := ih (all.erase a) hn hsub
    rw [List.length_erase_of_mem ha] at hh
    have hpos : 0 < all.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

theorem extend {G : Graph V} (hc : Connected G) (all : List V)
    (ha : ∀ v, v ∈ all) (r : V) (k fuel : Nat) :
    ∀ (xs : List V) (T : Graph V) (ls : List V), Tree G xs T → r ∈ xs → ls.Nodup →
      (∀ v ∈ ls, Leaf T v) → k ≤ ls.length →
      all.length - xs.length ≤ fuel → Spanning G k := by
  induction fuel with
  | zero =>
    intro xs T ls ht hr hn hl hk hf
    classical
    by_cases hh : ∀ v : V, v ∈ xs
    · exact ⟨xs,T,ls,ht,hh,hn,hl,hk⟩
    · obtain ⟨v,hv⟩ := Classical.not_forall.mp hh
      have hsub : v :: xs ⊆ all := fun {_} _ => ha _
      have hlen := lenBound (v :: xs) all (List.nodup_cons.mpr ⟨hv,treeNodup ht⟩) hsub
      simp only [List.length_cons] at hlen
      omega
  | succ f ih =>
    intro xs T ls ht hr hn hl hk hf
    classical
    by_cases hh : ∀ v : V, v ∈ xs
    · exact ⟨xs,T,ls,ht,hh,hn,hl,hk⟩
    · obtain ⟨v,hv⟩ := Classical.not_forall.mp hh
      obtain ⟨p,hp,y,hy,he⟩ := cross hc xs hr hv
      have hm : ∀ z ∈ ls, z ∈ xs := by
        intro z hz
        obtain ⟨w,hw,_⟩ := hl z hz
        exact (supported ht z w hw).1
      let ls' := y :: ls.erase p
      have hn' : ls'.Nodup := List.nodup_cons.mpr
        ⟨fun h => hy (hm _ (List.mem_of_mem_erase h)),hn.erase p⟩
      have hl' : ∀ z ∈ ls', Leaf (Add T p y) z := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact newLeaf ht hp hy
        · have hp' : z ≠ p := fun h => hn.not_mem_erase (h ▸ hz)
          have hz' := List.mem_of_mem_erase hz
          have hy' : z ≠ y := fun h => hy (h ▸ hm _ hz')
          exact oldLeaf (hl _ hz') hp' hy'
      have hk' : k ≤ ls'.length := by
        simp only [ls',List.length_cons,List.length_erase]
        split <;> omega
      have hf' : all.length - (y :: xs).length ≤ f := by
        simp only [List.length_cons]
        omega
      exact ih (y :: xs) (Add T p y) ls' (Tree.grow ht hp hy he)
        (List.mem_cons_of_mem _ hr) hn' hl' hk' hf'

private theorem makeStar {G : Graph V} (r : V) (ns : List V)
    (hn : ns.Nodup) (hr : r ∉ ns) (he : ∀ v ∈ ns, G r v) :
    ∃ T, Tree G (ns ++ [r]) T ∧ ∀ v ∈ ns, Leaf T v := by
  induction ns with
  | nil => exact ⟨_,Tree.single r,by simp⟩
  | cons y ys ih =>
    obtain ⟨hy,hyn⟩ := List.nodup_cons.mp hn
    have hr' : r ∉ ys := fun h => hr (List.mem_cons_of_mem _ h)
    have hyr : y ≠ r := fun h => hr (h ▸ List.mem_cons_self)
    obtain ⟨T,ht,hl⟩ := ih hyn hr' (fun v hv => he v (List.mem_cons_of_mem _ hv))
    have hnew : y ∉ ys ++ [r] := by simp [hy,hyr]
    have hroot : r ∈ ys ++ [r] := by simp
    refine ⟨Add T r y,Tree.grow ht hroot hnew (he y List.mem_cons_self),?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact newLeaf ht hroot hnew
    · exact oldLeaf (hl v hv) (fun h => hr' (h ▸ hv)) (fun h => hy (h ▸ hv))

theorem degreeBound {G : Graph V} (hc : Connected G) (all : List V)
    (ha : ∀ v, v ∈ all) (r : V) (ns : List V)
    (hn : ns.Nodup) (hr : r ∉ ns) (he : ∀ v ∈ ns, G r v) :
    Spanning G ns.length := by
  obtain ⟨T,ht,hl⟩ := makeStar r ns hn hr he
  exact extend hc all ha r ns.length all.length (ns ++ [r]) T ns ht (by simp) hn hl
    (Nat.le_refl _) (Nat.sub_le _ _)

/-- The stronger proper-clique bound. -/
theorem properClique {G : Graph V} (hc : Connected G) (all : List V)
    (ha : ∀ v, v ∈ all) (outside : V) (C : List V) (hn : C.Nodup)
    (ho : outside ∉ C)
    (hC : ∀ p ∈ C, ∀ q ∈ C, p ≠ q → G p q) :
    Spanning G C.length := by
  cases C with
  | nil =>
    apply degreeBound hc all ha outside []
    · simp
    · simp
    · simp
  | cons a cs =>
    obtain ⟨p,hp,y,hy,he⟩ := cross hc (a :: cs) List.mem_cons_self ho
    let C := a :: cs
    have hh : Spanning G (y :: C.erase p).length := by
      apply degreeBound hc all ha p (y :: C.erase p)
      · exact List.nodup_cons.mpr ⟨fun h => hy (List.mem_of_mem_erase h),hn.erase p⟩
      · intro h
        rcases List.mem_cons.mp h with h | h
        · exact hy (h ▸ hp)
        · exact hn.not_mem_erase h
      · intro v h
        rcases List.mem_cons.mp h with rfl | h
        · exact he
        · exact hC p hp v (List.mem_of_mem_erase h)
            (fun h' => hn.not_mem_erase (h' ▸ h))
    have hnlen : (y :: C.erase p).length = C.length := by
      have hpC : p ∈ C := hp
      have hpos := List.length_pos_of_mem hpC
      rw [List.length_cons,List.length_erase_of_mem hpC]
      omega
    rw [hnlen] at hh
    exact hh

/-- A locally independent set in the complement is a proper clique of G.
    The statement applies to every such set, hence also a largest one. -/
theorem conjecture161 {G : Graph V} (hc : Connected G) (all : List V)
    (ha : ∀ v, v ∈ all) (center : V) (I : List V) (hI : I.Nodup)
    (inComplementNeighborhood : ∀ v ∈ I, v ≠ center ∧ ¬ G center v)
    (independentInComplement : ∀ p ∈ I, ∀ q ∈ I, p ≠ q → ¬ (¬ G p q)) :
    Spanning G I.length := by
  classical
  exact properClique hc all ha center I hI
    (fun h => (inComplementNeighborhood center h).1 rfl)
    (fun p hp q hq hne => Classical.byContradiction
      (independentInComplement p hp q hq hne))

#print axioms conjecture161
end Graffiti161
