import DoubleShift183

namespace Graffiti183.Exceptional
open SimpleGraph Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000

variable {V : Type*} {G : SimpleGraph V} {m : ℕ}

def ShortRun (G : SimpleGraph V) (f : Fin m ↪ V) (z : V) : Prop :=
  ∃ a : Fin m, ∃ k : ℕ, (k=3 ∨ k=4) ∧
    ∀ i : Fin m, G.Adj z (f (rot a i)) ↔ i.val < k

def ExteriorProfiles (G : SimpleGraph V) (f : Fin m ↪ V) : Prop :=
  ∀ z ∉ indexSet f, ShortRun G f z ∨
    ∃ a : Fin m, ∃ d : ℕ, 3 ≤ d ∧ d ≤ m-3 ∧
      (∀ i : Fin m, G.Adj z (f (rot a i)) ↔ i.val=0 ∨ i.val=1 ∨ i.val=d ∨ i.val=d+1)

private lemma path_two_here (hc : G.Connected) {x y : V} (hd : G.dist x y = 2) :
    ∃ a, G.Adj x a ∧ G.Adj a y := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  rw [hd] at hp
  cases p with
  | nil => simp at hp
  | @cons _ a _ e p =>
    cases p with
    | nil => simp at hp
    | cons f p =>
      cases p with
      | nil => exact ⟨a,e,f⟩
      | cons _ _ => simp only [Walk.length_cons] at hp; omega

private lemma external_common_neighbor (hc : G.Connected)
    (f : Fin m ↪ V) (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    {u d : Fin m} (hd : 3 ≤ d.val) (hd' : d.val ≤ m-3)
    (hn : G.dist (f u) (f (rot u d)) ≤ 2) :
    ∃ z ∉ indexSet f, G.Adj z (f u) ∧ G.Adj z (f (rot u d)) := by
  let o : Fin m := ⟨0,by have := u.isLt; omega⟩
  have h0 : rot u o = u := rot_zero u (by have := u.isLt; omega)
  have nz : f u ≠ f (rot u d) := by
    intro eq
    have e1 := f.injective eq
    have e2 := rot_injective u (h0.trans e1)
    have ev : 0 = d.val := congrArg Fin.val e2
    omega
  have notadj : ¬G.Adj (f u) (f (rot u d)) := by
    intro e
    have e' : G.Adj (f (rot u o)) (f (rot u d)) := h0.symm ▸ e
    have h := (cycleAdj_rotate (by omega) u o d).mp ((hcyc _ _).mp e')
    unfold CycleAdj at h
    change 0+1=d.val ∨ d.val+1=0 ∨ (0=0 ∧ d.val+1=m) ∨ (d.val=0 ∧ 0+1=m) at h
    omega
  have h1 : G.dist (f u) (f (rot u d)) ≠ 1 := fun h => notadj (dist_eq_one_iff_adj.mp h)
  have hf : G.dist (f u) (f (rot u d)) ≠ 0 := fun h => nz (hc.dist_eq_zero_iff.mp h)
  have hh : G.dist (f u) (f (rot u d)) = 2 := by omega
  obtain ⟨z,e,e'⟩ := path_two_here hc hh
  refine ⟨z,?_,e.symm,e'⟩
  intro hz
  obtain ⟨j,hj⟩ := mem_indexSet.mp hz
  obtain ⟨t,ht⟩ := rot_surjective u j
  have htz : f (rot u t) = z := (congrArg f ht).trans hj
  have h1' : G.Adj (f (rot u o)) (f (rot u t)) := by
    rw [h0,htz]; exact e
  have h2' : G.Adj (f (rot u t)) (f (rot u d)) := by
    rw [htz]; exact e'
  have h1 := (cycleAdj_rotate (by omega) u o t).mp ((hcyc _ _).mp h1')
  have h2 := (cycleAdj_rotate (by omega) u t d).mp ((hcyc _ _).mp h2')
  unfold CycleAdj at h1 h2
  change 0+1=t.val ∨ t.val+1=0 ∨ (0=0 ∧ t.val+1=m) ∨ (t.val=0 ∧ 0+1=m) at h1
  omega

private lemma two_same_run_impossible (f : Fin m ↪ V) {u d a : Fin m}
    {k : ℕ} (hdk : k ≤ d.val) (hdk' : d.val + k ≤ m)
    {z : V} (hprof : ∀ i : Fin m, G.Adj z (f (rot a i)) ↔ i.val < k)
    (hzu : G.Adj z (f u)) (hzd : G.Adj z (f (rot u d))) : False := by
  obtain ⟨i,hi⟩ := rot_surjective a u
  have h1 : i.val < k := (hprof i).mp (hi.symm ▸ hzu)
  have h2 : (rot i d).val < k := by
    apply (hprof _).mp
    rw [←rot_assoc,hi]
    exact hzd
  change (i.val+d.val)%m < k at h2
  rw [Nat.mod_eq_of_lt (by omega)] at h2
  omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

lemma short_run_only {f : Fin m ↪ V} (hm : 7 ≤ m)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hcontact : ContactConditions G f) (hcore : NoSmallCore G m)
    {v w : Fin m} (hfar : 2 < G.dist (f v) (f w))
    (H : ExteriorProfiles G f) :
    ∀ z ∉ indexSet f, ShortRun G f z := by
  intro z hz
  rcases H z hz with h | ⟨a,d,h3,hd,hh⟩
  · exact h
  · exact (no_two_pair_profiles hm hcyc hcontact hcore hfar a d h3 hd ⟨z,hz,hh⟩).elim

theorem cycle_length_seven (hc : G.Connected) {f : Fin m ↪ V}
    (hm : 7 ≤ m) (hodd : m % 2 = 1)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    {v w : Fin m} (hunique : ∀ x, 2 < G.dist (f v) x ↔ x = f w)
    (H : ∀ z ∉ indexSet f, ShortRun G f z) : m = 7 := by
  by_contra hne
  have h9 : 9 ≤ m := by omega
  let d1 : Fin m := ⟨4,by omega⟩
  let d2 : Fin m := ⟨m-4,by omega⟩
  have d12 : d1 ≠ d2 := by
    intro e
    have h : 4 = m-4 := congrArg Fin.val e
    omega
  have val_d1 : d1.val = 4 := rfl
  have val_d2 : d2.val = m-4 := rfl
  obtain ⟨d,hl,hu,hn⟩ : ∃ d : Fin m, 4 ≤ d.val ∧ d.val ≤ m-4 ∧ f (rot v d) ≠ f w := by
    by_cases h : f (rot v d1) = f w
    · refine ⟨d2,by omega,by omega,?_⟩
      intro h'
      exact d12 (rot_injective v (f.injective (h.trans h'.symm)))
    · exact ⟨d1,by omega,by omega,h⟩
  have hn' : G.dist (f v) (f (rot v d)) ≤ 2 := by
    by_contra! hh
    exact hn ((hunique _).mp hh)
  obtain ⟨z,hz,hz0,hzd⟩ := external_common_neighbor hc f hcyc (by omega) (by omega) hn'
  obtain ⟨a,k,hk,hh⟩ := H z hz
  exact two_same_run_impossible f (by omega) (by omega) hh hz0 hzd

theorem seven_has_run_four (hc : G.Connected) {f : Fin 7 ↪ V}
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    {v w : Fin 7} (hunique : ∀ x, 2 < G.dist (f v) x ↔ x = f w)
    (H : ∀ z ∉ indexSet f, ShortRun G f z) :
    ∃ a : Fin 7, ∃ z ∉ indexSet f, ∀ i : Fin 7, G.Adj z (f (rot a i)) ↔ i.val ≤ 3 := by
  obtain ⟨d,hl,hu,hn⟩ : ∃ d : Fin 7, 3 ≤ d.val ∧ d.val ≤ 4 ∧ f (rot v d) ≠ f w := by
    by_cases h : f (rot v 3) = f w
    · refine ⟨4,by decide,by decide,?_⟩
      intro he
      exact (by decide : (3 : Fin 7) ≠ 4) (rot_injective v (f.injective (h.trans he.symm)))
    · exact ⟨3,by decide,by decide,h⟩
  have hn' : G.dist (f v) (f (rot v d)) ≤ 2 := by
    by_contra! hh
    exact hn ((hunique _).mp hh)
  obtain ⟨z,hz,hz0,hzd⟩ := external_common_neighbor hc f hcyc hl hu hn'
  obtain ⟨a,k,hk,hh⟩ := H z hz
  rcases hk with rfl | rfl
  · exact (two_same_run_impossible f hl (by omega) hh hz0 hzd).elim
  · exact ⟨a,z,hz,fun i => (hh i).trans (by omega)⟩

#print axioms cycle_length_seven
#print axioms seven_has_run_four
end Graffiti183.Exceptional
