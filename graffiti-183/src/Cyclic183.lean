import Indexed183

namespace Graffiti183.Exceptional
open SimpleGraph Finset

variable {m : ℕ}

def rot (a b : Fin m) : Fin m := ⟨(a.val+b.val)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩

private lemma mod_piece {a : ℕ} (ha : a < m+m) (h : m ≤ a) : a % m = a-m := by
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

lemma rot_injective (a : Fin m) : Function.Injective (rot a) := by
  intro b c he
  have h : (a.val+b.val)%m = (a.val+c.val)%m := congrArg Fin.val he
  apply Fin.ext
  have am := a.isLt
  have bm := b.isLt
  have cm := c.isLt
  by_cases hb : a.val+b.val < m <;> by_cases hc : a.val+c.val < m
  · rw [Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hc] at h
    omega
  · rw [Nat.mod_eq_of_lt hb, mod_piece (by omega) (by omega)] at h
    omega
  · rw [mod_piece (by omega) (by omega),Nat.mod_eq_of_lt hc] at h
    omega
  · rw [mod_piece (by omega) (by omega),mod_piece (by omega) (by omega)] at h
    omega

lemma rot_surjective (a : Fin m) : Function.Surjective (rot a) :=
  Finite.injective_iff_surjective.mp (rot_injective a)

def rotEmb (a : Fin m) : Fin m ↪ Fin m := ⟨rot a,rot_injective a⟩

lemma rot_zero (a : Fin m) (h : 0 < m) : rot a ⟨0,h⟩ = a := by
  apply Fin.ext
  change (a.val+0)%m = a.val
  simpa using Nat.mod_eq_of_lt a.isLt

lemma rot_assoc (a b c : Fin m) : rot (rot a b) c = rot a (rot b c) := by
  apply Fin.ext
  change ((a.val+b.val)%m+c.val)%m = (a.val+(b.val+c.val)%m)%m
  rw [Nat.mod_add_mod,Nat.add_mod_mod,Nat.add_assoc]

def succFin (a : Fin m) : Fin m := ⟨(a.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩

lemma succFin_rotate (a b : Fin m) : succFin (rot a b) = rot a (succFin b) := by
  apply Fin.ext
  change ((a.val+b.val)%m+1)%m = (a.val+(b.val+1)%m)%m
  rw [Nat.mod_add_mod,Nat.add_mod_mod,Nat.add_assoc]

lemma cycleAdj_iff_succ {i j : Fin m} (_hm : 2 ≤ m) :
    CycleAdj i j ↔ succFin i = j ∨ succFin j = i := by
  have H (a b : Fin m) :
      succFin a = b ↔ a.val+1=b.val ∨ (b.val=0 ∧ a.val+1=m) := by
    rw [Fin.ext_iff]
    change (a.val+1)%m = b.val ↔ _
    have h := a.isLt
    by_cases he : a.val+1 < m
    · rw [Nat.mod_eq_of_lt he]
      omega
    · have hh : a.val+1=m := by omega
      rw [hh,Nat.mod_self]
      omega
  rw [H,H]
  unfold CycleAdj
  tauto

lemma cycleAdj_rotate (hm : 2 ≤ m) (a i j : Fin m) :
    CycleAdj (rot a i) (rot a j) ↔ CycleAdj i j := by
  rw [cycleAdj_iff_succ hm,cycleAdj_iff_succ hm,succFin_rotate,succFin_rotate]
  constructor
  · rintro (h|h)
    · exact Or.inl (rot_injective a h)
    · exact Or.inr (rot_injective a h)
  · rintro (h|h)
    · exact Or.inl (congrArg (rot a) h)
    · exact Or.inr (congrArg (rot a) h)

variable {V : Type*}

lemma indexSet_rot (f : Fin m ↪ V) (a : Fin m) : indexSet ((rotEmb a).trans f) = indexSet f := by
  ext x
  simp only [mem_indexSet]
  constructor
  · exact fun ⟨i,h⟩ => ⟨rot a i,h⟩
  · rintro ⟨j,hj⟩
    obtain ⟨i,hi⟩ := rot_surjective a j
    exact ⟨i,(congrArg f hi).trans hj⟩

/-- Cycle index transport preserves the class of pairs far by at least three. -/
lemma separated_index_of_dist {G : SimpleGraph V} (f : Fin m ↪ V)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j) (hm : 5 ≤ m)
    {i j : Fin m} (hd : 2 < G.dist (f i) (f j)) :
    ∃ d : Fin m, 3 ≤ d.val ∧ d.val ≤ m-3 ∧ rot i d = j := by
  obtain ⟨d,hr⟩ := rot_surjective i j
  have hm0 : 0 < m := by omega
  let z : Fin m := ⟨0,hm0⟩
  have hi : rot i z = i := rot_zero i hm0
  have far : 2 < G.dist ((rotEmb i).trans f z) ((rotEmb i).trans f d) := by
    change 2 < G.dist (f (rot i z)) (f (rot i d))
    rwa [hi,hr]
  let F := (rotEmb i).trans f
  change 2 < G.dist (F z) (F d) at far
  have adjF (a b : Fin m) : G.Adj (F a) (F b) ↔ CycleAdj a b :=
    (hcyc _ _).trans (cycleAdj_rotate (by omega) i a b)
  have had (a b : Fin m) (e : CycleAdj a b) : G.dist (F a) (F b) ≤ 1 := by
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((adjF a b).mpr e)]
  have two (a b c : Fin m) (e : CycleAdj a b) (e' : CycleAdj b c) :
      G.dist (F a) (F c) ≤ 2 :=
    G.dist_le (SimpleGraph.Walk.cons ((adjF a b).mpr e) ((adjF b c).mpr e').toWalk)
  have hd0 : d.val ≠ 0 := by
    intro e
    have hh : d = z := Fin.ext e
    subst d
    rw [SimpleGraph.dist_self] at far
    omega
  have hd1 : d.val ≠ 1 := by
    intro e
    have := had z d (Or.inl e.symm)
    exact (by omega : False)
  have hd2 : d.val ≠ 2 := by
    intro e
    let a : Fin m := ⟨1,by omega⟩
    have := two z a d (Or.inl rfl) (Or.inl e.symm)
    exact (by omega : False)
  have hn1 : d.val + 1 ≠ m := by
    intro e
    have := had z d (Or.inr (Or.inr (Or.inl ⟨rfl,e⟩)))
    exact (by omega : False)
  have hn2 : d.val + 2 ≠ m := by
    intro e
    let a : Fin m := ⟨m-1,by omega⟩
    have e1 : CycleAdj z a := Or.inr (Or.inr (Or.inl ⟨rfl,by change m-1+1=m; omega⟩))
    have e2 : CycleAdj a d := Or.inr (Or.inl (by change d.val+1=m-1; omega))
    have := two z a d e1 e2
    exact (by omega : False)
  have := d.isLt
  exact ⟨d,by omega,by omega,hr⟩

#print axioms separated_index_of_dist
end Graffiti183.Exceptional
