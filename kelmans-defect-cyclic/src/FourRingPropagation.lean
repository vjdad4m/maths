import FourRingHostCuts

open Finset
namespace KelmansCactus.FourRingPropagation

/-- The ring index has no fixed point, and cutting at any one
index leaves a chain along which values propagate. -/
structure Circular {J : Type*} (next : Equiv.Perm J) : Prop where
  fixed : ∀i,next i≠i
  afterRemoval : ∀ (z : J) (f : J→Bool),
    (∀ i,i≠z→next i≠z→f i=f (next i)) →
    ∀ a b,a≠z→b≠z→f a=f b

def spin (n : ℕ) [NeZero n] : Equiv.Perm (Fin n) where
  toFun := fun x=>x+1
  invFun := fun x=>x-1
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private theorem spin_fixed {n : ℕ} [NeZero n] (n2 : 2≤n) (i : Fin n) :
    spin n i≠i := by
  intro e
  have g : i+1=i+0 := by simpa only [add_zero] using e
  have b : (1:Fin n)=0 := add_left_cancel g
  have v : (1:Fin n).val=0 := congrArg Fin.val b
  change 1%n=0 at v
  rw [Nat.mod_eq_of_lt (by omega : 1<n)] at v
  contradiction

private theorem cast_step (n m : ℕ) [NeZero n] :
    ((m+1 : ℕ):Fin n)=(m:Fin n)+1 := by
  apply Fin.ext
  change (m+1)%n=(m%n+1%n)%n
  exact Nat.add_mod _ _ _

private theorem nonzero_shift {n m : ℕ} [NeZero n] (m1 : 1≤m) (mn : m<n) (z : Fin n) :
    z+(m:Fin n)≠z := by
  intro e
  have g : z+(m:Fin n)=z+0 := by simpa only [add_zero] using e
  have b : (m:Fin n)=0 := add_left_cancel g
  have v : (m:Fin n).val=0 := congrArg Fin.val b
  rw [Fin.val_cast_of_lt mn] at v
  omega

theorem spin_circular {n : ℕ} [NeZero n] (n2 : 2≤n) : Circular (spin n) := by
  refine ⟨spin_fixed n2,?_⟩
  intro z f rule a b az bz
  have follows (m : ℕ) (m1 : 1≤m) (mn : m<n) : f (z+(m:Fin n))=f (z+1) := by
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases m0 : m=0
      · subst m
        rfl
      have ml : 1≤m := by omega
      have eq : spin n (z+(m:Fin n))=z+((m+1:ℕ):Fin n) := by
        change z+(m:Fin n)+1=z+((m+1:ℕ):Fin n)
        rw [cast_step,add_assoc]
      have prior := rule (z+(m:Fin n)) (nonzero_shift ml (by omega) z)
        (by rw [eq]; exact nonzero_shift m1 mn z)
      rw [eq] at prior
      exact prior.symm.trans (ih ml (by omega))
  have any (x : Fin n) (xz : x≠z) : f x=f (z+1) := by
    let y := x-z
    have e : z+y=x := by
      change z+(x-z)=x
      rw [add_comm,sub_add_cancel]
    have nz : y.val≠0 := by
      intro h
      have eq : y=0 := Fin.ext h
      exact xz (by simpa [eq] using e.symm)
    have u := follows y.val (by omega) (y.isLt)
    simpa only [Fin.cast_val_eq_self,e] using u
  exact (any a az).trans (any b bz).symm

/-- If at most one link could change a color, that link cannot
change it either, on a true cyclic ring. -/
theorem all_equal_of_one_break {J : Type*} (next : Equiv.Perm J)
    (ring : Circular next) (f : J→Bool)
    (atMostOne : ∀ i j,f i≠f (next i) → f j≠f (next j) → i=j) :
    ∀ a b,f a=f b := by
  classical
  have none (i : J) : f i=f (next i) := by
    by_contra bad
    have same (j : J) (jNot : j≠i) : f j=f (next j) :=
      Classical.not_not.mp (fun diff=>jNot (atMostOne _ _ diff bad))
    have other : next.symm i≠i := by
      intro e
      exact ring.fixed i (by
        have q := congrArg next e
        simpa using q.symm)
    have ab := ring.afterRemoval i f (fun j jn _=>same j jn)
      (next.symm i) (next i) other (ring.fixed i)
    have left := same (next.symm i) other
    rw [next.apply_symm_apply] at left
    exact bad (left.symm.trans ab)
  intro a b
  by_cases ab : a=b
  · rw [ab]
  · have e := ring.afterRemoval a f (fun i _ _=>none i) (next a) b (ring.fixed a) (Ne.symm ab)
    exact (none a).trans e

#print axioms spin_circular
#print axioms all_equal_of_one_break
end KelmansCactus.FourRingPropagation
