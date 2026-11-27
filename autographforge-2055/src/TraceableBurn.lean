import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Multiset.Sort
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Linarith

namespace TraceableBurn
open SimpleGraph

/-- A covering form of a burning schedule, indexed by increasing ball radius. -/
def Cover {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ x : V, ∃ r : Fin k, G.dist (c r) x ≤ r.val

private theorem dist_forward {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    {n : ℕ} (f : Fin n → V)
    (edge : ∀ (i j : Fin n), i.val+1=j.val → G.Adj (f i) (f j))
    (a b : Fin n) (hab : a ≤ b) : G.dist (f a) (f b) ≤ b.val-a.val := by
  let P := fun q : ℕ => ∀ j : Fin n, j.val=a.val+q → G.dist (f a) (f j) ≤ q
  have main : ∀ q, P q := by
    intro q
    induction q with
    | zero =>
      intro j h
      have eq : j=a := Fin.ext (by omega)
      subst j
      simp
    | succ q ih =>
      intro j h
      have hlt : a.val+q<n := by have jlt := j.isLt; omega
      let i : Fin n := ⟨a.val+q,hlt⟩
      have dij : G.dist (f i) (f j) ≤ 1 := by
        simpa using G.dist_le (Walk.cons (edge i j (by change a.val+q+1=j.val; omega)) Walk.nil)
      exact (hc.dist_triangle (u:=f a) (v:=f i) (w:=f j)).trans (Nat.add_le_add (ih i rfl) dij)
  exact main _ b (by have h : a.val ≤ b.val := hab; omega)

/-- Square-number blocks in a spanning path give a burning cover. -/
theorem cover_of_enumeration {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    {n k : ℕ} (hn : 0<n) (size : n ≤ k^2) (f : Fin n ≃ V)
    (edge : ∀ (i j : Fin n), i.val+1=j.val → G.Adj (f i) (f j)) : Cover G k := by
  let m : Fin k → Fin n := fun i => ⟨min (i.val^2+i.val) (n-1),by omega⟩
  refine ⟨fun i => f (m i),?_⟩
  intro x
  let j := f.symm x
  have jlt := j.isLt
  let s := j.val.sqrt
  have sl : s^2≤j.val := Nat.sqrt_le' _
  have su : j.val<(s+1)^2 := Nat.lt_succ_sqrt' _
  have sk : s<k := Nat.sqrt_lt'.2 (by omega)
  let r : Fin k := ⟨s,sk⟩
  refine ⟨r,?_⟩
  have ex : f j=x := f.apply_symm_apply x
  rw [← ex]
  have lm : (m r).val=min (s^2+s) (n-1) := rfl
  have near₁ : j.val-(m r).val ≤ s := by
    rw [lm]
    simp only [Nat.min_def]
    have sq : (s+1)^2=s^2+2*s+1 := by nlinarith
    rw [sq] at su
    split <;> omega
  have near₂ : (m r).val-j.val ≤ s := by
    have lm' : (m r).val ≤ s^2+s := by rw [lm]; exact min_le_left _ _
    omega
  by_cases h : m r ≤ j
  · exact (dist_forward hc f edge (m r) j h).trans near₁
  · rw [dist_comm]
    exact (dist_forward hc f edge j (m r) (le_of_not_ge h)).trans near₂

theorem path_budget (s : ℕ) : 3*s ≤ (s/2+2)^2 := by
  let q := s/2
  have h : s≤2*q+1 := by dsimp [q]; omega
  change 3*s≤(q+2)^2
  have hq : q^2+1≥2*q := by nlinarith [sq_nonneg ((q : ℤ)-1)]
  nlinarith

theorem cycle_budget (s : ℕ) : 3*s ≤ (s/3+3)^2 := by
  let q := s/3
  have h : s≤3*q+2 := by dsimp [q]; omega
  change 3*s≤(q+3)^2
  by_cases hq : q≤2
  · obtain h0|h1|h2 : q=0 ∨ q=1 ∨ q=2 := by omega
    all_goals simp_all; omega
  · have ht : 3≤q := by omega
    have hp := Nat.mul_le_mul_left q ht
    nlinarith

/-- Slater's degree-sequence lower bound for domination. -/
noncomputable def slater {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  let degrees := (Finset.univ.val.map (fun v => G.degree v)).sort (· ≥ ·)
  sInf {s | Fintype.card V ≤ s+(degrees.take s).sum}

private theorem sum_le_twice_length (xs : List ℕ) (h : ∀ x∈xs, x≤2) :
    xs.sum ≤ 2*xs.length := by
  induction xs with
  | nil => simp
  | cons a l ih =>
      have ha := h a (by simp)
      have hb := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [List.sum_cons,List.length_cons]
      omega

theorem card_le_thrice_slater {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : ∀ v, G.degree v≤2) : Fintype.card V ≤ 3*slater G := by
  classical
  let d := (Finset.univ.val.map (fun v => G.degree v)).sort (· ≥ ·)
  let S : Set ℕ := {s | Fintype.card V ≤ s+(d.take s).sum}
  have non : S.Nonempty := ⟨Fintype.card V,by change Fintype.card V≤Fintype.card V+_; omega⟩
  have hs := Nat.sInf_mem non
  change Fintype.card V ≤ sInf S+(d.take (sInf S)).sum at hs
  have hval : ∀ x∈d.take (sInf S),x≤2 := by
    intro x hx
    have hm : x∈d := List.mem_of_mem_take hx
    dsimp [d] at hm
    rw [Multiset.mem_sort,Multiset.mem_map] at hm
    obtain ⟨v,_,rfl⟩ := hm
    exact hd v
  have hl := sum_le_twice_length _ hval
  have ht : (d.take (sInf S)).length≤sInf S := by rw [List.length_take]; exact min_le_left _ _
  change Fintype.card V ≤ 3*sInf S
  omega

#print axioms card_le_thrice_slater

#print axioms cover_of_enumeration
#print axioms path_budget
#print axioms cycle_budget
end TraceableBurn
