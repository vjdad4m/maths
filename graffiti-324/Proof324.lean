import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Dedup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Written on the Wall II, conjecture 324

A bound on the largest complement edge neighborhood in terms of the
Havel–Hakimi residue implies that the graph is well total dominated.

The proof writes the Havel–Hakimi algorithm in complementary degrees.
For final residue r ≥ 3, the hypothesis bounds initial degrees by r.
The elimination run has a nonincreasing count of entries at least r−1
and a nondecreasing total cost: a degree-r entry costs r−2, and all other
entries cost their degree. Thus there are at least r high entries and
the initial cost is at most r(r−1). Combined with the neighborhood bound,
this forces every complement component to have a vertex universal in
that component. Every total dominating set therefore meets two
complement components and contains a total dominating pair.

The complement reformulation and earlier partial results are credited to
Claude Opus 5 at AI Village (graffiti-verification, section 7fn).
Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti324
open Finset SimpleGraph
open scoped BigOperators

private def hhTail (d : ℕ) (xs : List ℕ) : List ℕ :=
  (xs.take d).map Nat.pred ++ xs.drop d

private def descending (xs : List ℕ) : List ℕ := xs.mergeSort (fun a b => decide (b ≤ a))

private def residueAux : ℕ → List ℕ → ℕ
  | 0, xs => xs.length
  | fuel+1, xs => match descending xs with
    | [] => 0
    | d :: tail => if d = 0 then tail.length + 1 else residueAux fuel (hhTail d tail)

/-- Re-sort in descending order, delete the maximum, and subtract one
from the next that many degrees, until the list is all zero. -/
def residueSequence (xs : List ℕ) : ℕ := residueAux xs.length xs

private def HKStep (xs ys : List ℕ) : Prop :=
  ∃ d p q, xs.Perm (d :: (p ++ q)) ∧
    (d :: (p ++ q)).Pairwise (fun a b => b ≤ a) ∧
    0 < d ∧ p.length = d ∧ ys = p.map Nat.pred ++ q

private inductive HKRun : List ℕ → ℕ → Prop
  | done (r : ℕ) : HKRun (List.replicate r 0) r
  | step {xs ys r} : HKStep xs ys → HKRun ys r → HKRun xs r

private theorem descending_perm (xs : List ℕ) : (descending xs).Perm xs :=
  List.mergeSort_perm _ _

private theorem descending_sorted (xs : List ℕ) :
    (descending xs).Pairwise (fun a b => b ≤ a) := by
  unfold descending
  have hs := List.sorted_mergeSort (le := fun a b : ℕ => decide (b ≤ a))
    (fun a b c hab hbc => by simpa using (of_decide_eq_true hbc).trans (of_decide_eq_true hab))
    (fun a b => by simp [le_total]) xs
  exact hs.imp (fun h => of_decide_eq_true h)

private theorem hhTail_length (d : ℕ) (xs : List ℕ) : (hhTail d xs).length = xs.length := by
  simp [hhTail]
  omega

private theorem run_aux (f : ℕ) (xs : List ℕ) (hf : xs.length ≤ f)
    (hb : ∀ x ∈ xs, x < xs.length) : HKRun xs (residueAux f xs) := by
  induction f generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    exact HKRun.done 0
  | succ f ih =>
    have hp := descending_perm xs
    have hs := descending_sorted xs
    cases hd : descending xs with
    | nil =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (by rw [hd] at hp; simpa using hp.length_eq.symm)
      subst xs
      simp only [residueAux, hd]
      exact HKRun.done 0
    | cons d tail =>
      rw [hd] at hp hs
      have hlen : xs.length = tail.length+1 := by simpa using hp.length_eq.symm
      have hd₀ : d ≤ tail.length := by
        have hh := hb d (hp.mem_iff.mp (List.mem_cons_self ..))
        omega
      rw [residueAux, hd]
      change HKRun xs (if d = 0 then tail.length + 1 else residueAux f (hhTail d tail))
      by_cases hz : d = 0
      · rw [if_pos hz]
        have hzTail (x : ℕ) (hx : x ∈ tail) : x = 0 :=
          Nat.eq_zero_of_le_zero ((List.pairwise_cons.mp hs).1 x hx |>.trans_eq hz)
        have hzXs (x : ℕ) (hx : x ∈ xs) : x = 0 := by
          rcases List.mem_cons.mp (hp.mem_iff.mpr hx) with h | h
          · exact h.trans hz
          · exact hzTail x h
        have hx := List.eq_replicate_of_mem hzXs
        rw [hx, hlen]
        exact HKRun.done _
      · rw [if_neg hz]
        let p := tail.take d
        let q := tail.drop d
        have hpq : p ++ q = tail := List.take_append_drop ..
        have hdlen : p.length = d := by simp [p,Nat.min_eq_left hd₀]
        have hsmall (x : ℕ) (hx : x ∈ hhTail d tail) : x < (hhTail d tail).length := by
          rw [hhTail_length]
          have hmax (x : ℕ) (h : x ∈ tail) : x ≤ d := (List.pairwise_cons.mp hs).1 x h
          change x ∈ p.map Nat.pred ++ q at hx
          rcases List.mem_append.mp hx with h | h
          · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp h
            have h := hmax y (List.mem_of_mem_take hy)
            simp only [Nat.pred_eq_sub_one]
            omega
          · have hxd := hmax x (List.mem_of_mem_drop h)
            have hne : d ≠ tail.length := by
              intro hh
              have hq₀ : q = [] := by simp [q,hh]
              simp [hq₀] at h
            omega
        refine HKRun.step ⟨d,p,q,by rw [hpq]; exact hp.symm,
          by rw [hpq]; exact hs,by omega,hdlen,rfl⟩ ?_
        exact ih (hhTail d tail) (by rw [hhTail_length]; omega) hsmall

/-- Degree list expressed on the same vertices, for the complementary graph. -/
private def dual (xs : List ℕ) : List ℕ := xs.map (fun d => xs.length - 1 - d)

private def CompStep (xs ys : List ℕ) : Prop :=
  ∃ h p q, xs.Perm (h :: (p ++ q)) ∧
    (∀ x ∈ p ++ q, h ≤ x) ∧ (∀ a ∈ p, ∀ b ∈ q, a ≤ b) ∧
    q.length = h ∧ ys = p.map (fun d => min d (xs.length-2)) ++ q.map Nat.pred

private inductive CompRun : List ℕ → ℕ → Prop
  | done (r : ℕ) : CompRun (List.replicate r (r-1)) r
  | step {xs ys r} : CompStep xs ys → CompRun ys r → CompRun xs r

private theorem dual_step {xs ys : List ℕ} (h : HKStep xs ys) (hb : ∀ x ∈ xs, x < xs.length) :
    CompStep (dual xs) (dual ys) := by
  obtain ⟨d,p,q,hperm,horder,_,hlen,rfl⟩ := h
  let n := xs.length
  let f := fun x : ℕ => n-1-x
  have hN : n = 1+p.length+q.length := by
    have := hperm.length_eq
    simp only [List.length_cons,List.length_append] at this
    exact this.trans (by omega)
  have ha : (p.map Nat.pred ++ q).length = n-1 := by simp; omega
  have hd := (List.pairwise_cons.mp horder).1
  have hPQ := (List.pairwise_append.mp (List.pairwise_cons.mp horder).2).2.2
  refine ⟨f d,p.map f,q.map f,?_,?_,?_,?_,?_⟩
  · simpa [dual,f,n,List.map_cons,List.map_append] using hperm.map f
  · intro x hx
    rw [← List.map_append] at hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact Nat.sub_le_sub_left (hd y hy) _
  · intro a ha b hb
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    exact Nat.sub_le_sub_left (hPQ x hx y hy) _
  · simp [f]
    omega
  · simp only [dual, List.map_append,List.map_map,ha,List.length_map]
    congr 1
    · apply List.map_congr_left
      intro x hx
      have ht := hd x (List.mem_append_left _ hx)
      have hd' := hb d (hperm.mem_iff.mpr (List.mem_cons_self ..))
      simp only [Function.comp_apply, f, Nat.pred_eq_sub_one]
      dsimp [n] at *
      omega
    · apply List.map_congr_left
      intro x hx
      simp only [Function.comp_apply,f,Nat.pred_eq_sub_one]
      dsimp [n]
      omega

private theorem dual_run {xs : List ℕ} {r : ℕ} (h : HKRun xs r)
    (hb : ∀ x ∈ xs, x < xs.length) : CompRun (dual xs) r := by
  induction h with
  | done r =>
    simpa [dual] using CompRun.done r
  | @step xs ys r hs hr ih =>
    refine CompRun.step (dual_step hs hb) (ih ?_)
    obtain ⟨d,p,q,hperm,hord,hd,hlen,rfl⟩ := hs
    have hN := hperm.length_eq
    simp only [List.length_cons,List.length_append] at hN
    have hd' := hb d (hperm.mem_iff.mpr (List.mem_cons_self ..))
    intro x hx
    simp only [List.length_append,List.length_map]
    have hmax (x : ℕ) (hx : x ∈ p ++ q) : x ≤ d := (List.pairwise_cons.mp hord).1 x hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp h
      have ht := hmax y (List.mem_append_left _ hy)
      simp only [Nat.pred_eq_sub_one]
      omega
    · have ht := hmax x (List.mem_append_right _ h)
      have hp : 0 < q.length := List.length_pos_of_mem h
      omega

#print axioms dual_run


private theorem comp_step_length {xs ys : List ℕ} (h : CompStep xs ys) :
    ys.length + 1 = xs.length := by
  obtain ⟨d,p,q,hperm,_,_,_,rfl⟩ := h
  have hl := hperm.length_eq
  simp only [List.length_cons,List.length_append,List.length_map] at hl ⊢
  omega

private theorem comp_run_length {xs : List ℕ} {r : ℕ} (h : CompRun xs r) :
    r ≤ xs.length := by
  induction h with
  | done => simp
  | step h _ ih => have hs := comp_step_length h; omega

private theorem after_bounded {xs ys : List ℕ} {b : ℕ} (h : CompStep xs ys)
    (hb : ∀ x ∈ xs, x ≤ b) : ∀ x ∈ ys, x ≤ b := by
  obtain ⟨d,p,q,hperm,_,_,_,rfl⟩ := h
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    have := hb a (hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_append_left _ ha)))
    omega
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    have := hb a (hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_append_right _ ha)))
    exact (Nat.pred_le _).trans this

private theorem terminal_bounded {xs : List ℕ} {r b : ℕ} (h : CompRun xs r) (hr : 0 < r)
    (hb : ∀ x ∈ xs, x ≤ b) : r-1 ≤ b := by
  induction h with
  | done r => exact hb _ (by simp [Nat.ne_of_gt hr])
  | step hs _ ih => exact ih hr (after_bounded hs hb)

private theorem selected_ge_two {xs ys p q : List ℕ} {r h : ℕ}
    (hr : 3 ≤ r) (hp : xs.Perm (h :: (p ++ q)))
    (hmin : ∀ d ∈ p ++ q, h ≤ d) (htop : ∀ a ∈ p, ∀ b ∈ q, a ≤ b)
    (hlen : q.length = h) (he : ys = p.map (fun d => min d (xs.length-2)) ++ q.map Nat.pred)
    (hout : CompRun ys r) (x : ℕ) (hx : x ∈ q) : 2 ≤ x := by
  by_contra! hl
  have hpq := hmin x (List.mem_append_right _ hx)
  have hql := List.length_pos_of_mem hx
  have h₁ : q.length = 1 := by omega
  obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp h₁
  have ha' : a = x := by simpa [ha,eq_comm] using hx
  subst a
  have hle (d : ℕ) (hd : d ∈ xs) : d ≤ 1 := by
    rcases List.mem_cons.mp (hp.mem_iff.mp hd) with rfl | hd
    · omega
    rcases List.mem_append.mp hd with hd | hd
    · exact (htop d hd x hx).trans (by omega)
    · have hd' : d = x := by simpa [ha] using hd
      omega
  have hs : CompStep xs ys := ⟨h,p,q,hp,hmin,htop,hlen,he⟩
  have ht := terminal_bounded hout (by omega : 0 < r) (after_bounded hs hle)
  omega

private def positive (xs : List ℕ) : List ℕ := xs.filter (fun n => decide (0<n))

/-- Once the largest entry drops below the target residue, only zeros
can still be removed. -/
private theorem small_run {xs : List ℕ} {r : ℕ} (h : CompRun xs r) (hr : 3 ≤ r)
    (hb : ∀ d ∈ xs, d ≤ r-1) :
    (positive xs).Perm (List.replicate r (r-1)) := by
  induction h with
  | done r => simp [positive,show 0 < r-1 by omega]
  | @step xs ys r hs ht ih =>
    have hb' := after_bounded hs hb
    have hsmall := ih hr hb'
    obtain ⟨d,p,q,hperm,hmin,htop,hlen,he⟩ := hs
    have hLength := comp_step_length (show CompStep xs ys from ⟨d,p,q,hperm,hmin,htop,hlen,he⟩)
    have hnr := comp_run_length ht
    have hCap : r-1 ≤ xs.length-2 := by omega
    by_cases hz : d=0
    · have hq : q=[] := List.length_eq_zero_iff.mp (by omega)
      have hp (x : ℕ) (hx : x ∈ p) : min x (xs.length-2) = x :=
        min_eq_left ((hb _ (hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))).trans hCap)
      have he' : ys = p := by
        rw [he,hq]
        simp only [List.map_nil,List.append_nil]
        calc
          _ = p.map id := List.map_congr_left (fun x hx => hp x hx)
          _ = p := List.map_id _
      rw [he'] at hsmall
      have hh : (positive xs).Perm (positive (d :: (p ++ q))) := hperm.filter _
      have heq : positive (d :: (p ++ q)) = positive p := by simp [positive,hz,hq]
      rw [heq] at hh
      exact hh.trans hsmall
    · have hqn : q ≠ [] := fun he => hz (by simpa [he] using hlen.symm)
      obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil q hqn
      have hx₂ := selected_ge_two hr hperm hmin htop hlen he ht x hx
      have hxm := hb x (hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_append_right _ hx)))
      have hy : x.pred ∈ ys := by
        rw [he]
        exact List.mem_append_right _ (List.mem_map_of_mem hx)
      have hym : x.pred ∈ positive ys := by
        simp only [positive,List.mem_filter,decide_eq_true_eq]
        exact ⟨hy,by simp [Nat.pred_eq_sub_one]; omega⟩
      have hex := List.eq_of_mem_replicate (hsmall.mem_iff.mp hym)
      simp only [Nat.pred_eq_sub_one] at hex
      omega

private def mass (f : ℕ → ℕ) (xs : List ℕ) : ℕ := (xs.map f).sum

private theorem mass_mono (xs : List ℕ) (f g : ℕ → ℕ)
    (h : ∀ a ∈ xs, f a ≤ g a) : mass f xs ≤ mass g xs := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := h a (List.mem_cons_self ..)
    have hb := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [mass,List.map_cons,List.sum_cons] at hb ⊢
    omega

private theorem mass_eq_add (xs : List ℕ) (f g : ℕ → ℕ) (k : ℕ)
    (h : ∀ a ∈ xs, f a = g a+k) : mass f xs = mass g xs + xs.length*k := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := h a (List.mem_cons_self ..)
    have hb := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [mass,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul] at hb ⊢
    omega

private def high (r d : ℕ) : ℕ := if r-1 ≤ d then 1 else 0

private def cost (r d : ℕ) : ℕ := if d=r then r-2 else d

private theorem comp_run_invariants {xs : List ℕ} {r : ℕ} (h : CompRun xs r) (hr : 3 ≤ r)
    (hb : ∀ d ∈ xs, d ≤ r) :
    r ≤ mass (high r) xs ∧ mass (cost r) xs ≤ r*(r-1) := by
  induction h with
  | done r =>
    have hne : r-1 ≠ r := by omega
    simp [mass,high,cost,hne,Nat.mul_comm]
  | @step xs ys r hs ht ih =>
    have inv := ih hr (after_bounded hs hb)
    have hl := comp_step_length hs
    have hnr := comp_run_length ht
    obtain ⟨d,p,q,hperm,hmin,htop,hlen,he⟩ := hs
    have hCap : r-1 ≤ xs.length-2 := by omega
    have hp (x : ℕ) (hx : x ∈ p) : x ≤ r :=
      hb x (hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
    have hq (x : ℕ) (hx : x ∈ q) : x ≤ r :=
      hb x (hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_append_right _ hx)))
    have q_eq (x : ℕ) (hx : x ∈ q) : x = r := by
      by_cases hn : x = r
      · exact hn
      have hlt : x < r := lt_of_le_of_ne (hq x hx) hn
      exfalso
      have hs' (a : ℕ) (ha : a ∈ ys) : a ≤ r-1 := by
        rw [he] at ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
          have h := htop b hb x hx
          exact (min_le_left _ _).trans (h.trans (by omega))
        · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
          have h := hq b hb
          simp only [Nat.pred_eq_sub_one]
          omega
      have hs := small_run ht hr hs'
      have hx₂ := selected_ge_two hr hperm hmin htop hlen he ht x hx
      have hy : x.pred ∈ ys := by
        rw [he]
        exact List.mem_append_right _ (List.mem_map_of_mem hx)
      have hym : x.pred ∈ positive ys := by
        simp only [positive,List.mem_filter,decide_eq_true_eq]
        exact ⟨hy,by simp [Nat.pred_eq_sub_one]; omega⟩
      have hEq := List.eq_of_mem_replicate (hs.mem_iff.mp hym)
      simp only [Nat.pred_eq_sub_one] at hEq
      omega
    have hpH := mass_mono p (fun a => high r (min a (xs.length-2))) (high r) (by
      intro a _
      change high r (min a (xs.length-2)) ≤ high r a
      unfold high
      split <;> split <;> omega)
    have hqH := mass_mono q (fun a => high r a.pred) (high r) (by
      intro a _
      change high r a.pred ≤ high r a
      unfold high
      simp only [Nat.pred_eq_sub_one]
      split <;> split <;> omega)
    have hpW := mass_mono p (cost r) (fun a => cost r (min a (xs.length-2))) (by
      intro a ha
      have ha' := hp a ha
      change cost r a ≤ cost r (min a (xs.length-2))
      unfold cost
      split <;> split <;> omega)
    have hqW := mass_eq_add q (fun a => cost r a.pred) (cost r) 1 (by
      intro a ha
      rw [q_eq a ha]
      have hn : r-1 ≠ r := by omega
      simp [cost,Nat.pred_eq_sub_one,hn]
      omega)
    have hdW : cost r d ≤ d := by unfold cost; split <;> omega
    have hh' := (hperm.map (high r)).sum_eq
    have hw' := (hperm.map (cost r)).sum_eq
    simp only [List.map_cons,List.map_append,List.sum_cons,List.sum_append] at hh' hw'
    have hi₁ : r ≤ mass (fun a => high r (min a (xs.length-2))) p +
        mass (fun a => high r a.pred) q := by
      simpa only [he,mass,List.map_append,List.sum_append,List.map_map] using inv.1
    have hi₂ : mass (fun a => cost r (min a (xs.length-2))) p +
        mass (fun a => cost r a.pred) q ≤ r*(r-1) := by
      simpa only [he,mass,List.map_append,List.sum_append,List.map_map] using inv.2
    simp only [mass,Function.comp_apply] at hpH hqH hpW hqW hi₁ hi₂ ⊢
    simp only [Nat.mul_one] at hqW
    omega

#print axioms comp_run_invariants


noncomputable section

section Edges
variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj

def edgeNeighborhood (H : SimpleGraph V) (u v : V) : Finset V :=
  H.neighborFinset u ∪ H.neighborFinset v

def maxEdgeNeighborhood (H : SimpleGraph V) : ℕ :=
  univ.sup (fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card)

theorem edgeNeighborhood_le_max (H : SimpleGraph V) {u v : V} (h : H.Adj u v) :
    (edgeNeighborhood H u v).card ≤ maxEdgeNeighborhood H :=
  (le_sup (f := fun v => (edgeNeighborhood H u v).card) (mem_filter.mpr ⟨mem_univ _,h⟩)).trans
    (le_sup (f := fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card) (mem_univ u))

private theorem edgeNeighborhood_spec {H : SimpleGraph V} {u v w : V} :
    w ∈ edgeNeighborhood H u v ↔ H.Adj u w ∨ H.Adj v w := by
  simp [edgeNeighborhood]

private theorem at_least_two {H : SimpleGraph V} {u v : V} (h : H.Adj u v) :
    2 ≤ maxEdgeNeighborhood H := by
  have hS : ({u,v} : Finset V) ⊆ edgeNeighborhood H u v := by
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact edgeNeighborhood_spec.mpr (Or.inr h.symm)
    · exact edgeNeighborhood_spec.mpr (Or.inl h)
  have hcard := (card_le_card hS).trans (edgeNeighborhood_le_max H h)
  simpa [h.ne] using hcard

theorem max_attained (H : SimpleGraph V) (he : ∃ u v, H.Adj u v) :
    ∃ u v, H.Adj u v ∧ (edgeNeighborhood H u v).card = maxEdgeNeighborhood H := by
  obtain ⟨a,b,hab⟩ := he
  haveI : Nonempty V := ⟨a⟩
  have hpos := at_least_two hab
  obtain ⟨u,_,hu⟩ := exists_mem_eq_sup (univ : Finset V) univ_nonempty
    (fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card)
  change maxEdgeNeighborhood H = _ at hu
  have hun : (univ.filter (H.Adj u)).Nonempty := by
    by_contra! hn
    rw [not_nonempty_iff_eq_empty.mp hn, Finset.sup_empty] at hu
    change maxEdgeNeighborhood H = 0 at hu
    omega
  obtain ⟨v,hv,hd⟩ := exists_mem_eq_sup (univ.filter (H.Adj u)) hun
    (fun v => (edgeNeighborhood H u v).card)
  exact ⟨u,v,(mem_filter.mp hv).2,(hu.trans hd).symm⟩

theorem empty_edge_max (H : SimpleGraph V) (he : ¬ ∃ u v, H.Adj u v) :
    maxEdgeNeighborhood H = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le_iff.mpr
  intro u _
  apply Finset.sup_le_iff.mpr
  intro v hv
  exact (he ⟨u,v,(mem_filter.mp hv).2⟩).elim



end Edges

section Domination
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance : DecidableEq V := Classical.decEq V

def TotalDominates (D : Finset V) : Prop := ∀ v, ∃ w ∈ D, G.Adj v w

def WellTotalDominated : Prop :=
  ∀ D, TotalDominates G D → (∀ E, E ⊂ D → ¬TotalDominates G E) →
    ∀ E, TotalDominates G E → D.card ≤ E.card

omit [Fintype V] in
private theorem dominates_two {D : Finset V} (hD : TotalDominates G D) (v : V) :
    ∃ a ∈ D, ∃ b ∈ D, G.Adj a b := by
  obtain ⟨a,ha,_⟩ := hD v
  obtain ⟨b,hb,hab⟩ := hD a
  exact ⟨a,ha,b,hb,hab⟩

omit [Fintype V] in
private theorem wtd_of_pairs (v : V)
    (hpair : ∀ D, TotalDominates G D →
      ∃ a b, G.Adj a b ∧ ({a,b} : Finset V) ⊆ D ∧ TotalDominates G {a,b}) :
    WellTotalDominated G := by
  intro D hD hmin E hE
  obtain ⟨a,b,hab,hsub,hdom⟩ := hpair D hD
  obtain ⟨x,hx,y,hy,hxy⟩ := dominates_two G hE v
  have he : D = {a,b} := by
    by_contra hne
    exact hmin _ (ssubset_of_subset_of_ne hsub (Ne.symm hne)) hdom
  have hle : ({x,y} : Finset V).card ≤ E.card := card_le_card (insert_subset hx (singleton_subset_iff.mpr hy))
  simpa [he,hab.ne,hxy.ne] using hle


end Domination

section Graph
variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj

def degreeList (H : SimpleGraph V) : List ℕ := (univ : Finset V).toList.map (fun v => H.degree v)

def residue (H : SimpleGraph V) : ℕ := residueSequence (degreeList H)

private theorem degreeList_length (H : SimpleGraph V) :
    (degreeList H).length = Fintype.card V := by simp [degreeList]

private theorem degreeList_mass (H : SimpleGraph V) (f : ℕ → ℕ) :
    mass f (degreeList H) = ∑ v, f (H.degree v) := by
  unfold mass degreeList
  rw [List.map_map, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

private theorem degreeList_bounded (H : SimpleGraph V) :
    ∀ x ∈ degreeList H, x < (degreeList H).length := by
  intro x hx
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
  rw [degreeList_length]
  exact H.degree_lt_card_verts v

private theorem degreeList_dual (G : SimpleGraph V) :
    dual (degreeList G) = degreeList Gᶜ := by
  unfold dual
  rw [degreeList_length]
  unfold degreeList
  rw [List.map_map]
  apply List.map_congr_left
  intro v _
  have e := G.degree_compl (v := v)
  change Fintype.card V - 1 - G.degree v = _
  convert e.symm using 2

private theorem complement_run (G : SimpleGraph V) :
    CompRun (degreeList Gᶜ) (residue G) := by
  rw [← degreeList_dual]
  exact dual_run (run_aux _ _ le_rfl (degreeList_bounded G)) (degreeList_bounded G)

private def closedNeighborhood (H : SimpleGraph V) (v : V) : Finset V :=
  insert v (H.neighborFinset v)

private theorem closed_card (H : SimpleGraph V) (v : V) :
    (closedNeighborhood H v).card = H.degree v + 1 := by
  unfold closedNeighborhood
  rw [card_insert_of_not_mem (by simp),card_neighborFinset_eq_degree]

private def Closed (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∉ S, ¬H.Adj x y

private def UniversalIn (H : SimpleGraph V) (S : Finset V) (x : V) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, y ≠ x → H.Adj x y

private theorem root_universal (H : SimpleGraph V) (x : V) :
    UniversalIn H (closedNeighborhood H x) x := by
  refine ⟨mem_insert_self _ _,?_⟩
  intro y hy hne
  exact (H.mem_neighborFinset _ _).mp ((mem_insert.mp hy).resolve_left hne)

private theorem closed_neigh_le {H : SimpleGraph V} {x y : V} (hy : H.Adj x y) :
    closedNeighborhood H x ⊆ edgeNeighborhood H x y := by
  intro w hw
  rcases mem_insert.mp hw with rfl | hw
  · exact edgeNeighborhood_spec.mpr (Or.inr hy.symm)
  · exact edgeNeighborhood_spec.mpr (Or.inl ((H.mem_neighborFinset _ _).mp hw))

private theorem degree_bound (H : SimpleGraph V) (r : ℕ)
    (hm : maxEdgeNeighborhood H ≤ 1+r) (x : V) : H.degree x ≤ r := by
  by_cases hx : H.degree x = 0
  · omega
  obtain ⟨y,hy⟩ := (H.degree_pos_iff_exists_adj x).mp (by omega)
  have hl := (card_le_card (closed_neigh_le hy)).trans ((edgeNeighborhood_le_max H hy).trans hm)
  rw [closed_card] at hl
  omega

private theorem neighborhood_closed (H : SimpleGraph V) (x : V)
    (h : maxEdgeNeighborhood H ≤ H.degree x + 1) : Closed H (closedNeighborhood H x) := by
  intro a ha b hb hab
  rcases mem_insert.mp ha with rfl | ha
  · exact hb (mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr hab))
  · have hx := (H.mem_neighborFinset _ _).mp ha
    have heq : closedNeighborhood H x = edgeNeighborhood H x a :=
      eq_of_subset_of_card_le (closed_neigh_le hx) (by
        rw [closed_card]
        exact (edgeNeighborhood_le_max H hx).trans h)
    exact hb (heq.symm ▸ edgeNeighborhood_spec.mpr (Or.inr hab))

private def HasBlocks (H : SimpleGraph V) : Prop :=
  ∀ x, ∃ S : Finset V, x ∈ S ∧ Closed H S ∧ ∃ v, UniversalIn H S v

omit [Fintype V] in
private theorem wtd_of_blocks (H : SimpleGraph V) [Nonempty V] (hb : HasBlocks H) :
    WellTotalDominated Hᶜ := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  apply wtd_of_pairs Hᶜ v
  intro D hd
  obtain ⟨x,hx,_⟩ := hd v
  obtain ⟨S,hxs,hclosed,u,hu,hall⟩ := hb x
  obtain ⟨y,hy,huy⟩ := hd u
  have hyn : y ∉ S := fun hyS => huy.2 (hall y hyS huy.ne.symm)
  have hxy : Hᶜ.Adj x y := ⟨fun e => hyn (e ▸ hxs),hclosed x hxs y hyn⟩
  refine ⟨x,y,hxy,insert_subset hx (singleton_subset_iff.mpr hy),?_⟩
  intro z
  by_cases hz : z ∈ S
  · exact ⟨y,by simp,⟨fun e => hyn (e ▸ hz),hclosed z hz y hyn⟩⟩
  · exact ⟨x,by simp,⟨fun e => hz (e.symm ▸ hxs),fun h => hclosed x hxs z hz h.symm⟩⟩

private theorem singleton_block (H : SimpleGraph V) (x : V) (hd : H.degree x = 0) :
    Closed H {x} ∧ UniversalIn H {x} x := by
  refine ⟨?_,by
    refine ⟨by simp,?_⟩
    intro y hy hn
    exact (hn (mem_singleton.mp hy)).elim⟩
  intro a ha b _ hab
  rw [mem_singleton.mp ha] at hab
  have ht := (H.degree_pos_iff_exists_adj x).mpr ⟨b,hab⟩
  omega

private theorem two_or_fewer_outside (H : SimpleGraph V) {S : Finset V} {u : V}
    (hs : Closed H S) (hu : UniversalIn H S u)
    (hc : (((univ : Finset V) \ S).filter (fun w => 0 < H.degree w)).card ≤ 2) :
    HasBlocks H := by
  classical
  intro x
  by_cases hx : x ∈ S
  · exact ⟨S,hx,hs,u,hu⟩
  by_cases hdeg : H.degree x = 0
  · exact ⟨{x},mem_singleton_self x,(singleton_block H x hdeg).1,x,(singleton_block H x hdeg).2⟩
  obtain ⟨y,hy⟩ := (H.degree_pos_iff_exists_adj x).mp (by omega)
  let P := ((univ : Finset V) \ S).filter (fun w => 0 < H.degree w)
  have hin (a : V) (hax : a ∉ S) (ha : ∃ b, H.Adj a b) : a ∈ P :=
    mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hax⟩,(H.degree_pos_iff_exists_adj a).mpr ha⟩
  have hyp : y ∉ S := fun h => hs y h x hx hy.symm
  have hp : ({x,y} : Finset V) ⊆ P := insert_subset (hin x hx ⟨y,hy⟩)
    (singleton_subset_iff.mpr (hin y hyp ⟨x,hy.symm⟩))
  have hcard : P.card ≤ ({x,y} : Finset V).card := by simpa [hy.ne] using hc
  have heq := eq_of_subset_of_card_le hp hcard
  refine ⟨{x,y},by simp,?_,x,?_⟩
  · intro a ha b hb hab
    have haS : a ∉ S := by
      rcases mem_insert.mp ha with rfl | h
      · exact hx
      · simpa [mem_singleton.mp h] using hyp
    have hbS : b ∉ S := fun hb' => hs b hb' a haS hab.symm
    exact hb (heq.symm ▸ hin b hbS ⟨a,hab.symm⟩)
  · refine ⟨by simp,?_⟩
    intro a ha hne
    have := (mem_insert.mp ha).resolve_left hne
    simpa [mem_singleton.mp this] using hy

private theorem blocks_small_max (H : SimpleGraph V) (hm : maxEdgeNeighborhood H ≤ 3) :
    HasBlocks H := by
  classical
  have hd := degree_bound H 2 hm
  intro x
  by_cases hx : H.degree x = 0
  · exact ⟨{x},by simp,(singleton_block H x hx).1,x,(singleton_block H x hx).2⟩
  by_cases h₂ : H.degree x = 2
  · exact ⟨closedNeighborhood H x,mem_insert_self _ _,neighborhood_closed H x (by omega),
      x,root_universal H x⟩
  obtain ⟨y,hy⟩ := (H.degree_pos_iff_exists_adj x).mp (by omega)
  by_cases hy₂ : H.degree y = 2
  · exact ⟨closedNeighborhood H y,mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr hy.symm),
      neighborhood_closed H y (by omega),y,root_universal H y⟩
  have deg_y : 0 < H.degree y := (H.degree_pos_iff_exists_adj y).mpr ⟨x,hy.symm⟩
  have hxN : H.neighborFinset x = {y} := by
    apply (eq_of_subset_of_card_le (s := {y}) ?_ ?_).symm
    · exact singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr hy)
    · rw [card_neighborFinset_eq_degree,card_singleton]
      have := hd x
      omega
  have hyN : H.neighborFinset y = {x} := by
    apply (eq_of_subset_of_card_le (s := {x}) ?_ ?_).symm
    · exact singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr hy.symm)
    · rw [card_neighborFinset_eq_degree,card_singleton]
      have := hd y
      omega
  refine ⟨closedNeighborhood H x,mem_insert_self _ _,?_,x,root_universal H x⟩
  intro a ha b hb hab
  have hS : closedNeighborhood H x = {x,y} := by simp [closedNeighborhood,hxN]
  rw [hS] at ha hb
  rcases mem_insert.mp ha with rfl | ha
  · have h := (H.mem_neighborFinset _ _).mpr hab
    rw [hxN] at h
    exact hb (mem_insert_of_mem h)
  · rw [mem_singleton.mp ha] at hab
    have h := (H.mem_neighborFinset _ _).mpr hab
    rw [hyN] at h
    exact hb (mem_insert.mpr (Or.inl (mem_singleton.mp h)))


private def degreeHigh (H : SimpleGraph V) (r : ℕ) : Finset V :=
  univ.filter (fun x => r-1 ≤ H.degree x)

private def degreeLow (H : SimpleGraph V) (r : ℕ) : Finset V :=
  univ.filter (fun x => H.degree x < r-1)

private def degreeTop (H : SimpleGraph V) (r : ℕ) : Finset V :=
  univ.filter (fun x => H.degree x = r)

omit [Fintype V] in
private theorem card_filter_eq_indicator (S : Finset V) (p : V → Prop) [DecidablePred p] :
    (S.filter p).card = ∑ x ∈ S, if p x then (1 : ℕ) else 0 := by
  rw [← Finset.sum_filter]
  simp

private theorem degree_cost_identity (H : SimpleGraph V) {r : ℕ} (hr : 3 ≤ r)
    (hd : ∀ x, H.degree x ≤ r) :
    (∑ x, cost r (H.degree x)) + (degreeTop H r).card =
      (r-1)*(degreeHigh H r).card + ∑ x ∈ degreeLow H r, H.degree x := by
  unfold degreeTop degreeHigh degreeLow
  rw [card_filter_eq_indicator, card_filter_eq_indicator, Finset.sum_filter, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hx := hd x
  by_cases he : H.degree x = r
  · simp [cost,he,show r-1 ≤ r by omega,show ¬r < r-1 by omega]
    omega
  by_cases ha : r-1 ≤ H.degree x
  · have hh : H.degree x = r-1 := by omega
    simp [cost,he,ha,hh,show r-1 ≠ r by omega]
  · have h : H.degree x < r-1 := by omega
    simp [cost,he,ha,h]

omit [Fintype V] in
private theorem count_neighbors_comm (H : SimpleGraph V) (S T : Finset V) :
    (∑ v ∈ S, (T.filter (H.Adj v)).card) =
      ∑ w ∈ T, (S.filter (H.Adj w)).card := by
  simp only [card_filter_eq_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : H.Adj v w
  · simp [h,h.symm]
  · have hn : ¬H.Adj w v := fun h' => h h'.symm
    simp [h,hn]

private theorem bound_neighbor_card (H : SimpleGraph V) (S : Finset V) (x : V) :
    (S.filter (H.Adj x)).card ≤ H.degree x := by
  rw [← H.card_neighborFinset_eq_degree x]
  exact card_le_card (fun w hw => (H.mem_neighborFinset _ _).mpr (mem_filter.mp hw).2)

private theorem closed_high_small_outside (H : SimpleGraph V) {r : ℕ} (hr : 3 ≤ r)
    (hcost : (∑ x, cost r (H.degree x)) ≤ r*(r-1))
    {u : V} (hu : H.degree u = r) (hall : ∀ x ∈ closedNeighborhood H u, r-1 ≤ H.degree x) :
    (((univ : Finset V) \ closedNeighborhood H u).filter (fun x => 0 < H.degree x)).card ≤ 2 := by
  classical
  let S := closedNeighborhood H u
  let T := (univ : Finset V) \ S
  have hpart : (∑ x ∈ T, cost r (H.degree x)) + (∑ x ∈ S, cost r (H.degree x)) =
      ∑ x, cost r (H.degree x) := sum_sdiff (subset_univ _)
  have hS : S.card * (r-2) ≤ ∑ x ∈ S, cost r (H.degree x) := by
    rw [← sum_const_nat (s := S) (f := fun _ => r-2) (fun _ _ => rfl)]
    apply sum_le_sum
    intro x hx
    have := hall x hx
    unfold cost
    split <;> omega
  have hT : (T.filter (fun x => 0 < H.degree x)).card ≤ ∑ x ∈ T, cost r (H.degree x) := by
    rw [card_filter_eq_indicator]
    apply sum_le_sum
    intro x _
    unfold cost
    split <;> split <;> omega
  have hcard : S.card = r+1 := (closed_card H u).trans (by rw [hu])
  rw [hcard] at hS
  have id : (r+1)*(r-2)+2 = r*(r-1) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hr
    have a : 3+k-2 = k+1 := by omega
    have b : 3+k-1 = k+2 := by omega
    rw [a,b]
    ring
  change (T.filter (fun x => 0 < H.degree x)).card ≤ 2
  omega

set_option maxHeartbeats 1200000 in
private theorem blocks_from_budget (H : SimpleGraph V) {r : ℕ} (hr : 3 ≤ r)
    (hm : maxEdgeNeighborhood H ≤ 1+r) (hq : r ≤ (degreeHigh H r).card)
    (hcost : (∑ x, cost r (H.degree x)) ≤ r*(r-1)) : HasBlocks H := by
  classical
  have hd := degree_bound H r hm
  by_cases hcomplete : ∃ x, H.degree x = r ∧
      ∀ y ∈ closedNeighborhood H x, r-1 ≤ H.degree y
  · obtain ⟨x,hx,hall⟩ := hcomplete
    have hc := neighborhood_closed H x (by omega)
    exact two_or_fewer_outside H hc (root_universal H x)
      (closed_high_small_outside H hr hcost hx hall)
  let A := degreeTop H r
  let L := degreeLow H r
  let Q := degreeHigh H r
  let f := fun x => (L.filter (H.Adj x)).card
  let g := fun y => (A.filter (H.Adj y)).card
  have hA (x : V) : x ∈ A ↔ H.degree x = r := by simp [A,degreeTop]
  have hL (x : V) : x ∈ L ↔ H.degree x < r-1 := by simp [L,degreeLow]
  have hQ (x : V) : x ∈ Q ↔ r-1 ≤ H.degree x := by simp [Q,degreeHigh]
  have hAB : A ⊆ Q := fun x hx => (hQ x).mpr (by rw [(hA x).mp hx]; omega)
  have ha (x : V) (hx : x ∈ A) : 1 ≤ f x := by
    by_contra! h
    have hd₀ := (hA x).mp hx
    apply hcomplete
    refine ⟨x,hd₀,?_⟩
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · omega
    · by_contra! hlow
      have hm : y ∈ L.filter (H.Adj x) :=
        mem_filter.mpr ⟨(hL y).mpr hlow,(H.mem_neighborFinset _ _).mp hy⟩
      exact (not_le_of_gt h) (card_pos.mpr ⟨y,hm⟩)
  have hg (x : V) (_ : x ∈ L) : g x ≤ H.degree x := bound_neighbor_card H A x
  have hcount : (∑ x ∈ A, f x) = ∑ y ∈ L, g y := count_neighbors_comm H A L
  have hAlo : A.card ≤ ∑ x ∈ A, f x := by
    rw [← Nat.mul_one A.card,← sum_const_nat (s := A) (f := fun _ => 1) (fun _ _ => rfl)]
    exact sum_le_sum ha
  have hLhi : (∑ y ∈ L, g y) ≤ ∑ y ∈ L, H.degree y := sum_le_sum hg
  have hAmass := degree_cost_identity H hr hd
  change (∑ x, cost r (H.degree x)) + A.card =
    (r-1)*Q.card + ∑ y ∈ L, H.degree y at hAmass
  change r ≤ Q.card at hq
  have hprod : (r-1)*Q.card ≤ (r-1)*r := by
    rw [Nat.mul_comm (r-1) r]
    omega
  have hQr : Q.card = r :=
    le_antisymm (Nat.le_of_mul_le_mul_left hprod (by omega)) hq
  rw [hQr,Nat.mul_comm (r-1) r] at hAmass
  have hmEq : (∑ y ∈ L, H.degree y) = A.card := by omega
  have hONE (x : V) (hx : x ∈ A) : f x = 1 := by
    have hmSum : (∑ v ∈ A, (1:ℕ)) = ∑ v ∈ A, f v := by simp; omega
    by_contra hn
    have hgt : 1 < f x := by have := ha x hx; omega
    have hh := sum_lt_sum ha ⟨x,hx,hgt⟩
    omega
  have hALL (y : V) (hy : y ∈ L) : g y = H.degree y := by
    have hmSum : (∑ v ∈ L, g v) = ∑ v ∈ L, H.degree v := by omega
    by_contra hn
    have hgt : g y < H.degree y := by have := hg y hy; omega
    have hh := sum_lt_sum hg ⟨y,hy,hgt⟩
    omega
  by_cases hAexists : A.Nonempty
  · obtain ⟨u,hu⟩ := hAexists
    let S := closedNeighborhood H u
    have hdu := (hA u).mp hu
    have hS : S.card = r+1 := (closed_card H u).trans (by rw [hdu])
    have hClosed : Closed H S := neighborhood_closed H u (by omega)
    have hI : S ∩ L = L.filter (H.Adj u) := by
      ext x
      simp only [mem_inter,mem_filter]
      constructor
      · rintro ⟨hx,hxl⟩
        rcases mem_insert.mp hx with he | hx
        · subst x
          have hh := (hL u).mp hxl
          omega
        · exact ⟨hxl,(H.mem_neighborFinset _ _).mp hx⟩
      · rintro ⟨hxl,hux⟩
        exact ⟨mem_insert_of_mem ((H.mem_neighborFinset _ _).mpr hux),hxl⟩
    have hInt : (S ∩ L).card = 1 := by rw [hI]; exact hONE u hu
    have hsub : S \ L ⊆ Q := by
      intro x hx
      apply (hQ x).mpr
      apply Classical.byContradiction
      intro h
      exact (mem_sdiff.mp hx).2 ((hL x).mpr (by omega))
    have hpart := card_inter_add_card_sdiff S L
    have eq : S \ L = Q := eq_of_subset_of_card_le hsub (by omega)
    have hQin : Q ⊆ S := by rw [← eq]; exact sdiff_subset
    have hout (y : V) (hy : y ∉ S) : H.degree y = 0 := by
      have hyL : y ∈ L := (hL y).mpr (by
        apply Classical.byContradiction
        intro hn
        exact hy (hQin ((hQ y).mpr (by omega))))
      have he : A.filter (H.Adj y) = ∅ := by
        ext x
        simp only [mem_filter,not_mem_empty,iff_false]
        exact fun ⟨hx,ha⟩ => hClosed x (hQin (hAB hx)) y hy ha.symm
      have h := hALL y hyL
      simp [g,he] at h
      omega
    intro y
    by_cases hy : y ∈ S
    · exact ⟨S,hy,hClosed,u,root_universal H u⟩
    · exact ⟨{y},by simp,(singleton_block H y (hout y hy)).1,y,(singleton_block H y (hout y hy)).2⟩
  have hA₀ : A = ∅ := not_nonempty_iff_eq_empty.mp hAexists
  have hout (x : V) (hx : x ∉ Q) : H.degree x = 0 := by
    have h := hALL x ((hL x).mpr (by
      apply Classical.byContradiction
      intro h
      exact hx ((hQ x).mpr (by omega))))
    simpa [g,hA₀] using h.symm
  have hDegQ (x : V) (hx : x ∈ Q) : H.degree x = r-1 := by
    have h₁ := (hQ x).mp hx
    have h₂ := hd x
    have h₃ : H.degree x ≠ r := by
      intro h
      have hh := (hA x).mpr h
      simp [hA₀] at hh
    omega
  have hClosed : Closed H Q := by
    intro a _ b hb hab
    have hh := (H.degree_pos_iff_exists_adj b).mpr ⟨a,hab.symm⟩
    have := hout b hb
    omega
  intro x
  by_cases hx : x ∈ Q
  · have hclose : closedNeighborhood H x ⊆ Q := by
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact hx
      · apply Classical.byContradiction
        intro hn
        exact hClosed x hx y hn ((H.mem_neighborFinset _ _).mp hy)
    have heq : closedNeighborhood H x = Q := eq_of_subset_of_card_le hclose (by
      rw [closed_card,hDegQ x hx,hQr]
      omega)
    exact ⟨Q,hx,hClosed,x,heq ▸ root_universal H x⟩
  · exact ⟨{x},by simp,(singleton_block H x (hout x hx)).1,x,(singleton_block H x (hout x hx)).2⟩

private theorem bound_implies_wtd (G : SimpleGraph V) (hc : G.Connected)
    (h : maxEdgeNeighborhood Gᶜ ≤ 1 + residue G) : WellTotalDominated G := by
  haveI := hc.nonempty
  let r := residue G
  change maxEdgeNeighborhood Gᶜ ≤ 1+r at h
  have hBlocks : HasBlocks Gᶜ := by
    by_cases hr : 3 ≤ r
    · have hd := degree_bound Gᶜ r h
      have hb (x : ℕ) (hx : x ∈ degreeList Gᶜ) : x ≤ r := by
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
        exact hd v
      obtain ⟨hq,hc⟩ := comp_run_invariants (complement_run G) hr hb
      rw [degreeList_mass] at hq hc
      have hq' : r ≤ (degreeHigh Gᶜ r).card := by
        simpa [degreeHigh,high] using hq
      exact blocks_from_budget Gᶜ hr h hq' hc
    · exact blocks_small_max Gᶜ (by omega)
  simpa using wtd_of_blocks Gᶜ hBlocks

/-- The exact catalogue bound, using zero for the empty edge maximum. -/
theorem conjecture324 (G : SimpleGraph V) (hc : G.Connected) (_hn : 1 < Fintype.card V)
    (h : maxEdgeNeighborhood Gᶜ ≤ 1 + residue G) : WellTotalDominated G :=
  bound_implies_wtd G hc h

/-- Complete graphs satisfy the conclusion even if the empty maximum is undefined. -/
theorem complete_wellTotalDominated (G : SimpleGraph V) (hc : G.Connected)
    (h : ¬∃ a b, Gᶜ.Adj a b) : WellTotalDominated G :=
  bound_implies_wtd G hc (by rw [empty_edge_max _ h]; omega)

#print axioms conjecture324
#print axioms complete_wellTotalDominated
#print axioms max_attained

end Graph
end
end Graffiti324
