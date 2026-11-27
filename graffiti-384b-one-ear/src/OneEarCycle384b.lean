import Recolor34_384b
import LowSample384b

namespace Graffiti384b.OneEar
open Finset SimpleGraph LowSample
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A simple route of even positive length avoiding the unique ear pins an alternating cycle. -/
theorem even_route {e : V} (only : twos G = {e}) (q : (types G).card ≤ (nonleaves G).card)
    {n : ℕ} (big : 2 ≤ n) (even : n % 2 = 0) (f : ℕ → V)
    (step : ∀ i < n, G.Adj (f i) (f (i+1)))
    (inj : ∀ i ≤ n, ∀ j ≤ n, f i = f j → i=j)
    (avoid : ∀ i ≤ n, f i ≠ e) (first : G.Adj e (f 0)) (last : G.Adj e (f n)) :
    gamma G ≤ bound G := by
  classical
  let side (k : ℕ) := (((range (n+1)).filter (fun i => i%2=k)).image f)
  let P := side 0
  let Q := insert e (side 1)
  have mem (k i : ℕ) (hi : i≤n) (par : i%2=k) : f i∈side k :=
    mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr (by omega),par⟩,rfl⟩
  have index {k : ℕ} {v : V} (m : v∈side k) : ∃ i≤n, i%2=k ∧ f i=v := by
    obtain ⟨i,im,fi⟩ := mem_image.mp m
    exact ⟨i,Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp im).1),(mem_filter.mp im).2,fi⟩
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro v vp vq
    obtain ⟨i,hi,ei,rfl⟩ := index vp
    rcases mem_insert.mp vq with eq | vq
    · exact avoid i hi eq
    · obtain ⟨j,hj,oj,eq⟩ := index vq
      have := inj j hj i hi eq
      omega
  have middle (i : ℕ) (lo : 0<i) (up : i<n) :
      2 ≤ nbr G (f i) (side (1-i%2)) := by
    have prev := step (i-1) (by omega)
    rw [show i-1+1=i by omega] at prev
    exact PinnedColor34.two G (fun eq => by have := inj (i-1) (by omega) (i+1) (by omega) eq; omega)
      prev.symm (step i up) (mem _ _ (by omega) (by omega)) (mem _ _ (by omega) (by omega))
  have eqm : e∈Q := mem_insert_self ..
  apply PinnedColor34.complete G dis q
  · intro v vn _ out
    by_contra! small
    have vm : v∈twos G := mem_sdiff.mpr ⟨vn,fun vh => by have := (mem_filter.mp vh).2; omega⟩
    rw [only,mem_singleton] at vm
    exact out (vm ▸ eqm)
  · intro v vp
    obtain ⟨i,hi,par,rfl⟩ := index vp
    by_cases iz : i=0
    · subst i
      exact PinnedColor34.two G (Ne.symm (avoid 1 (by omega))) first.symm (step 0 (by omega))
        eqm (mem_insert_of_mem (mem 1 1 (by omega) rfl))
    by_cases en : i=n
    · subst i
      have prev := step (n-1) (by omega)
      rw [show n-1+1=n by omega] at prev
      exact PinnedColor34.two G (Ne.symm (avoid (n-1) (by omega))) last.symm prev.symm eqm
        (mem_insert_of_mem (mem 1 _ (by omega) (by omega)))
    have h := middle i (by omega) (by omega)
    rw [par] at h
    exact h.trans (card_le_card (filter_subset_filter _ (subset_insert ..)))
  · intro v vq
    rcases mem_insert.mp vq with rfl | vm
    · exact PinnedColor34.two G (fun eq => by have := inj 0 (by omega) n le_rfl eq; omega)
        first last (mem 0 0 (by omega) rfl) (mem 0 n le_rfl even)
    · obtain ⟨i,hi,par,rfl⟩ := index vm
      have h := middle i (by omega) (by omega)
      simpa only [par,Nat.sub_self] using h

end Graffiti384b.OneEar
#print axioms Graffiti384b.OneEar.even_route
