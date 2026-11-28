import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
The finite interval stage of the ordered two-route construction.
Source draft only; not yet checked by Lean. The index type labels the
original detours, even when two candidates have identical endpoints.
-/
namespace PosaGreedy189

variable {ι : Type*} (S : Finset ι) (l r : ι → ℕ) (N : ℕ)

/-- At threshold `c`, take a detour starting strictly before `c`
and extending strictly past it, maximizing the right endpoint among
all interval candidates starting before `c`. -/
structure ChoiceAt (c : ℕ) (a : ι) : Prop where
  source : a ∈ S
  left : l a < c
  advances : c < r a
  best : ∀ b ∈ S, l b < c → r b ≤ r a

/-- The initial threshold will be 1; subsequent thresholds are precisely
the preceding right endpoints. -/
inductive Trace : ℕ → List ι → Prop
  | stop : Trace N []
  | step {c : ℕ} {a : ι} {as : List ι} :
      ChoiceAt S l r c a → Trace (r a) as → Trace c (a :: as)

variable {S l r N}

theorem exists_trace
    (bound : ∀ a ∈ S, r a ≤ N)
    (bridge : ∀ i, 0 < i → i < N → ∃ a ∈ S, l a < i ∧ i < r a)
    (c : ℕ) (pos : 0 < c) (leN : c ≤ N) :
    ∃ as, Trace S l r N c as := by
  classical
  by_cases endp : c = N
  · subst c
    exact ⟨[], .stop⟩
  · obtain ⟨b, hb, bl, br⟩ := bridge c pos (lt_of_le_of_ne leN endp)
    let U := S.filter (fun a => l a < c)
    have hU : U.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, bl⟩⟩
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image U r hU
    have ha' := Finset.mem_filter.mp ha
    have advance : c < r a :=
      br.trans_le (hmax b (Finset.mem_filter.mpr ⟨hb, bl⟩))
    have hrN : r a ≤ N := bound a ha'.1
    obtain ⟨as, htail⟩ := exists_trace bound bridge (r a)
      (pos.trans advance) hrN
    refine ⟨a :: as, .step ⟨ha'.1, ha'.2, advance, ?_⟩ htail⟩
    intro d hd dl
    exact hmax d (Finset.mem_filter.mpr ⟨hd, dl⟩)
termination_by N - c
decreasing_by omega

namespace Trace

theorem mem_source_right {c : ℕ} {xs : List ι} (h : Trace S l r N c xs)
    {a : ι} (am : a ∈ xs) : a ∈ S ∧ c < r a := by
  induction h with
  | stop => simp at am
  | @step c x ys hfirst htail ih =>
      rcases List.mem_cons.mp am with e | hm
      · subst a
        exact ⟨hfirst.source, hfirst.advances⟩
      · obtain ⟨hs, hr⟩ := ih hm
        exact ⟨hs, hfirst.advances.trans hr⟩

theorem suffix {c : ℕ} {xs ys : List ι} (h : Trace S l r N c (xs ++ ys)) :
    ∃ d, Trace S l r N d ys := by
  induction xs generalizing c with
  | nil => exact ⟨c, h⟩
  | cons x xs ih =>
    change Trace S l r N c (x :: (xs ++ ys)) at h
    cases h with
    | step hx htail => exact ih htail

theorem last_right {c : ℕ} {xs : List ι} {a : ι}
    (h : Trace S l r N c (xs ++ [a])) : r a = N := by
  obtain ⟨_, H⟩ := h.suffix (xs := xs) (ys := [a])
  cases H with
  | step hx done => cases done; rfl

/-- In both coordinates the chain is strictly increasing; source labels
therefore cannot repeat. -/
theorem pairwise_increasing {c : ℕ} {xs : List ι} (h : Trace S l r N c xs) :
    xs.Pairwise (fun a b => l a < l b ∧ r a < r b) := by
  induction h with
  | stop => exact List.Pairwise.nil
  | @step c a ys xa tail ih =>
      refine List.pairwise_cons.mpr ⟨?_, ih⟩
      intro b bm
      obtain ⟨src, br⟩ := tail.mem_source_right bm
      have lb : c ≤ l b := by
        by_contra hn
        exact (not_le_of_gt br) (xa.best b src (by omega))
      exact ⟨xa.left.trans_le lb, br⟩

theorem consecutive_overlap {c : ℕ} {pre post : List ι} {a b : ι}
    (h : Trace S l r N c (pre ++ (a :: b :: post))) : l b < r a := by
  obtain ⟨_, suff⟩ := h.suffix (xs := pre) (ys := a :: b :: post)
  cases suff with
  | step first tail =>
    cases tail with
    | step second rest => exact second.left

/-- Starting with `a,b`, all remaining detours begin at or after the
right endpoint of `a`. In particular their interiors do not overlap
that of `a`; this is stronger than no triple interior overlap. -/
theorem later_separated {c : ℕ} {pre post : List ι} {a b d : ι}
    (h : Trace S l r N c (pre ++ (a :: b :: post))) (mem : d ∈ post) :
    r a ≤ l d := by
  obtain ⟨_, suff⟩ := h.suffix (xs := pre) (ys := a :: b :: post)
  cases suff with
  | step first tail =>
    cases tail with
    | step second rest =>
      obtain ⟨src, dr⟩ := rest.mem_source_right mem
      by_contra hn
      exact (not_le_of_gt dr) (second.best d src (by omega))

theorem no_triple_interior_overlap {c : ℕ} {pre post : List ι} {a b d : ι}
    (h : Trace S l r N c (pre ++ (a :: b :: post))) (mem : d ∈ post) (i : ℕ) :
    ¬ ((l a < i ∧ i < r a) ∧ (l b < i ∧ i < r b) ∧ (l d < i ∧ i < r d)) := by
  have sep := h.later_separated mem
  rintro ⟨⟨_, ar⟩, _, ⟨dl, _⟩⟩
  omega

/-- Every integer from the initial threshold up to (but not including)
the last endpoint lies strictly inside at least one chosen interval. -/
theorem covers {c : ℕ} {xs : List ι} (h : Trace S l r N c xs)
    {i : ℕ} (lo : c ≤ i) (hi : i < N) :
    ∃ a ∈ xs, l a < i ∧ i < r a := by
  induction h with
  | stop => omega
  | @step c a ys first tail ih =>
      by_cases ar : i < r a
      · exact ⟨a, List.mem_cons_self, first.left.trans_le lo, ar⟩
      · obtain ⟨b, bm, bl, br⟩ := ih (by omega)
        exact ⟨b, List.mem_cons_of_mem _ bm, bl, br⟩

end Trace

/-- A chain begins at index 0. By `Trace.last_right`, it ends at `N`;
the other `Trace` lemmas give the numeric track-spacing facts. -/
theorem exists_spanning_chain (hn : 2 ≤ N)
    (bound : ∀ a ∈ S, r a ≤ N)
    (bridge : ∀ i, 0 < i → i < N → ∃ a ∈ S, l a < i ∧ i < r a) :
    ∃ a xs, l a = 0 ∧ Trace S l r N 1 (a :: xs) := by
  obtain ⟨xs, h⟩ := exists_trace bound bridge 1 (by omega) (by omega)
  cases h with
  | stop => omega
  | @step c a xs first tail =>
    exact ⟨a, xs, by have := first.left; omega, .step first tail⟩

end PosaGreedy189

#print axioms PosaGreedy189.exists_spanning_chain
#print axioms PosaGreedy189.Trace.later_separated
#print axioms PosaGreedy189.Trace.covers
