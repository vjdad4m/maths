import PartialPaletteCut

namespace Graffiti384b.PositivePalette
open Finset SimpleGraph OneEar
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An even cycle through a designated vertex protects it along with every high vertex. -/
theorem even_cycle {e : V}
    {n : ℕ} (big : 2 ≤ n) (even : n % 2 = 0) (f : ℕ → V)
    (step : ∀ i < n, G.Adj (f i) (f (i+1)))
    (inj : ∀ i ≤ n, ∀ j ≤ n, f i = f j → i=j)
    (avoid : ∀ i ≤ n, f i ≠ e) (first : G.Adj e (f 0)) (last : G.Adj e (f n)) :
    Covered G (insert e (high G)) := by
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
  have middle (i : ℕ) (lo : 0 < i) (up : i < n) :
      2 ≤ nbr G (f i) (side (1-i%2)) := by
    have prev := step (i-1) (by omega)
    rw [show i-1+1=i by omega] at prev
    exact PinnedColor34.two G (fun eq => by have := inj (i-1) (by omega) (i+1) (by omega) eq; omega)
      prev.symm (step i up) (mem _ _ (by omega) (by omega)) (mem _ _ (by omega) (by omega))
  have eqm : e∈Q := mem_insert_self ..
  apply complete G dis
  · intro v vm _ out
    exact (mem_filter.mp ((mem_insert.mp vm).resolve_left (fun eq => out (eq ▸ eqm)))).2
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

variable {G} {e a b : V} {n : ℕ}

theorem close_cycle (p : Route G e a b n) 
     (ea : G.Adj e a) (eb : G.Adj e b)
    (ab : a≠b) (par : n%2=0) : Covered G (insert e (high G)) := by
  have nz : n≠0 := fun eq => ab (p.start.symm.trans (eq ▸ p.finish))
  exact even_cycle G (by omega) par p.atIdx p.step p.unique p.avoid (by rwa [p.start]) (by rwa [p.finish])

/-- A triangle on the first edge of a simple route allows either parity.
If its third vertex is on the route, the two prefixes to it have lengths one and two. -/
theorem parity_detour (p : Route G e a b n) (two : 2≤n) 
     (ea : G.Adj e a) (eb : G.Adj e b) (ab : a≠b)
    {z : V} (ze : z≠e) (az : G.Adj a z) (uz : G.Adj (p.atIdx 1) z) :
    Covered G (insert e (high G)) := by
  classical
  by_cases ev : n%2=0
  · exact close_cycle p ea eb ab ev
  have au : G.Adj a (p.atIdx 1) := by simpa only [p.start] using p.step 0 (by omega)
  have earlier (i j : ℕ) (ij : i < j) (jn : j≤n) : ∀ k≤n-j, p.atIdx i ≠ (p.suffix j jn).atIdx k := by
    intro k hk eq
    have := p.unique i (by omega) (j+k) (by omega) eq
    omega
  have absent {j : ℕ} (jp : 0 < j) (jn : j≤n) : ∀ k≤n-j, a≠(p.suffix j jn).atIdx k :=
    by simpa only [p.start] using earlier 0 j jp jn
  by_cases hit : ∃ i≤n, p.atIdx i=z
  · obtain ⟨i,hi,iz⟩ := hit
    have ip : 1 < i := by
      by_cases le : 1 < i
      · exact le
      exfalso
      rcases (show i=0 ∨ i=1 by omega) with rfl|rfl
      · exact az.ne (p.start.symm.trans iz)
      · exact uz.ne iz
    let t := p.suffix i hi
    by_cases oddTail : (n-i)%2=1
    · let r := t.prepend (by rwa [iz]) ea.ne.symm (absent (by omega) hi)
      exact close_cycle r ea eb ab (by omega)
    · let s := t.prepend (by rwa [iz]) (p.avoid 1 (by omega)) (earlier 1 i ip hi)
      have fresh (k : ℕ) (hk : k≤n-i+1) : a≠s.atIdx k := by
        cases k with
        | zero => exact au.ne
        | succ j => exact absent (by omega) hi j (by omega)
      let r := s.prepend au ea.ne.symm fresh
      exact close_cycle r ea eb ab (by omega)
  · have zfresh (k : ℕ) (hk : k≤n-1) : z≠(p.suffix 1 (by omega)).atIdx k :=
      fun eq => hit ⟨1+k,by omega,eq.symm⟩
    let s := (p.suffix 1 (by omega)).prepend uz.symm ze zfresh
    have fr (k : ℕ) (hk : k≤n-1+1) : a≠s.atIdx k := by
      cases k with
      | zero => exact az.ne
      | succ j => exact absent (j:=1) (by decide) (by omega) j (by omega)
    let r := s.prepend az ea.ne.symm fr
    exact close_cycle r ea eb ab (by omega)
end Graffiti384b.PositivePalette
#print axioms Graffiti384b.PositivePalette.even_cycle
#print axioms Graffiti384b.PositivePalette.parity_detour
