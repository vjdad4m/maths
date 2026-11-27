import OneEarCycle384b

namespace Graffiti384b.OneEar
open Finset SimpleGraph LowSample
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An indexed simple route avoiding the ear. Values past the endpoint are ignored. -/
structure Route (G : SimpleGraph V) (e a b : V) (n : ℕ) where
  atIdx : ℕ → V
  start : atIdx 0 = a
  finish : atIdx n = b
  step : ∀ i < n, G.Adj (atIdx i) (atIdx (i+1))
  unique : ∀ i ≤ n, ∀ j ≤ n, atIdx i = atIdx j → i=j
  avoid : ∀ i ≤ n, atIdx i ≠ e

variable {e a b c : V} {n : ℕ}

def Route.suffix (p : Route G e a b n) (i : ℕ) (hi : i≤n) : Route G e (p.atIdx i) b (n-i) where
  atIdx j := p.atIdx (i+j)
  start := by simp
  finish := by rw [show i+(n-i)=n by omega,p.finish]
  step j hj := p.step (i+j) (by omega)
  unique j hj k hk eq := by have := p.unique (i+j) (by omega) (i+k) (by omega) eq; omega
  avoid j hj := p.avoid _ (by omega)

def Route.prepend (p : Route G e a b n) (edge : G.Adj c a) (ce : c≠e)
    (fresh : ∀ j≤n, c≠p.atIdx j) : Route G e c b (n+1) where
  atIdx := Nat.rec c (fun j _ => p.atIdx j)
  start := rfl
  finish := p.finish
  step i hi := by
    cases i with
    | zero => change G.Adj c (p.atIdx 0); rwa [p.start]
    | succ j => exact p.step j (by omega)
  unique i hi j hj eq := by
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => exact (fresh j (by omega) eq).elim
    | succ i =>
      cases j with
      | zero => exact (fresh i (by omega) eq.symm).elim
      | succ j => exact congrArg Nat.succ (p.unique i (by omega) j (by omega) eq)
  avoid i hi := by
    cases i with
    | zero => exact ce
    | succ j => exact p.avoid j (by omega)

def Route.reverse (p : Route G e a b n) : Route G e b a n where
  atIdx i := p.atIdx (n-i)
  start := by simpa using p.finish
  finish := by simpa using p.start
  step i hi := by
    have h := (p.step (n-(i+1)) (by omega)).symm
    rwa [show n-(i+1)+1=n-i by omega] at h
  unique i hi j hj eq := by
    have := p.unique (n-i) (by omega) (n-j) (by omega) eq
    omega
  avoid i _ := p.avoid (n-i) (by omega)

theorem Route.close (p : Route G e a b n) (only : twos G={e})
    (q : (types G).card≤(nonleaves G).card) (ea : G.Adj e a) (eb : G.Adj e b)
    (ab : a≠b) (par : n%2=0) : gamma G≤bound G := by
  have nz : n≠0 := fun eq => ab (p.start.symm.trans (eq ▸ p.finish))
  exact even_route G only q (by omega) par p.atIdx p.step p.unique p.avoid (by rwa [p.start]) (by rwa [p.finish])

/-- A triangle on the first edge of a simple route allows either parity.
If its third vertex is on the route, the two prefixes to it have lengths one and two. -/
theorem change_parity (p : Route G e a b n) (two : 2≤n) (only : twos G={e})
    (q : (types G).card≤(nonleaves G).card) (ea : G.Adj e a) (eb : G.Adj e b) (ab : a≠b)
    {z : V} (ze : z≠e) (az : G.Adj a z) (uz : G.Adj (p.atIdx 1) z) :
    gamma G≤bound G := by
  classical
  by_cases ev : n%2=0
  · exact p.close only q ea eb ab ev
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
      exact r.close only q ea eb ab (by omega)
    · let s := t.prepend (by rwa [iz]) (p.avoid 1 (by omega)) (earlier 1 i ip hi)
      have fresh (k : ℕ) (hk : k≤n-i+1) : a≠s.atIdx k := by
        cases k with
        | zero => exact au.ne
        | succ j => exact absent (by omega) hi j (by omega)
      let r := s.prepend au ea.ne.symm fresh
      exact r.close only q ea eb ab (by omega)
  · have zfresh (k : ℕ) (hk : k≤n-1) : z≠(p.suffix 1 (by omega)).atIdx k :=
      fun eq => hit ⟨1+k,by omega,eq.symm⟩
    let s := (p.suffix 1 (by omega)).prepend uz.symm ze zfresh
    have fr (k : ℕ) (hk : k≤n-1+1) : a≠s.atIdx k := by
      cases k with
      | zero => exact az.ne
      | succ j => exact absent (j:=1) (by decide) (by omega) j (by omega)
    let r := s.prepend az ea.ne.symm fr
    exact r.close only q ea eb ab (by omega)
end Graffiti384b.OneEar
#print axioms Graffiti384b.OneEar.change_parity
