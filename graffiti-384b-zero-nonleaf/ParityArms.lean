import OriginalArms

namespace Graffiti384b.OddStars.HallArms
open Finset SimpleGraph OneEar PositivePalette
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An even cycle protects any two designated vertices on it and every high vertex. -/
private theorem marked_cycle {e z : V}
    {n : ℕ} (big : 2 ≤ n) (even : n % 2 = 0) (f : ℕ → V)
    (step : ∀ i < n, G.Adj (f i) (f (i+1)))
    (inj : ∀ i ≤ n, ∀ j ≤ n, f i = f j → i=j)
    (avoid : ∀ i ≤ n, f i ≠ e) (first : G.Adj e (f 0)) (last : G.Adj e (f n))
    (marked : ∃i≤n,f i=z) :
    Covered G (insert e (insert z (high G))) := by
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
  · intro v vm pin out
    have k := (mem_insert.mp vm).resolve_left (fun eq => out (eq ▸ eqm))
    rcases mem_insert.mp k with rfl|hv
    · obtain ⟨i,hi,fi⟩ := marked
      by_cases evenI : i%2=0
      · exact (pin (fi ▸ mem 0 i hi evenI)).elim
      · exact (out (mem_insert_of_mem (fi ▸ mem 1 i hi (by omega)))).elim
    · exact (mem_filter.mp hv).2
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

/-- Closing two disjoint arms at the two terminals produces a protected
cycle whenever their lengths have the same parity. -/
theorem equal_parity_cut {e z a b c d : V} (ez : e≠z)
    (ea : G.Adj e a) (eb : G.Adj e b) (az : a≠z) (bz : b≠z)
    (zc : G.Adj z c) (zd : G.Adj z d) {n m : ℕ}
    (p : Route (inside G ({e,z}ᶜ)) e a c n) (q : Route (inside G ({e,z}ᶜ)) e b d m)
    (sep : ∀i≤n,∀j≤m,p.atIdx i≠q.atIdx j) (par : n%2=m%2) :
    Covered G (insert e (insert z (high G))) := by
  classical
  let N := n+2+m
  let f (i : ℕ) := if i≤n then p.atIdx i else if i=n+1 then z else q.atIdx (N-i)
  have L {i : ℕ} (lo : i≤n) : f i=p.atIdx i := if_pos lo
  have M : f (n+1)=z := by simp [f]
  have R {i : ℕ} (hi : n+2≤i) : f i=q.atIdx (N-i) := by
    simp [f,show ¬i≤n by omega,show i≠n+1 by omega]
  have zfree {s t : V} {l : ℕ} (r : Route (inside G ({e,z}ᶜ)) e s t l)
      (sz : s≠z) (i : ℕ) (hi : i≤l) : r.atIdx i≠z := by
    cases i with
    | zero => simpa only [r.start] using sz
    | succ i =>
      have h := mem_compl.mp (r.step i (by omega)).2.2
      exact fun eq => h (mem_insert_of_mem (mem_singleton.mpr eq))
  have pz := zfree p az
  have qz := zfree q bz
  have step (i : ℕ) (hi : i<N) : G.Adj (f i) (f (i+1)) := by
    by_cases insideL : i<n
    · rw [L (by omega),L (by omega)]; exact (p.step i insideL).1
    by_cases lastL : i=n
    · subst i; rw [L le_rfl,M,p.finish]; exact zc.symm
    by_cases mid : i=n+1
    · subst i; rw [M,R (by omega),show N-(n+1+1)=m by dsimp [N]; omega,q.finish]; exact zd
    rw [R (by omega),R (by omega)]
    have move := (q.step (N-(i+1)) (by dsimp [N] at *; omega)).1.symm
    rwa [show N-(i+1)+1=N-i by omega] at move
  have unique (i : ℕ) (hi : i≤N) (j : ℕ) (hj : j≤N) (eq : f i=f j) : i=j := by
    have cls (t : ℕ) : t≤n ∨ t=n+1 ∨ n+2≤t := by omega
    rcases cls i with il|im|ir <;> rcases cls j with jl|jm|jr
    · exact p.unique i il j jl ((L il).symm.trans (eq.trans (L jl)))
    · subst j; rw [L il,M] at eq; exact (pz i il eq).elim
    · rw [L il,R jr] at eq; exact (sep i il (N-j) (by dsimp [N]; omega) eq).elim
    · subst i; rw [M,L jl] at eq; exact (pz j jl eq.symm).elim
    · omega
    · subst i; rw [M,R jr] at eq; exact (qz _ (by dsimp [N]; omega) eq.symm).elim
    · rw [R ir,L jl] at eq; exact (sep j jl (N-i) (by dsimp [N]; omega) eq.symm).elim
    · subst j; rw [R ir,M] at eq; exact (qz _ (by dsimp [N]; omega) eq).elim
    · rw [R ir,R jr] at eq
      have := q.unique (N-i) (by dsimp [N]; omega) (N-j) (by dsimp [N]; omega) eq
      omega
  have avoid (i : ℕ) (_ : i≤N) : f i≠e := by
    by_cases il : i≤n
    · rw [L il]; exact p.avoid i il
    by_cases im : i=n+1
    · subst i; rw [M]; exact ez.symm
    rw [R (by omega)]; exact q.avoid _ (by dsimp [N]; omega)
  apply marked_cycle G (e:=e) (z:=z) (n:=N) (by dsimp [N]; omega) (by dsimp [N]; omega) f step unique avoid
  · rwa [L (by omega),p.start]
  · rwa [R (by dsimp [N]; omega),Nat.sub_self,q.start]
  · exact ⟨n+1,by dsimp [N]; omega,M⟩

/-- Every disjoint linkage between these terminal neighbor pairs has odd
total length in an original-graph failure. -/
theorem failure_opposite_parity (bad : bound G<gamma G) {e z a b c d : V}
    (zz : trianglesAt G z=0) (dz : G.degree z=2) (one : trianglesAt G e=1)
    (ea : (patch G {z}).Adj e a) (eb : (patch G {z}).Adj e b)
    (zc : (patch G {z}).Adj z c) (zd : (patch G {z}).Adj z d) {n m : ℕ}
    (p : Route (inside (patch G {z}) ({e,z}ᶜ)) e a c n)
    (q : Route (inside (patch G {z}) ({e,z}ᶜ)) e b d m)
    (sep : ∀i≤n,∀j≤m,p.atIdx i≠q.atIdx j) : (n+m)%2=1 := by
  classical
  by_contra! even
  let J := patch G {z}
  have ez : e≠z := fun eq => by rw [eq,zz] at one; contradiction
  have noez : ¬G.Adj e z := by
    intro h
    have ee := (zero_two_forces_ears G bad zz dz).2 e one
    have zh := contacts_high G bad zz dz ee ((G.mem_neighborFinset ..).mpr h)
    have := (mem_filter.mp zh).2; omega
  have cut := equal_parity_cut J ez ea eb (fun h => noez (h ▸ ea.1)) (fun h => noez (h ▸ eb.1))
    zc zd p q sep (by omega)
  obtain ⟨_,_,tight,_⟩ := two_frames G bad zz dz one
  have eq := (high_description G bad zz dz {z}).1
  rw [eq] at cut
  have ret := count_covered G (covered_mono G (J:=J) (fun _ _ h => h.1) cut)
  have low (v : V) (dv : G.degree v=2) : v∉high G := fun h => by have := (mem_filter.mp h).2; omega
  have ee := (zero_two_forces_ears G bad zz dz).2 e one
  rw [card_insert_of_not_mem (by simp [ez,low e ee]),card_insert_of_not_mem (low z dz)] at ret
  omega

end Graffiti384b.OddStars.HallArms
#print axioms Graffiti384b.OddStars.HallArms.equal_parity_cut
#print axioms Graffiti384b.OddStars.HallArms.failure_opposite_parity