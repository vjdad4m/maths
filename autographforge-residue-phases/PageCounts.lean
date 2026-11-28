import ResiduePhases

namespace ResiduePhases
open private hhTail descending descending_perm descending_sorted from Proof324

/-- A descending page list with counts of twos, ones, and zeros. -/
def buckets (a b c : ℕ) : List ℕ :=
  List.replicate a 2 ++ List.replicate b 1 ++ List.replicate c 0

theorem buckets_sorted (a b c : ℕ) :
    (buckets a b c).Pairwise (fun x y => y ≤ x) := by
  unfold buckets
  have ordered (x n : ℕ) : (List.replicate n x).Pairwise (fun x y => y ≤ x) :=
    (List.sorted_replicate _ _).2 (Or.inr le_rfl)
  have o12 : (List.replicate a 2 ++ List.replicate b 1).Pairwise (fun x y => y ≤ x) := by
    rw [List.pairwise_append]
    refine ⟨ordered 2 a,ordered 1 b,?_⟩
    intro x hx y hy
    rw [List.eq_of_mem_replicate hx,List.eq_of_mem_replicate hy]
    decide
  rw [List.pairwise_append]
  refine ⟨o12,ordered 0 c,?_⟩
  intro x _ y hy
  rw [List.eq_of_mem_replicate hy]
  exact Nat.zero_le _

private theorem sorted_buckets_of_perm {lo : List ℕ} {a b c : ℕ}
    (h : lo.Perm (buckets a b c)) : descending lo = buckets a b c :=
  List.eq_of_perm_of_sorted ((descending_perm lo).trans h) (descending_sorted lo)
    (buckets_sorted _ _ _)

/-- Spend a budget on the largest remaining page degrees. This formula
requires enough positive entries, so none of the budget is wasted on zeros. -/
theorem bucket_step (a b c t : ℕ) (enough : t ≤ a+b) :
    (hhTail t (buckets a b c)).Perm
      (buckets (a-t) (b-(t-a)+min t a) (c+(t-a))) := by
  by_cases ha : t ≤ a
  · have hsplit : buckets a b c =
        List.replicate t 2 ++ (List.replicate (a-t) 2 ++ List.replicate b 1 ++ List.replicate c 0) := by
      have e : a = t+(a-t) := by omega
      unfold buckets
      conv_lhs => rw [e,List.replicate_add]
      simp only [List.append_assoc]
    have take : (List.replicate t 2 ++ (List.replicate (a-t) 2 ++ List.replicate b 1 ++
        List.replicate c 0)).take t = List.replicate t 2 := by
      rw [List.take_append_of_le_length (by simp),List.take_replicate,min_self]
    have drop : (List.replicate t 2 ++ (List.replicate (a-t) 2 ++ List.replicate b 1 ++
        List.replicate c 0)).drop t =
        List.replicate (a-t) 2 ++ List.replicate b 1 ++ List.replicate c 0 := by
      simp [List.drop_append_eq_append_drop,List.drop_replicate]
    rw [hsplit,hhTail,take,drop,List.map_replicate]
    simp only [min_eq_left ha,Nat.sub_eq_zero_of_le ha,Nat.sub_zero,Nat.add_zero,buckets]
    change (List.replicate t 1 ++ (List.replicate (a-t) 2 ++ List.replicate b 1 ++
      List.replicate c 0)).Perm _
    simp only [List.append_assoc]
    have p := (List.perm_append_comm (l₁ := List.replicate t 1)
      (l₂ := List.replicate (a-t) 2)).append_right (List.replicate b 1 ++ List.replicate c 0)
    simpa only [List.append_assoc, List.replicate_add, Nat.add_comm b t] using p
  · have h : a ≤ t := by omega
    let v := t-a
    have vb : v ≤ b := by dsimp [v]; omega
    let front := List.replicate a 2 ++ List.replicate v 1
    let back := List.replicate (b-v) 1 ++ List.replicate c 0
    have plen : front.length = t := by simp [front,v]; omega
    have hsplit : buckets a b c = front ++ back := by
      have e : List.replicate b 1 = List.replicate v 1 ++ List.replicate (b-v) 1 := by
        rw [← List.replicate_add]
        congr 1
        omega
      change List.replicate a 2 ++ List.replicate b 1 ++ List.replicate c 0 = _
      conv_lhs => rw [e]
      simp only [front,back,List.append_assoc]
    rw [hsplit,hhTail,List.take_append_of_le_length (le_of_eq plen.symm),List.take_of_length_le (le_of_eq plen),
      List.drop_left' plen]
    simp only [List.drop_zero,List.map_append,List.map_replicate,front,back,
      buckets,Nat.sub_eq_zero_of_le h,List.replicate_zero,List.nil_append,min_eq_right h]
    change (List.replicate a 1 ++ List.replicate v 0 ++
      (List.replicate (b-v) 1 ++ List.replicate c 0)).Perm _
    have p := (List.perm_append_comm (l₁ := List.replicate v 0)
      (l₂ := List.replicate (b-v) 1)).append_left (List.replicate a 1)
    have q := p.append_right (List.replicate c 0)
    change List.Perm _ (List.replicate (b-v+a) 1 ++ List.replicate (c+v) 0)
    rw [Nat.add_comm (b-v) a,Nat.add_comm c v]
    simpa only [List.append_assoc,List.replicate_add] using q


/-- The page portion of a hub run, listed in order of its expenditures. -/
def spendPages : List ℕ → List ℕ → List ℕ
  | [], lo => lo
  | t :: ts, lo => spendPages ts (hhTail t (descending lo))

/-- When the initial degree mass exceeds the full expenditure by twice
the largest individual budget, no step ever spends on a zero. -/
theorem bucket_run {cap : ℕ} (ts lo : List ℕ) (a b c : ℕ)
    (inShape : lo.Perm (buckets a b c))
    (maxStep : ∀ t ∈ ts, t ≤ cap) (room : ts.sum + 2*cap ≤ 2*a+b) :
    ∃ A B C, (spendPages ts lo).Perm (buckets A B C) ∧
      A = a-ts.sum ∧ 2*A+B+ts.sum = 2*a+b ∧ A+B+C = a+b+c := by
  induction ts generalizing lo a b c with
  | nil => exact ⟨a,b,c,inShape,by simp,by simp,rfl⟩
  | cons t ts ih =>
    have ht := maxStep t (List.mem_cons_self ..)
    have enough : t ≤ a+b := by
      simp only [List.sum_cons] at room
      omega
    let a' := a-t
    let b' := b-(t-a)+min t a
    let c' := c+(t-a)
    have step : (hhTail t (descending lo)).Perm (buckets a' b' c') := by
      rw [sorted_buckets_of_perm inShape]
      exact bucket_step a b c t enough
    have mass : 2*a'+b'+t = 2*a+b := by
      dsimp [a',b']
      by_cases hh : t ≤ a
      · rw [min_eq_left hh]; omega
      · rw [min_eq_right (by omega : a ≤ t)]; omega
    have len : a'+b'+c' = a+b+c := by
      dsimp [a',b',c']
      by_cases hh : t ≤ a
      · rw [min_eq_left hh]; omega
      · rw [min_eq_right (by omega : a ≤ t)]; omega
    obtain ⟨A,B,C,perm,first,mass',len'⟩ := ih (hhTail t (descending lo)) a' b' c' step
      (fun u hu => maxStep u (List.mem_cons_of_mem _ hu)) (by
        simp only [List.sum_cons] at room
        omega)
    refine ⟨A,B,C,perm,?_,?_,len'.trans len⟩
    · simp only [List.sum_cons]
      dsimp [a'] at first
      omega
    · simp only [List.sum_cons]
      omega

/-- If a run starts with L twos, spends D ≥ L, and leaves an even mass
2p, the terminal residue is L-p. -/
theorem all_twos_residue {cap L p : ℕ} (ts : List ℕ)
    (maxStep : ∀ t ∈ ts, t ≤ cap) (room : ts.sum + 2*cap ≤ 2*L)
    (cleared : L ≤ ts.sum) (mass : ts.sum + 2*p = 2*L) :
    Graffiti324.residueSequence (spendPages ts (List.replicate L 2)) = L-p := by
  have input : (List.replicate L 2).Perm (buckets L 0 0) := by simp [buckets]
  obtain ⟨A,B,C,hperm,hA,hM,hL⟩ := bucket_run ts _ L 0 0 input maxStep (by simpa using room)
  have Az : A = 0 := by omega
  have Be : B = 2*p := by omega
  have Ce : C+p = L-p := by omega
  rw [residue_perm hperm,Az,Be]
  change Graffiti324.residueSequence (List.replicate (2*p) 1 ++ List.replicate C 0) = _
  rw [residue_even_ones,Ce]


private theorem sum_pred_positive (xs : List ℕ) (pos : ∀ x ∈ xs, 0 < x) :
    (xs.map Nat.pred).sum + xs.length = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have xp : 0 < x := pos x (List.mem_cons_self ..)
    have rest := ih (fun v hv => pos v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.pred_eq_sub_one] at *
    omega

private theorem hub_debt_step (n : ℕ) : (n+1)*n = n*(n-1)+2*n := by
  cases n with
  | zero => decide
  | succ n =>
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring

/-- Total spending on pages is the initial hub mass less the cost of
decrementing all other hubs at every step. Each individual expenditure
is bounded by the initial hub degree excess over the other hub count. -/
theorem hub_phase_budgets {cap : ℕ} {hi lo out : List ℕ}
    (run : HubPhase hi lo out)
    (high : ∀ x ∈ hi, hi.length+2 ≤ x)
    (upper : ∀ x ∈ hi, x ≤ hi.length-1+cap) :
    ∃ ts, out = spendPages ts lo ∧ (∀ t ∈ ts, t ≤ cap) ∧
      ts.sum + hi.length*(hi.length-1) = hi.sum := by
  induction run with
  | nil => exact ⟨[],rfl,by simp,by simp⟩
  | @step hi lo tail out d hd _ _ budget _ ih =>
    have perm := descending_perm hi
    rw [hd] at perm
    have len : hi.length = tail.length+1 := by simpa using perm.length_eq.symm
    have orig (x : ℕ) (hx : x ∈ d::tail) : hi.length+2 ≤ x ∧ x ≤ hi.length-1+cap :=
      ⟨high x (perm.mem_iff.mp hx),upper x (perm.mem_iff.mp hx)⟩
    have hi' : ∀ x ∈ tail.map Nat.pred, (tail.map Nat.pred).length+2 ≤ x := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      have hy' := (orig y (List.mem_cons_of_mem _ hy)).1
      simp only [List.length_map,Nat.pred_eq_sub_one]
      omega
    have upper' : ∀ x ∈ tail.map Nat.pred, x ≤ (tail.map Nat.pred).length-1+cap := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      have hy' := orig y (List.mem_cons_of_mem _ hy)
      have nz : 1 ≤ tail.length := List.length_pos_iff.mpr (by
        intro e; simp [e] at hy)
      simp only [List.length_map,Nat.pred_eq_sub_one]
      omega
    obtain ⟨ts,eq,bnd,total⟩ := ih hi' upper'
    refine ⟨(d-tail.length)::ts,eq,?_,?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl|mem
      · have dd := (orig d (List.mem_cons_self ..)).2
        omega
      · exact bnd t mem
    have desc : d+tail.sum = hi.sum := by simpa using perm.sum_eq
    have sub := sum_pred_positive tail (fun x hx => by
      have p := (orig x (List.mem_cons_of_mem _ hx)).1
      omega)
    simp only [List.length_map] at total
    rw [List.sum_cons,len,show tail.length+1-1 = tail.length by omega,hub_debt_step]
    omega

/-- Exact residue for the hub-page degree lists once the aggregate hub
budget leaves mass 2p, clears all the twos and never reaches zero early. -/
theorem hub_page_residue {hi : List ℕ} {cap L p : ℕ}
    (high : ∀ x ∈ hi, hi.length+2 ≤ x)
    (upper : ∀ x ∈ hi, x ≤ hi.length-1+cap)
    (room : hi.sum + 2*cap ≤ hi.length*(hi.length-1)+2*L)
    (cleared : hi.length*(hi.length-1)+L ≤ hi.sum)
    (mass : hi.sum + 2*p = hi.length*(hi.length-1)+2*L) :
    Graffiti324.residueSequence (hi ++ List.replicate L 2) = L-p := by
  have low : ∀ x ∈ List.replicate L 2, x ≤ 2 := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
  obtain ⟨out,run,_,_⟩ := hubs_go_first hi (List.replicate L 2) high low
  obtain ⟨ts,eq,bound,total⟩ := hub_phase_budgets run high upper
  rw [hub_phase_residue run,eq]
  exact all_twos_residue ts bound (by omega) (by omega) (by omega)


/-- The fan-chain degree sequence with j+3 blocks and 4j+9 pages in each block. -/
theorem fan_chain_degree_list (j : ℕ) :
    Graffiti324.residueSequence
      ((List.replicate (2*j+4) (4*j+10) ++ List.replicate 2 (4*j+9)) ++
        List.replicate ((j+3)*(4*j+9)) 2) = 2*j*j+11*j+14 := by
  have hh : 2*j+4+2-1 = 2*j+5 := by omega
  have sub : (j+3)*(4*j+9) - (2*j*j+10*j+13) = 2*j*j+11*j+14 := by
    have e : (j+3)*(4*j+9) = (2*j*j+10*j+13) + (2*j*j+11*j+14) := by ring
    rw [e]
    omega
  rw [← sub]
  apply hub_page_residue (cap := 2*j+6)
  · intro x hx
    simp only [List.length_append,List.length_replicate]
    rcases List.mem_append.mp hx with l|r
    · rw [List.eq_of_mem_replicate l]; omega
    · rw [List.eq_of_mem_replicate r]; omega
  · intro x hx
    simp only [List.length_append,List.length_replicate,hh]
    rcases List.mem_append.mp hx with l|r
    · rw [List.eq_of_mem_replicate l]; omega
    · rw [List.eq_of_mem_replicate r]; omega
  · simp only [List.sum_append,List.sum_replicate_nat,List.length_append,List.length_replicate,hh]
    have e : (2*j+4)*(4*j+10)+2*(4*j+9)+2*(2*j+6) + (4*j*j+16*j+14) =
        (2*j+4+2)*(2*j+5)+2*((j+3)*(4*j+9)) := by ring
    omega
  · simp only [List.sum_append,List.sum_replicate_nat,List.length_append,List.length_replicate,hh]
    have e : (2*j+4+2)*(2*j+5)+(j+3)*(4*j+9) + (j+1) =
        (2*j+4)*(4*j+10)+2*(4*j+9) := by ring
    omega
  · simp only [List.sum_append,List.sum_replicate_nat,List.length_append,List.length_replicate,hh]
    ring


/-- The book-chain degree sequence with j+3 blocks and 4j+9 pages in each block. -/
theorem book_chain_degree_list (j : ℕ) :
    Graffiti324.residueSequence
      ((List.replicate (2*j+4) (4*j+11) ++ List.replicate 2 (4*j+10)) ++
        List.replicate ((j+3)*(4*j+9)) 2) = 2*j*j+12*j+17 := by
  have hh : 2*j+4+2-1 = 2*j+5 := by omega
  have sub : (j+3)*(4*j+9) - (2*j*j+9*j+10) = 2*j*j+12*j+17 := by
    have e : (j+3)*(4*j+9) = (2*j*j+9*j+10) + (2*j*j+12*j+17) := by ring
    rw [e]
    omega
  rw [← sub]
  apply hub_page_residue (cap := 2*j+6)
  · intro x hx
    simp only [List.length_append,List.length_replicate]
    rcases List.mem_append.mp hx with l|r
    · rw [List.eq_of_mem_replicate l]; omega
    · rw [List.eq_of_mem_replicate r]; omega
  · intro x hx
    simp only [List.length_append,List.length_replicate,hh]
    rcases List.mem_append.mp hx with l|r
    · rw [List.eq_of_mem_replicate l]; omega
    · rw [List.eq_of_mem_replicate r]; omega
  · simp only [List.sum_append,List.sum_replicate_nat,List.length_append,List.length_replicate,hh]
    have e : (2*j+4)*(4*j+11)+2*(4*j+10)+2*(2*j+6) + (4*j*j+14*j+8) =
        (2*j+4+2)*(2*j+5)+2*((j+3)*(4*j+9)) := by ring
    omega
  · simp only [List.sum_append,List.sum_replicate_nat,List.length_append,List.length_replicate,hh]
    have e : (2*j+4+2)*(2*j+5)+(j+3)*(4*j+9) + (3*j+7) =
        (2*j+4)*(4*j+11)+2*(4*j+10) := by ring
    omega
  · simp only [List.sum_append,List.sum_replicate_nat,List.length_append,List.length_replicate,hh]
    ring

#print axioms bucket_step
#print axioms bucket_run
#print axioms all_twos_residue
#print axioms hub_phase_budgets
#print axioms hub_page_residue
#print axioms fan_chain_degree_list
#print axioms book_chain_degree_list
end ResiduePhases
