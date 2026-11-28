import Proof324

namespace ResiduePhases
open private residueAux descending descending_perm descending_sorted hhTail hhTail_length from Proof324

private theorem descending_of_perm {a b : List ℕ} (perm : a.Perm b)
    (sorted : b.Pairwise (fun x y => y ≤ x)) : descending a = b :=
  List.eq_of_perm_of_sorted ((descending_perm a).trans perm) (descending_sorted a) sorted

/-- Relabeling a degree list does not change its residue. -/
theorem residue_perm {a b : List ℕ} (h : a.Perm b) :
    Graffiti324.residueSequence a = Graffiti324.residueSequence b := by
  have sorted : descending a = descending b :=
    descending_of_perm (h.trans (descending_perm b).symm) (descending_sorted b)
  unfold Graffiti324.residueSequence
  rw [h.length_eq]
  cases b.length with
  | zero => exact h.length_eq
  | succ n => rw [residueAux,residueAux,sorted]

private theorem tail_sorted (a b : ℕ) :
    (List.replicate a 1 ++ List.replicate b 0).Pairwise (fun x y => y ≤ x) := by
  rw [List.pairwise_append]
  refine ⟨(List.sorted_replicate _ _).2 (Or.inr le_rfl),
    (List.sorted_replicate _ _).2 (Or.inr le_rfl),?_⟩
  intro x hx y hy
  rw [List.eq_of_mem_replicate hx,List.eq_of_mem_replicate hy]
  decide

/-- Exact terminal phase: each remaining pair of degree-one entries
contributes one more zero to the residue. -/
theorem residue_even_ones (p z : ℕ) :
    Graffiti324.residueSequence (List.replicate (2*p) 1 ++ List.replicate z 0) = z+p := by
  induction p generalizing z with
  | zero =>
    simp only [Nat.mul_zero,List.replicate_zero,List.nil_append,Nat.add_zero]
    have sort : descending (List.replicate z 0) = List.replicate z 0 :=
      descending_of_perm (List.Perm.refl _) ((List.sorted_replicate _ _).2 (Or.inr le_rfl))
    unfold Graffiti324.residueSequence
    rw [List.length_replicate]
    cases z with
    | zero => rfl
    | succ z =>
      rw [residueAux,sort,List.replicate_succ]
      simp
  | succ p ih =>
    let xs := List.replicate (2*(p+1)) 1 ++ List.replicate z 0
    have sort : descending xs = xs := descending_of_perm (List.Perm.refl _) (tail_sorted _ _)
    have len : xs.length = 2*p+z+1+1 := by simp [xs]; omega
    change residueAux xs.length xs = z+(p+1)
    rw [len,residueAux,sort]
    have eq : xs = 1 :: 1 :: (List.replicate (2*p) 1 ++ List.replicate z 0) := by
      have m : 2*(p+1) = 2*p+1+1 := by omega
      simp [xs,m,List.replicate_succ]
    rw [eq]
    change residueAux (2*p+z+1) (0 :: (List.replicate (2*p) 1 ++ List.replicate z 0)) = _
    have perm : (0 :: (List.replicate (2*p) 1 ++ List.replicate z 0)).Perm
        (List.replicate (2*p) 1 ++ List.replicate (z+1) 0) := by
      rw [List.replicate_succ]
      exact (List.perm_middle).symm
    have len' : (0 :: (List.replicate (2*p) 1 ++ List.replicate z 0)).length = 2*p+z+1 := by
      simp
    rw [← len']
    change Graffiti324.residueSequence _ = _
    rw [residue_perm perm,ih]
    omega

/-- If all hubs outrank the pages, one Havel–Hakimi step uses its
degree budget on every remaining hub before decrementing any pages. -/
theorem peel_hub (d : ℕ) (hi lo : List ℕ)
    (ordered : (d :: (hi ++ lo)).Pairwise (fun x y => y ≤ x))
    (positive : 0 < d) (hub_budget : hi.length ≤ d) :
    Graffiti324.residueSequence (d :: (hi ++ lo)) =
      Graffiti324.residueSequence (hi.map Nat.pred ++ hhTail (d-hi.length) lo) := by
  have sort : descending (d :: (hi ++ lo)) = d :: (hi ++ lo) :=
    descending_of_perm (.refl _) ordered
  have split : hhTail d (hi ++ lo) = hi.map Nat.pred ++ hhTail (d-hi.length) lo := by
    simp [hhTail,List.take_append_eq_append_take, List.take_of_length_le hub_budget,
      List.drop_append_eq_append_drop,List.drop_eq_nil_of_le hub_budget,List.append_assoc]
  unfold Graffiti324.residueSequence
  rw [List.length_cons,residueAux,sort]
  change (if d = 0 then (hi ++ lo).length + 1
    else residueAux (hi ++ lo).length (hhTail d (hi ++ lo))) = _
  rw [if_neg (by omega : d ≠ 0),← split,hhTail_length]


/-- The hub stage sorts the two lists separately and spends the head
degree on the remaining hubs before it touches any page. -/
inductive HubPhase : List ℕ → List ℕ → List ℕ → Prop where
  | nil (lo) : HubPhase [] lo lo
  | step {hi lo tail lo' : List ℕ} {d : ℕ}
      (head : descending hi = d :: tail)
      (ordered : ((d :: tail) ++ descending lo).Pairwise (fun x y => y ≤ x))
      (positive : 0 < d) (budget : tail.length ≤ d)
      (next : HubPhase (tail.map Nat.pred) (hhTail (d-tail.length) (descending lo)) lo') :
      HubPhase hi lo lo'

theorem hub_phase_residue {hi lo lo' : List ℕ} (run : HubPhase hi lo lo') :
    Graffiti324.residueSequence (hi ++ lo) = Graffiti324.residueSequence lo' := by
  induction run with
  | nil => rfl
  | @step hi lo tail lo' d hd hsorted hpos hbudget _ ih =>
    have perm : (hi ++ lo).Perm ((d :: tail) ++ descending lo) := by
      rw [← hd]
      exact (descending_perm hi).symm.append (descending_perm lo).symm
    exact (residue_perm perm).trans
      ((peel_hub d tail (descending lo) hsorted hpos hbudget).trans ih)

/-- If the minimum hub degree is at least the hub count plus two and
all page degrees start at most two, Havel–Hakimi peels every hub first. -/
theorem hubs_go_first (hi lo : List ℕ)
    (high : ∀ x ∈ hi, hi.length+2 ≤ x)
    (low : ∀ x ∈ lo, x ≤ 2) :
    ∃ lo', HubPhase hi lo lo' ∧ lo'.length = lo.length ∧ ∀ x ∈ lo', x ≤ 2 := by
  generalize hh : hi.length = n
  induction n generalizing hi lo with
  | zero =>
    have e : hi = [] := List.length_eq_zero_iff.mp hh
    subst hi
    exact ⟨lo,.nil _,rfl,low⟩
  | succ n ih =>
    have hp := descending_perm hi
    have hs := descending_sorted hi
    cases seed : descending hi with
    | nil =>
      rw [seed] at hp
      have hlen := hp.length_eq
      simp at hlen
      omega
    | cons d tail =>
      rw [seed] at hp hs
      have hn : tail.length = n := by
        have := hp.length_eq
        simp at this
        omega
      have order : ((d :: tail) ++ descending lo).Pairwise (fun x y => y ≤ x) := by
        rw [List.pairwise_append]
        refine ⟨hs,descending_sorted lo,?_⟩
        intro a ha b hb
        have A := high a (hp.mem_iff.mp ha)
        have B := low b ((descending_perm lo).mem_iff.mp hb)
        omega
      have D := high d (hp.mem_iff.mp (List.mem_cons_self ..))
      let next := hhTail (d-tail.length) (descending lo)
      have length : next.length = lo.length :=
        (hhTail_length _ _).trans (descending_perm lo).length_eq
      have hlow : ∀ x ∈ next, x ≤ 2 := by
        intro x hx
        unfold next hhTail at hx
        rcases List.mem_append.mp hx with hx|hx
        · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
          have := low j ((descending_perm lo).mem_iff.mp (List.mem_of_mem_take hj))
          simp only [Nat.pred_eq_sub_one]
          omega
        · exact low x ((descending_perm lo).mem_iff.mp (List.mem_of_mem_drop hx))
      have hhigh : ∀ x ∈ tail.map Nat.pred, (tail.map Nat.pred).length + 2 ≤ x := by
        intro x hx
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
        have := high a (hp.mem_iff.mp (List.mem_cons_of_mem _ ha))
        simp only [List.length_map,Nat.pred_eq_sub_one]
        omega
      obtain ⟨out,run,len,loBound⟩ := ih (tail.map Nat.pred) next hhigh hlow (by simpa using hn)
      exact ⟨out,.step seed order (by omega) (by omega) run,len.trans length,loBound⟩

#print axioms residue_perm
#print axioms residue_even_ones
#print axioms peel_hub
#print axioms hub_phase_residue
#print axioms hubs_go_first
end ResiduePhases
