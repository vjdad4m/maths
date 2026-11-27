import FlankRules

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private def extendedFun {n k : ℕ} (f : Fin (n+1) ↪ V) (x : Fin k ↪ V) : Fin ((n+1)+k) → V :=
  Fin.addCases f x

private theorem extendedFun_left {n k : ℕ} (f : Fin (n+1) ↪ V) (x : Fin k ↪ V) (i : Fin (n+1)) :
    extendedFun f x (Fin.castAdd k i) = f i := by
  unfold extendedFun
  exact Fin.addCases_left i

private theorem extendedFun_right {n k : ℕ} (f : Fin (n+1) ↪ V) (x : Fin k ↪ V) (j : Fin k) :
    extendedFun f x (Fin.natAdd (n+1) j) = x j := by
  unfold extendedFun
  exact Fin.addCases_right j

/-- The outside labels can be appended to the eight core labels. -/
def extend {n k : ℕ} (f : Fin (n+1) ↪ V) (x : Fin k ↪ V)
    (off : ∀ i j, x j ≠ f i) : Fin ((n+1)+k) ↪ V where
  toFun := extendedFun f x
  inj' := by
    intro i
    refine Fin.addCases (m := n+1) (n := k) (motive := fun i => ∀ j,
      extendedFun f x i = extendedFun f x j → i = j) ?_ ?_ i
    · intro a u
      refine Fin.addCases (m := n+1) (n := k) ?_ ?_ u
      · intro b h
        have eq : f a = f b := by simpa only [extendedFun_left] using h
        rw [f.injective eq]
      · intro b h
        exact (off a b (by simpa only [extendedFun_left,extendedFun_right] using h.symm)).elim
    · intro a u
      refine Fin.addCases (m := n+1) (n := k) ?_ ?_ u
      · intro b h
        exact (off b a (by simpa only [extendedFun_left,extendedFun_right] using h)).elim
      · intro b h
        have eq : x a = x b := by simpa only [extendedFun_right] using h
        rw [x.injective eq]

@[simp] theorem extend_left {n k : ℕ} (f : Fin (n+1) ↪ V) (x : Fin k ↪ V) (off) (i : Fin (n+1)) :
    extend f x off (Fin.castAdd k i) = f i := extendedFun_left f x i

@[simp] theorem extend_right {n k : ℕ} (f : Fin (n+1) ↪ V) (x : Fin k ↪ V) (off) (j : Fin k) :
    extend f x off (Fin.natAdd (n+1) j) = x j := extendedFun_right f x j

def ProfileAt {n : ℕ} (G : SimpleGraph V) (f : Fin (n+1) ↪ V) (v : V) (m : ℕ) : Prop :=
  ∀ i, G.Adj v (f i) ↔ touch m i = true

theorem extension_chart {n k : ℕ} {f : Fin (n+1) ↪ V} {x : Fin k ↪ V} {off}
    {e : Fin (n+1) → Fin (n+1) → Bool} {m : Fin k → ℕ} {b : Fin k → Fin k → Bool}
    (core : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (profiles : ∀ j, ProfileAt G f (x j) (m j))
    (links : ∀ u v, G.Adj (x u) (x v) ↔ b u v = true) :
    ∀ i j, G.Adj (extend f x off i) (extend f x off j) ↔ extension e m b i j = true := by
  apply Fin.addCases
  · intro i
    apply Fin.addCases
    · intro j
      simpa only [extend_left,extension,Fin.addCases_left] using core i j
    · intro j
      simpa only [extend_left,extend_right,extension,Fin.addCases_left,Fin.addCases_right,G.adj_comm]
        using profiles j i
  · intro i
    apply Fin.addCases
    · intro j
      simpa only [extend_left,extend_right,extension,Fin.addCases_left,Fin.addCases_right]
        using profiles i j
    · intro j
      simpa only [extend_right,extension,Fin.addCases_right] using links i j

theorem external_profile [DecidableEq V] [DecidableRel G.Adj] [Fintype V] {n : ℕ}
    (budget : Catalogue.treeNumber G ≤ 5) {f : Fin (n+1) ↪ V} {mate : Fin (n+1)}
    {e : Fin (n+1) → Fin (n+1) → Bool} (rules : FlankRules n e mate) {v : V}
    (core : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true) (outside : ∀ i, v ≠ f i)
    (offZ : ¬ G.Adj v (f (Fin.last n))) (offMate : ¬ G.Adj v (f mate)) :
    ∃ m ∈ rules.profiles, ProfileAt G f v m := by
  let flags := fun i : Fin (n+1) => decide (G.Adj v (f i))
  let row := encode flags
  have atRow : ProfileAt G f v row := fun i => by
    unfold touch row
    rw [encode_bit flags i]
    simp [flags]
  have offz : touch row (Fin.last n) = false :=
    Bool.eq_false_iff.mpr (fun e => offZ ((atRow _).mpr e))
  have offm : touch row mate = false :=
    Bool.eq_false_iff.mpr (fun e => offMate ((atRow _).mpr e))
  rcases rules.single row offz offm with ⟨T,tree⟩|⟨m,ok,agree⟩
  · let x : Fin 1 ↪ V := ⟨fun _ => v,fun _ _ _ => Subsingleton.elim _ _⟩
    let g := extend f x (fun i _ => outside i)
    have chart : ∀ i j, G.Adj (g i) (g j) ↔ singleEdge e row i j = true :=
      extension_chart core (fun _ => atRow) (fun _ _ => by simp [x,singleLinks])
    exact (CompactOmission.six_tree_absurd budget chart tree).elim
  · exact ⟨m,ok,fun i => (atRow i).trans (by rw [agree i])⟩

theorem block_head {n : ℕ} (f : Fin (n+1) ↪ V) (pos : 0 < n) :
    (block f).head? = some (f 0) := by
  cases n with
  | zero => omega
  | succ n => simp [block,List.finRange_succ]

theorem block_last {n : ℕ} (f : Fin (n+1) ↪ V) (pos : 0 < n) :
    (block f).getLast? = some (f (rightEnd n)) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [block,List.finRange_succ_last,List.map_append,List.getLast?_append_of_ne_nil _ (by simp)]
    rfl

end Graffiti199Depleted.WiderOmission
