import Partial133

namespace Graffiti133Pentagon
open SimpleGraph Graffiti133 Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

def pent (i j : Fin 5) : Prop := i + 1 = j ∨ j + 1 = i
private instance : DecidableRel pent := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private lemma pent_alt : ∀ i j : Fin 5, i ≠ j → ¬pent i j →
    ∃ a b, a ≠ j ∧ b ≠ i ∧ pent i a ∧ pent a b ∧ pent b j := by decide

private def reserved (b : Fin 5 → Bool) (i j : Fin 6) : Prop :=
  if hi : i.val < 5 then
    if hj : j.val < 5 then pent ⟨i.val,hi⟩ ⟨j.val,hj⟩
    else b ⟨i.val,hi⟩ = true
  else if hj : j.val < 5 then b ⟨j.val,hj⟩ = true else False
private instance (b : Fin 5 → Bool) : DecidableRel (reserved b) := by
  intro i j
  unfold reserved
  split <;> split <;> infer_instance

private def spokePath (i : Fin 5) (positive : Bool) : Fin 5 → Fin 6 :=
  ![5, i.castSucc, (i + (if positive then 1 else 4)).castSucc,
    (i + (if positive then 2 else 3)).castSucc, (i + (if positive then 3 else 2)).castSucc]

private lemma computed_spokePath : ∀ b : Fin 5 → Bool,
    (∀ i, b i = true → b (i+2) = false) → (∃ i, b i = true) →
    ∃ i pos,
      (∀ u v : Fin 5, spokePath i pos u = spokePath i pos v → u = v) ∧
      ∀ u v : Fin 5, u < v → (reserved b (spokePath i pos u) (spokePath i pos v) ↔
        u.val + 1 = v.val) := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem cycle_pentagon (h4 : FourCycleFree G) {c : Fin 5 → V}
    (inj : Function.Injective c) (sides : ∀ i, G.Adj (c i) (c (i+1))) :
    ∀ i j, G.Adj (c i) (c j) ↔ pent i j := by
  have forward (i j : Fin 5) (h : pent i j) : G.Adj (c i) (c j) := by
    rcases h with e | e
    · exact e ▸ sides i
    · exact e ▸ (sides j).symm
  intro i j
  refine ⟨?_,forward i j⟩
  intro e
  apply Classical.byContradiction
  intro no
  obtain ⟨a,b,ha,hb,e1,e2,e3⟩ := pent_alt i j (fun h => e.ne (congrArg c h)) no
  have eq := h4 (c i) (c b) (c a) (c j) (fun h => hb (inj h).symm)
    (forward _ _ e1) (forward _ _ e2).symm e (forward _ _ e3)
  exact ha (inj eq)

theorem extend_pentagon (h4 : FourCycleFree G) {c : Fin 5 → V}
    (inj : Function.Injective c) (hcycle : ∀ i j, G.Adj (c i) (c j) ↔ pent i j)
    (x : V) (hx : ∀ i, x ≠ c i) (ha : ∃ i, G.Adj x (c i)) :
    ∃ f : Fin 5 → V, InducedPath G f ∧ f 0 = x ∧
      (∀ i : Fin 5, 0 < i.val → ∃ j : Fin 5, f i = c j) := by
  classical
  let b : Fin 5 → Bool := fun i => decide (G.Adj x (c i))
  have btrue (i : Fin 5) : b i = true ↔ G.Adj x (c i) := by simp [b]
  have d2 (i : Fin 5) (h : b i = true) : b (i+2) = false := by
    cases e : b (i+2)
    · rfl
    · have e1 : pent i (i+1) := Or.inl rfl
      have e2 : pent (i+1) (i+2) := Or.inl (by fin_cases i <;> decide)
      have eq := h4 (c i) (c (i+2)) x (c (i+1))
        (fun w => (show i ≠ i+2 by fin_cases i <;> decide) (inj w))
        ((btrue _).mp h).symm ((btrue _).mp e).symm
        ((hcycle _ _).mpr e1) ((hcycle _ _).mpr e2).symm
      exact False.elim (hx _ eq)
  obtain ⟨i,pos,hi,hs⟩ := computed_spokePath b d2 (by
    obtain ⟨i,he⟩ := ha
    exact ⟨i,(btrue _).mpr he⟩)
  let g (r : Fin 6) : V := if hr : r.val < 5 then c ⟨r.val,hr⟩ else x
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < 5 <;> by_cases hB : b.val < 5
    · have he := inj (show c ⟨a.val,hA⟩ = c ⟨b.val,hB⟩ by simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun t : Fin 5 => t.val) he)
    · exact False.elim (hx ⟨a.val,hA⟩ (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm))
    · exact False.elim (hx ⟨b.val,hB⟩ (by simpa only [g,dif_neg hA,dif_pos hB] using eq))
    · apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
  have hrel (a q : Fin 6) : G.Adj (g a) (g q) ↔ reserved b a q := by
    by_cases hA : a.val < 5 <;> by_cases hQ : q.val < 5
    · simpa only [g,reserved,dif_pos hA,dif_pos hQ] using hcycle ⟨a.val,hA⟩ ⟨q.val,hQ⟩
    · simpa only [g,reserved,dif_pos hA,dif_neg hQ,G.adj_comm] using (btrue ⟨a.val,hA⟩).symm
    · simpa only [g,reserved,dif_neg hA,dif_pos hQ] using (btrue ⟨q.val,hQ⟩).symm
    · simp [g,reserved,hA,hQ]
  refine ⟨g ∘ spokePath i pos,⟨ginj.comp hi,fun a q he => (hrel _ _).trans (hs a q he)⟩,rfl,?_⟩
  intro j hj
  have hbase : ∀ a pos (j : Fin 5), 0 < j.val → (spokePath a pos j).val < 5 := by decide
  have lt := hbase i pos j hj
  exact ⟨⟨_,lt⟩,dif_pos lt⟩


end Graffiti133Pentagon
