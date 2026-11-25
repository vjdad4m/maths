/- Reproduce with Lean 4.19.0 and Mathlib v4.19.0: in a project pinned to that tag, run `lake env lean Formal310.lean`. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
set_option warningAsError true
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators
namespace Graffiti310
variable {V : Type*} [Fintype V]

def TotalDominates (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

noncomputable def totalDomination (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}

noncomputable def totalDistance (G : SimpleGraph V) (r : V) : ℕ :=
  ∑ v : V, G.dist r v

noncomputable def minTotalDistance (G : SimpleGraph V) : ℕ :=
  sInf (Set.range (totalDistance G))

theorem sum_mono {A : Type*} (s : Finset A) (f g : A → ℕ)
    (h : ∀ x ∈ s, f x ≤ g x) : (∑ x ∈ s, f x) ≤ ∑ x ∈ s, g x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    simp only [Finset.sum_insert ha]
    exact Nat.add_le_add h1 h2

theorem predecessor (G : SimpleGraph V) (hc : G.Connected) (r v : V) (hv : v ≠ r) :
    ∃ w, G.Adj v w ∧ G.dist r w + 1 = G.dist r v := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact False.elim (hv rfl)
  | cons =>
    rename_i w had p
    refine ⟨w,had,?_⟩
    have h₁ : G.dist r w + 1 ≤ G.dist r v := by
      have hl := G.dist_le p
      rw [SimpleGraph.dist_comm] at hl
      have ht : G.dist r v = G.dist v r := SimpleGraph.dist_comm
      rw [SimpleGraph.Walk.length_cons] at hp
      omega
    have h₂ := hc.dist_triangle (u := r) (v := w) (w := v)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr had.symm] at h₂
    omega

theorem parent_exists (G : SimpleGraph V) (hc : G.Connected) (r : V) :
    ∃ parent : V → V, ∀ v, v ≠ r →
      G.Adj v (parent v) ∧ G.dist r (parent v) + 1 = G.dist r v := by
  classical
  have h (v : V) : ∃ w, v ≠ r → G.Adj v w ∧ G.dist r w + 1 = G.dist r v := by
    by_cases hv : v=r
    · exact ⟨r,fun h => False.elim (h hv)⟩
    · obtain ⟨w,hw⟩ := predecessor G hc r v hv
      exact ⟨w, fun _ => hw⟩
  exact ⟨fun v => Classical.choose (h v),fun v => Classical.choose_spec (h v)⟩

theorem levelTwo (G : SimpleGraph V) (r : V)
    (parent : V → V) (hp : ∀ v, v ≠ r →
      G.Adj v (parent v) ∧ G.dist r (parent v) + 1 = G.dist r v)
    (v : V) (hv : 2 ≤ G.dist r v) : ∃ x, G.dist r x = 2 := by
  generalize hd : G.dist r v = d at *
  induction d using Nat.strongRecOn generalizing v with
  | ind d ih =>
    by_cases h2 : d=2
    · exact ⟨v,hd.trans h2⟩
    · have hn : v ≠ r := by intro hh; have hz : G.dist r v = 0 := hh.symm ▸ G.dist_self; omega
      have hh := (hp v hn).2
      exact ih (G.dist r (parent v)) (by omega) (parent v) rfl (by omega)

/-- The BFS charging argument for a root of eccentricity at least two. -/
theorem nonStar (G : SimpleGraph V) (hc : G.Connected)
    (r : V) (hfar : ∃ v, 2 ≤ G.dist r v) :
    ∃ D : Finset V, TotalDominates G D ∧ 3 * (D.card - 1) ≤ totalDistance G r := by
  classical
  obtain ⟨p,hp⟩ := parent_exists G hc r
  let internal : V → Prop := fun v => ∃ w, w ≠ r ∧ p w = v
  let D := Finset.univ.filter internal
  have hD : TotalDominates G D := by
    intro v
    by_cases hv : v=r
    · subst v
      obtain ⟨w,hw⟩ := hfar
      obtain ⟨x,hx⟩ := levelTwo G r p hp w hw
      have hx₀ : x ≠ r := by
        intro he
        have hz : G.dist r x = 0 := he.symm ▸ G.dist_self
        omega
      have hdist : G.dist r (p x) = 1 := by
        have ht := (hp x hx₀).2
        omega
      exact ⟨p x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx₀,rfl⟩,
        SimpleGraph.dist_eq_one_iff_adj.mp hdist⟩
    · exact ⟨p v, Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hv,rfl⟩,(hp v hv).1⟩
  let A := Finset.univ.filter (fun v => internal v ∧ G.dist r v=1)
  let B := Finset.univ.filter (fun v => internal v ∧ 2 ≤ G.dist r v)
  let depthTwo := Finset.univ.filter (fun v => G.dist r v=2)
  let depthThree := Finset.univ.filter (fun v => 3 ≤ G.dist r v)
  let child : V → V := fun v => if h : internal v then Classical.choose h else r
  have hchild (v : V) (h : internal v) : child v ≠ r ∧ p (child v) = v := by
    simp only [child,dif_pos h]
    exact Classical.choose_spec h
  have hstep (v : V) (h : internal v) : G.dist r (child v) = G.dist r v + 1 := by
    rcases hchild v h with ⟨hn,he⟩
    simpa [he] using (hp (child v) hn).2.symm
  have hinj (U : Finset V) (hU : ∀ v ∈ U, internal v) :
      Set.InjOn child (↑U : Set V) := by
    intro v hv w hw heq
    have he₁ := (hchild v (hU v hv)).2
    have he₂ := (hchild w (hU w hw)).2
    exact he₁.symm.trans ((congrArg p heq).trans he₂)
  have hA : A.card ≤ depthTwo.card := by
    apply Finset.card_le_card_of_injOn child _ (hinj A (fun v hv => (Finset.mem_filter.mp hv).2.1))
    intro v hv
    have hi := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hstep v hi.1, hi.2]⟩
  have hB : B.card ≤ depthThree.card := by
    apply Finset.card_le_card_of_injOn child _ (hinj B (fun v hv => (Finset.mem_filter.mp hv).2.1))
    intro v hv
    have hi := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hstep v hi.1]; omega⟩
  have hDab : D.card ≤ 1+A.card+B.card := by
    have hs : D ⊆ insert r (A ∪ B) := by
      intro v hv
      by_cases he : v=r
      · exact Finset.mem_insert.mpr (Or.inl he)
      · apply Finset.mem_insert_of_mem
        have hi := (Finset.mem_filter.mp hv).2
        have hpos := hc.pos_dist_of_ne (u := r) (v := v) (Ne.symm he)
        by_cases h₁ : G.dist r v=1
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,h₁⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,by omega⟩))
    have h₁ := Finset.card_le_card hs
    have h₂ := Finset.card_insert_le r (A ∪ B)
    have h₃ := Finset.card_union_le A B
    omega
  let charge : V → ℕ := fun v =>
    (if internal v ∧ G.dist r v=1 then 1 else 0) +
    (if G.dist r v=2 then 2 else 0) + (if 3 ≤ G.dist r v then 3 else 0)
  have hcharge (v : V) : charge v ≤ G.dist r v := by
    dsimp [charge]
    split <;> split <;> split <;> omega
  have hsum : (∑ v : V, charge v) = A.card+2*depthTwo.card+3*depthThree.card := by
    have hh₁ := Finset.sum_filter (s := (Finset.univ : Finset V))
      (fun v => internal v ∧ G.dist r v=1) (fun _ => (1 : ℕ))
    have hh₂ := Finset.sum_filter (s := (Finset.univ : Finset V))
      (fun v => G.dist r v=2) (fun _ => (2 : ℕ))
    have hh₃ := Finset.sum_filter (s := (Finset.univ : Finset V))
      (fun v => 3 ≤ G.dist r v) (fun _ => (3 : ℕ))
    unfold charge
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hh₁, ← hh₂, ← hh₃]
    simp only [Finset.sum_const, nsmul_eq_mul]
    change A.card * 1 + depthTwo.card * 2 + depthThree.card * 3 = _
    omega
  have htotal := sum_mono Finset.univ charge (G.dist r) (fun v _ => hcharge v)
  rw [hsum] at htotal
  exact ⟨D,hD,by unfold totalDistance; omega⟩

theorem starCase (G : SimpleGraph V) (hc : G.Connected) (hn : 2 < Fintype.card V)
    (r : V) (hstar : ∀ v, G.dist r v ≤ 1) :
    ∃ D : Finset V, TotalDominates G D ∧ D.card ≤ 1+(totalDistance G r + 2)/3 := by
  classical
  obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) r
  have had (v : V) (hv : v ≠ r) : G.Adj r v := by
    have hpos := hc.pos_dist_of_ne (u := r) (v := v) (Ne.symm hv)
    exact SimpleGraph.dist_eq_one_iff_adj.mp (by have h := hstar v; omega)
  have hsum : Fintype.card V - 1 ≤ totalDistance G r := by
    let C := (Finset.univ : Finset V).erase r
    have hC : C.card = Fintype.card V - 1 := by
      simp [C, Finset.card_erase_of_mem (Finset.mem_univ _)]
    have hEq : C = Finset.univ.filter (fun v => v ≠ r) := by
      ext v
      simp [C]
    have hh := Finset.sum_filter (s := (Finset.univ : Finset V)) (fun v => v ≠ r)
      (fun _ => (1 : ℕ))
    rw [← hEq] at hh
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one, hC] at hh
    change Fintype.card V - 1 = (∑ a : V, if a ≠ r then (1 : ℕ) else 0) at hh
    rw [hh]
    unfold totalDistance
    apply sum_mono
    intro v _
    by_cases h : v=r
    · simp [h]
    · have hpos := hc.pos_dist_of_ne (u := r) (v := v) (Ne.symm h)
      simpa [h] using hpos
  let D : Finset V := {r,w}
  refine ⟨D, ?_, ?_⟩
  · intro v
    by_cases hv : v=r
    · subst v
      exact ⟨w,by simp [D],had _ hw⟩
    · exact ⟨r,by simp [D],(had _ hv).symm⟩
  · have hcard : D.card=2 := by simp [D,Ne.symm hw]
    omega

/-- The exact rounded conjecture, stated with the least total-distance sum,
and total domination number defined as the least cardinal of a total dominating set. -/
theorem conjecture310 (G : SimpleGraph V) (hc : G.Connected) (hn : 2 < Fintype.card V) :
    totalDomination G ≤ 1 + (minTotalDistance G + 2)/3 := by
  classical
  have hex : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  letI := hex
  have hne : (Set.range (totalDistance G)).Nonempty :=
    ⟨_, ⟨Classical.choice hex,rfl⟩⟩
  obtain ⟨r, hr⟩ := Nat.sInf_mem hne
  have hm : totalDistance G r = minTotalDistance G := hr
  by_cases hfar : ∃ v, 2 ≤ G.dist r v
  · obtain ⟨D,hd,hcard⟩ := nonStar G hc r hfar
    have hb : totalDomination G ≤ D.card := Nat.sInf_le ⟨D,hd,rfl⟩
    omega
  · have hstar (v : V) : G.dist r v ≤ 1 := by
      by_cases h : 2 ≤ G.dist r v
      · exact False.elim (hfar ⟨v,h⟩)
      · omega
    obtain ⟨D,hd,hcard⟩ := starCase G hc hn r hstar
    have hb : totalDomination G ≤ D.card := Nat.sInf_le ⟨D,hd,rfl⟩
    omega

#print axioms conjecture310
end Graffiti310
