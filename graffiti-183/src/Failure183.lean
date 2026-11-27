import SixBound183
import Dominated183
import Components185

namespace Graffiti183.Exceptional
open SimpleGraph Finset Short177

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Nontrivial V] in
lemma claw_free_of_failure (hc : G.Connected) (hf : ¬ Graffiti183.Claim183 G) :
    ClawFree G := by
  classical
  intro c x y z ex ey ez nxy nxz nyz xy xz
  by_contra yz
  let A : Finset V := {x,y,z}
  have hsub : A ⊆ G.neighborFinset c := by
    intro u hu
    simp only [A,mem_insert,mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr ex
    · exact (G.mem_neighborFinset _ _).mpr ey
    · exact (G.mem_neighborFinset _ _).mpr ez
  have ind : Short177.Indep G A := by
    intro a ha b hb ne e
    simp only [A,mem_insert,mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact ne rfl
    · exact xy e
    · exact xz e
    · exact xy e.symm
    · exact ne rfl
    · exact yz e
    · exact xz e.symm
    · exact yz e.symm
    · exact ne rfl
  have hcard : A.card = 3 := by simp [A,nxy,nxz,nyz]
  have hl : 3 ≤ Graffiti179.localInd G c := by
    rw [←hcard]
    unfold Graffiti179.localInd
    exact le_sup (s := (G.neighborFinset c).powerset.filter (Short177.Indep G)) (f:=Finset.card)
      (mem_filter.mpr ⟨mem_powerset.mpr hsub,ind⟩)
  have hm : 3 ≤ Graffiti179.lambda G := hl.trans (le_sup (f:=Graffiti179.localInd G) (mem_univ c))
  have h := (Graffiti179.order_add_two G hc hm).trans
    (Nat.add_le_add (Graffiti185.Reuse.leaves_bridge G) (Graffiti185.Reuse.bipartite_bridge G))
  have hM := Graffiti183.metric_upper_bound hc
  exact hf (hM.trans h)

theorem conjecture183_of_cut (hc : G.Connected) (r : V)
    (hr : 2 ≤ Nat.card (Graffiti185.Cut.Deleted G r).ConnectedComponent) :
    Graffiti183.Claim183 G := by
  have h := Graffiti185.Cut.bound_delete_components G r hc
  have h2 : Fintype.card V + 2 ≤ Graffiti183.maxLeaves G + Graffiti183.bipartiteNumber G :=
    (Nat.add_le_add_left hr _).trans h
  exact (Graffiti183.metric_upper_bound hc).trans h2

omit [Nontrivial V] in
theorem conjecture183_of_strict_adjacent_domination (hc : G.Connected)
    {w q z : V} (hwq : G.Adj w q) (hqz : G.Adj q z)
    (hwz : ¬G.Adj w z) (hnez : w ≠ z)
    (hinc : ∀ x, G.Adj w x → x ≠ q → G.Adj q x) :
    Graffiti183.Claim183 G :=
  (Graffiti183.metric_upper_bound hc).trans
     (order_two_of_strict_adjacent_domination G hc hwq hqz hwz hnez hinc)

theorem failure_constraints (hc : G.Connected) (hf : ¬ Claim183 G) :
    ClawFree G ∧
    (∀ r, Nat.card (Graffiti185.Cut.Deleted G r).ConnectedComponent ≤ 1) ∧
    Graffiti183.maxLeaves G + 5 ≤ Fintype.card V ∧
    6 ≤ Graffiti183.bipartiteNumber G ∧
    (∀ {w q}, G.Adj w q → (∀ x, G.Adj w x → x ≠ q → G.Adj q x) →
      ∀ z, G.Adj q z → w ≠ z → G.Adj w z) := by
  have hclaw : ClawFree G := claw_free_of_failure G hc hf
  obtain ⟨⟨hrad,v,w,hd,hu⟩,hb⟩ :=
    (Graffiti183.conjecture183_failure_iff hc (Graffiti185.Reuse.order_bound G hc)).mp hf
  obtain ⟨p⟩ := exists_six_pattern hc hclaw (by omega) hd hu
  have h6 := bipartite_at_least_six p
  refine ⟨hclaw,?_,by omega,h6,?_⟩
  · intro r
    by_cases h : Nat.card (Graffiti185.Cut.Deleted G r).ConnectedComponent ≤ 1
    · exact h
    · exact False.elim (hf (conjecture183_of_cut G hc r (by omega)))
  · intro w q e ineq z ez hne
    by_cases hno : G.Adj w z
    · exact hno
    · exact False.elim (hf (conjecture183_of_strict_adjacent_domination G hc e ez hno hne ineq))

#print axioms failure_constraints
#print axioms conjecture183_of_cut

end Graffiti183.Exceptional
