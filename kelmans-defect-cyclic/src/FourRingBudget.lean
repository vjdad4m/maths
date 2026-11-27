import NearPerfectEquivalence

open Finset
namespace KelmansCactus.FourRingBudget
open ThreePort

abbrev Slot := Bool × Bool

def left (w : Slot→ℕ) := w (false,false)+w (false,true)
def right (w : Slot→ℕ) := w (true,false)+w (true,true)

/-- The width pairs that could occur in a zero-hole
nonrecoverable cell: local cell size is 1 mod 3, width one
is recoverable, and (total 2 | total 2) is recoverable. -/
def BadHalves (w : Slot→ℕ) : Prop :=
  (∀ s,w s≤2) ∧ (left w+right w)%3=1 ∧ left w+right w≠1 ∧
    ¬(left w=2 ∧ right w=2)

def Transit (l n : ℕ) : Prop :=
  (l=0 ∧ n=2) ∨ (l=1 ∧ n=3) ∨ (l=3 ∧ n=2) ∨
    (l=4 ∧ (n=0 ∨ n=3))

private theorem only_transition {a b : Slot→ℕ} (h : BadHalves a)
    (lower : Opposite (a (true,false)) (b (false,false)))
    (upper : Opposite (a (true,true)) (b (false,true))) :
    Transit (left a) (left b) := by
  obtain ⟨bounds,mod,diff,bal⟩ := h
  have al : left a≤4 := by
    have x:=bounds (false,false)
    have y:=bounds (false,true)
    unfold left
    omega
  change (left a+(a (true,false)+a (true,true)))%3=1 at mod
  change left a+(a (true,false)+a (true,true))≠1 at diff
  change ¬(left a=2 ∧ a (true,false)+a (true,true)=2) at bal
  rcases lower with ⟨x1,y1⟩|⟨x1,x2,y1,y2,s1⟩ <;>
    rcases upper with ⟨x3,y3⟩|⟨x3,x4,y3,y4,s2⟩ <;>
    simp only [Transit,left] at * <;> omega

theorem no_three_transitions {a b c d : ℕ}
    (ab : Transit a b) (bc : Transit b c) (cd : Transit c d) : False := by
  unfold Transit at *
  omega

/-- In the paired-ring routing, no three consecutive cells can
all be fully covered with locally nonrecoverable capped states.
The routing may be any permutation; it need not be one cycle. -/
theorem no_three_good {J : Type*} (next : Equiv.Perm J) (w : J→Slot→ℕ)
    (symmetric : ∀ i bit, Opposite (w i (true,bit)) (w (next i) (false,bit)))
    {i : J} (a : BadHalves (w i)) (b : BadHalves (w (next i)))
    (c : BadHalves (w (next (next i)))) : False := by
  have tr {x : J} (t : BadHalves (w x)) : Transit (left (w x)) (left (w (next x))) :=
    only_transition t (symmetric x false) (symmetric x true)
  exact no_three_transitions (tr a) (tr b) (tr c)

theorem ring_budget {J : Type*} [Fintype J] [DecidableEq J]
    (next : Equiv.Perm J) (w : J→Slot→ℕ)
    (symmetric : ∀ i bit, Opposite (w i (true,bit)) (w (next i) (false,bit)))
    (defective : Finset J) (good : ∀ i∉defective,BadHalves (w i)) :
    Fintype.card J≤3*defective.card := by
  classical
  have badInTriple (i : J) :
      i∈defective ∨ next i∈defective ∨ next (next i)∈defective := by
    by_contra! n
    exact no_three_good next w symmetric (good _ n.1) (good _ n.2.1) (good _ n.2.2)
  let D₁ := defective.image next.symm
  let D₂ := defective.image (next.symm ∘ next.symm)
  have covers : (univ : Finset J) ⊆ defective∪D₁∪D₂ := by
    intro i _
    rcases badInTriple i with hit|hit|hit
    · exact mem_union_left _ (mem_union_left _ hit)
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨next i,hit,next.symm_apply_apply _⟩))
    · exact mem_union_right _ (mem_image.mpr ⟨next (next i),hit,by simp⟩)
  have n₁ : D₁.card=defective.card := card_image_of_injective _ next.symm.injective
  have n₂ : D₂.card=defective.card := card_image_of_injective _ (next.symm.injective.comp next.symm.injective)
  have n := card_le_card covers
  rw [card_univ] at n
  have union₁ := card_union_le defective D₁
  have union₂ := card_union_le (defective∪D₁) D₂
  omega

#print axioms no_three_good
#print axioms ring_budget
end KelmansCactus.FourRingBudget
