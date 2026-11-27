import Chain
import Mathlib.Tactic.Linarith

namespace Chain5169
open SimpleGraph Finset BullCover1125 TriangleMatching1078 Packing2560

/-- A claw-free edge-dominating patch contains two endpoints and at most
three outside vertices. Sum the published row 2560 local bound. -/
theorem five_per_edge {W : Type*} [Fintype W] (G : SimpleGraph W)
    (iso : IsolateFree G) (cl : Free G claw) : Fintype.card W ≤ 5*lineDomination G := by
  classical
  obtain ⟨D,sz,dom⟩ := EulerDom574.line_attained G
  obtain ⟨p⟩ := partition iso dom
  let block (i : ↥D) := insert (p.left i) (insert (p.right i) (p.outside i))
  have all : (univ : Finset W) ⊆ univ.biUnion block := by
    intro v _
    obtain ⟨i,hi⟩ := p.complete v
    exact mem_biUnion.mpr ⟨i,mem_univ _,by simpa [block] using hi⟩
  calc
    Fintype.card W = (univ : Finset W).card := card_univ.symm
    _ ≤ _ := card_le_card all
    _ ≤ ∑ i : ↥D, (block i).card := card_biUnion_le
    _ ≤ ∑ _ : ↥D, 5 := sum_le_sum fun i _ => by
      have ha := card_insert_le (p.left i) (insert (p.right i) (p.outside i))
      have hb := card_insert_le (p.right i) (p.outside i)
      have hc := three_bound cl (p.attached i)
      dsimp [block]
      omega
    _ = _ := by simp [sz,Nat.mul_comm]

/-- Holds whenever the edge-cover size attains the elementary half-order
lower bound. The connected claw-free case is proved in Sharp.lean. -/
theorem minimal_order {W : Type*} [Fintype W] (G : SimpleGraph W) (cl : Free G claw)
    {r : ℕ} (num : edgeCoverValue G = some r) (half : 2*r ≤ Fintype.card W+1)
    (viol : (lineDomination G : ℚ) < (3/5 : ℚ)*r-1) : 13 ≤ Fintype.card W := by
  classical
  have iso : IsolateFree G := by
    by_contra h
    simp [edgeCoverValue,h] at num
  have cap := five_per_edge G iso cl
  have rat : (5:ℚ)*lineDomination G+5 < 3*r := by linarith
  have intBound : 5*lineDomination G+5 < 3*r := by exact_mod_cast rat
  by_contra! small
  have smallCover : r ≤ 6 := by omega
  have cases : lineDomination G = 0 ∨ lineDomination G = 1 ∨ lineDomination G = 2 := by omega
  rcases cases with h|h|h <;> omega

/-- The second normalized spelling at line 3060 is algebraically equivalent. -/
theorem duplicate (g r : ℚ) : (g < (3/5)*r + -1) ↔ (5/3)*g+5/3 < r := by
  constructor <;> intro h <;> linarith

theorem family (k : ℕ) (hk : 3 ≤ k) : (chain k).Connected ∧ Free (chain k) claw ∧
    edgeCoverValue (chain k) = some (2*k+1) ∧ lineDomination (chain k) = k ∧
    ((3/5 : ℚ)*(2*(k:ℚ)+1)-1) - lineDomination (chain k) = ((k:ℚ)-2)/5 ∧
    (lineDomination (chain k) : ℚ) < (3/5 : ℚ)*(2*(k:ℚ)+1) + -1 := by
  have m := (matching_exact k).1
  have h : (3:ℚ) ≤ k := by exact_mod_cast hk
  exact ⟨connected k,claw_free k,cover_exact (by omega),m,by rw [m]; linarith,by rw [m]; linarith⟩

theorem row5169_false : ¬ (∀ (G : SimpleGraph (Fin 13)) (r : ℕ), edgeCoverValue G = some r →
    (lineDomination G : ℚ) < (3/5 : ℚ)*r + -1 → ¬ Free G claw) := by
  intro row
  obtain ⟨_,cl,num,_,_,viol⟩ := family 3 (by decide)
  exact row (chain 3) 7 num (by norm_num at viol ⊢; exact viol) cl

#print axioms matching_exact
#print axioms cover_exact
#print axioms five_per_edge
#print axioms minimal_order
#print axioms duplicate
#print axioms family
#print axioms row5169_false
end Chain5169
