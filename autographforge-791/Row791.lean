import Independent

namespace CubicRainbow791
open SimpleGraph Finset TriangleMatching1078 HallRainbow1121 AutoGraphForge378

private def full (a b c : Fin 4) := ∀ x : Fin 4, x ≠ 0 → a=x ∨ b=x ∨ c=x

private theorem sees {f : V → Fin 4} (rain : Rainbow g f) {v : V} (zero : f v=0) :
    full (f (n0 v)) (f (n1 v)) (f (n2 v)) := by
  intro x hx
  obtain ⟨u,adj,color⟩ := rain v zero x hx
  change u=n0 v ∨ u=n1 v ∨ u=n2 v at adj
  rcases adj with rfl|rfl|rfl
  · exact Or.inl color
  · exact Or.inr (Or.inl color)
  · exact Or.inr (Or.inr color)

private theorem colors_nonzero : ∀ a b c : Fin 4, full a b c →
    a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ≠ b := by unfold full; decide

private theorem unique_third : ∀ a b c d : Fin 4, full a c d → full b c d → a=b := by
  unfold full
  decide

theorem weight_lower {f : V → Fin 4} (rain : Rainbow g f) : 13 ≤ weight f := by
  let Z := univ.filter fun v : V => f v = 0
  have mem {u} : u ∈ Z ↔ f u=0 := by simp [Z]
  have independent : ∀ x ∈ Z, ∀ y ∈ Z, ¬g.Adj x y := by
    intro x hx y hy edge
    have h := colors_nonzero _ _ _ (sees rain (mem.mp hx))
    change y=n0 x ∨ y=n1 x ∨ y=n2 x at edge
    rcases edge with rfl|rfl|rfl
    · exact h.1 (mem.mp hy)
    · exact h.2.1 (mem.mp hy)
    · exact h.2.2.1 (mem.mp hy)
  have count : Z.card + weight f = 20 := by
    simpa [Z,weight] using filter_card_add_filter_neg_card_eq_card (p:=fun v : V => f v=0) (s:=univ)
  apply Classical.byContradiction
  intro small
  have forced := independent_rigid Z independent (by omega)
  have zero (v : V) (h : v ∈ leftSites ∪ rightSites) : f v = 0 := mem.mp (forced ▸ h)
  have h0 : full (f 8) (f 9) (f 18) := sees rain (zero 0 (by decide))
  have h1 : full (f 8) (f 10) (f 11) := sees rain (zero 1 (by decide))
  have h2 : full (f 9) (f 10) (f 11) := sees rain (zero 2 (by decide))
  exact (colors_nonzero _ _ _ h0).2.2.2 (unique_third _ _ _ _ h1 h2)

def labeling : V → Fin 4 := ![1,0,0,3,0,0,0,0,2,2,1,3,2,2,1,3,3,1,0,2]

theorem rainbow_exact : rainbowNumber g 3 = 13 := by
  have feasible : Rainbow g labeling := by unfold Rainbow; decide
  have cost : weight labeling = 13 := by decide
  have upper : rainbowNumber g 3 ≤ 13 := Nat.sInf_le ⟨labeling,cost,feasible⟩
  obtain ⟨f,eq,rain⟩ := Nat.sInf_mem (s:={n | ∃ f : V → Fin 4, weight f=n ∧ Rainbow g f})
    ⟨_,labeling,rfl,feasible⟩
  exact le_antisymm upper ((weight_lower rain).trans_eq eq)

theorem certificate : Fintype.card V = 20 ∧ g.Connected ∧ g.IsRegularOfDegree 3 ∧
    rainbowNumber g 3 = 13 ∧ lineDomination g = 6 ∧ minMaximalMatching g = 6 :=
  ⟨Fintype.card_fin _,connected,cubic,rainbow_exact,match_exact⟩

theorem row791_false : ¬ (∀ (G : SimpleGraph V) [DecidableRel G.Adj], 2 ≤ Fintype.card V →
    G.IsRegularOfDegree 3 → rainbowNumber G 3 ≤ 2*lineDomination G) := by
  intro row
  have contrad := row g (by decide) cubic
  rw [rainbow_exact,match_exact.1] at contrad
  omega

/-- The same connected numerical input falsifies the normalized half-ratio
and both strict converses. Physical line 2733 is a pointer to 791. -/
theorem other_spellings :
    ¬ (1/2 : ℚ)*rainbowNumber g 3 ≤ lineDomination g ∧
    (2:ℚ)*lineDomination g < rainbowNumber g 3 ∧
    (lineDomination g : ℚ) < (1/2 : ℚ)*rainbowNumber g 3 ∧ g.IsRegularOfDegree 3 := by
  rw [rainbow_exact,match_exact.1]
  exact ⟨by norm_num,by norm_num,by norm_num,cubic⟩

#print axioms other_spellings
#print axioms independent_rigid
#print axioms match_exact
#print axioms weight_lower
#print axioms rainbow_exact
#print axioms certificate
#print axioms row791_false
end CubicRainbow791
