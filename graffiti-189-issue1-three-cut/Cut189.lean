import Base189
namespace Issue189
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
/-- Full union of the bags indexed by `s`. -/
def liftB (s : Finset I) : Finset V := Finset.univ.filter (fun v => bag v ∈ s)
/-- Bags outside `q` with some base edge into `q`. -/
def Bdry (q : Finset I) : Finset I := Finset.univ.filter (fun j =>
  j ∉ q ∧ ∃ i : I, i ∈ q ∧ touch i j)
def xyZ : Finset V := liftB {5,6,7}
/-- Every boundary separating two surviving bags contains a whole listed separator.
This checks only the eight-bag base, not 2^34 vertex deletion sets. -/
theorem quotient : ∀ u : Finset I, u.Nonempty → (∃ j : I, j ∉ u ∧ j ∉ Bdry u) →
    ({0,7} : Finset I) ⊆ Bdry u ∨ ({2,7} : Finset I) ⊆ Bdry u ∨
    ({0,3,4} : Finset I) ⊆ Bdry u ∨ ({5,6,7} : Finset I) ⊆ Bdry u := by decide
theorem weights : (liftB {0,7}).card = 14 ∧ (liftB {2,7}).card = 14 ∧
    (liftB {0,3,4}).card = 15 ∧ xyZ.card = 13 := by decide
/-- A deletion is a separator if its complement splits into two nonempty
sides with no edge between them. -/
def Separates (s : Finset V) := ∃ u : Finset V, u.Nonempty ∧ Disjoint u s ∧
    (∃ v, v ∉ u ∧ v ∉ s) ∧ ∀ a ∈ u, ∀ b ∉ u, b ∉ s → ¬ G.Adj a b
theorem lift_mono {a b : Finset I} (hab : a ⊆ b) : liftB a ⊆ liftB b := by
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab (Finset.mem_filter.mp hx).2⟩
theorem unique_small_cut (s : Finset V) (hs : Separates s) (hc : s.card ≤ 13) : s = xyZ := by
  obtain ⟨u, ⟨w,hw⟩, _, ⟨v,vu,vs⟩, h⟩ := hs
  let q := u.image bag
  have out {b : V} (bu : b ∉ u) (bs : b ∉ s) : bag b ∉ q := by
    intro eq
    obtain ⟨a,au,ab⟩ := Finset.mem_image.mp eq
    exact h a au b bu bs ⟨fun e => bu (e ▸ au), Or.inl ab⟩
  have bsub : liftB (Bdry q) ⊆ s := by
    intro b hb
    have bh := (Finset.mem_filter.mp ((Finset.mem_filter.mp hb).2)).2
    obtain ⟨i,iq,ij⟩ := bh.2
    obtain ⟨a,au,ab⟩ := Finset.mem_image.mp iq
    have bu : b ∉ u := fun hu => bh.1 (Finset.mem_image.mpr ⟨b,hu,rfl⟩)
    by_contra bs
    exact h a au b bu bs ⟨fun e => bu (e ▸ au), Or.inr (ab ▸ ij)⟩
  have nb : bag v ∉ Bdry q := fun hf => vs (bsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩))
  have qq := quotient q ⟨bag w,Finset.mem_image.mpr ⟨w,hw,rfl⟩⟩ ⟨bag v,out vu vs,nb⟩
  rcases weights with ⟨w1,w2,w3,w4⟩
  rcases qq with h1|h2|h3|h4
  · have hh := Finset.card_le_card ((lift_mono h1).trans bsub)
    omega
  · have hh := Finset.card_le_card ((lift_mono h2).trans bsub)
    omega
  · have hh := Finset.card_le_card ((lift_mono h3).trans bsub)
    omega
  · exact (Finset.eq_of_subset_of_card_le ((lift_mono h4).trans bsub) (w4 ▸ hc : s.card ≤ xyZ.card)).symm
end Issue189
