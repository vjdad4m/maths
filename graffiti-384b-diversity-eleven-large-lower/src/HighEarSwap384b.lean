import HighEarRetained384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Replace one omitted ear by both its kept anchors. The ear is restored;
each anchor has an additional retained neighbor, and no other omitted
vertex depends on either anchor. -/
theorem exact_of_ear_swap (t : (types G).card=11)
    {O : Finset V} (five : 5≤O.card)
    (good : TwoDominates G Oᶜ)
    {e a b : V} (he : e∈O) (ha : a∉O) (hb : b∉O) (ab : a≠b)
    (ae : G.Adj a e) (be : G.Adj b e)
    (left : ∃ x∉O, x≠a ∧ x≠b ∧ G.Adj a x)
    (right : ∃ x∉O, x≠a ∧ x≠b ∧ G.Adj b x)
    (alone : ∀ z∈O, z≠e → ¬G.Adj z a ∧ ¬G.Adj z b) :
    gamma G≤bound G := by
  classical
  let T := insert a (insert b (O.erase e))
  have memT (x : V) : x∈T ↔ x=a ∨ x=b ∨ (x≠e ∧ x∈O) := by
    simp [T]
  have six : 6≤T.card := by
    have na : a∉insert b (O.erase e) := by simp [ab,ha]
    have nb : b∉O.erase e := by simp [hb]
    rw [show T=insert a (insert b (O.erase e)) by rfl,
      card_insert_of_not_mem na,card_insert_of_not_mem nb,card_erase_of_mem he]
    omega
  have ec : e∈Tᶜ := by
    rw [mem_compl,memT]
    exact fun h => h.elim (fun h => ha (h ▸ he))
      (fun h => h.elim (fun h => hb (h ▸ he)) (fun h => h.1 rfl))
  have witness (u : V) (ue : G.Adj u e)
      (extra : ∃ x∉O, x≠a ∧ x≠b ∧ G.Adj u x) : 2≤nbr G u Tᶜ := by
    obtain ⟨x,xO,xa,xb,ux⟩ := extra
    have xc : x∈Tᶜ := by simp [mem_compl,memT,xa,xb,xO]
    have neq : e≠x := fun h=>xO (h ▸ he)
    have inc : ({e,x} : Finset V) ⊆ Tᶜ.filter (G.Adj u) :=
      insert_subset (mem_filter.mpr ⟨ec,ue⟩)
        (singleton_subset_iff.mpr (mem_filter.mpr ⟨xc,ux⟩))
    simpa [nbr,card_pair neq] using card_le_card inc
  have dom : TwoDominates G Tᶜ := by
    intro z hz
    have zt : z∈T := by simpa using hz
    rcases (memT z).mp zt with rfl|rfl|⟨ze,zo⟩
    · exact witness _ ae left
    · exact witness _ be right
    have inc : Oᶜ.filter (G.Adj z) ⊆ Tᶜ.filter (G.Adj z) := by
      intro x hx
      obtain ⟨xo,zx⟩ := mem_filter.mp hx
      apply mem_filter.mpr
      refine ⟨?_,zx⟩
      rw [mem_compl,memT]
      rintro (rfl|rfl|⟨_,xO⟩)
      · exact (alone z zo ze).1 zx
      · exact (alone z zo ze).2 zx
      · exact (mem_compl.mp xo) xO
    exact (good z (by simpa using zo)).trans (card_le_card inc)
  have gm : gamma G≤(Tᶜ).card :=
    Nat.sInf_le (s := {k : ℕ | ∃ d, TwoDominates G d ∧ d.card=k}) ⟨Tᶜ,dom,rfl⟩
  rw [card_compl] at gm
  unfold bound
  rw [t]
  omega

#print axioms exact_of_ear_swap
end Graffiti384b.DiversityEleven
