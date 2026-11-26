import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! Written on the Wall II, #315. Independent Lean formalization of the
structural proof by Jonas J. Gebendorfer, "Three Well-Total-Domination
Conjectures from the Written on the Wall II List", 28 July 2026:
https://www.researchgate.net/publication/411012117_Three_Well-Total-Domination_Conjectures_from_the_Written_on_the_Wall_II_List_Structural_resolutions_of_Conjectures_315_317_and_322
Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf
-/

namespace Graffiti315
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def TotalDominating (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x, ∃ y ∈ S, G.Adj x y

def WellTotalDominated (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, TotalDominating G S →
    (∀ T ⊆ S, TotalDominating G T → T = S) →
      ∀ T : Finset V, TotalDominating G T → S.card ≤ T.card

omit [Fintype V] in
private theorem total_dom_card_ge_two {G : SimpleGraph V} [Nonempty V]
    {T : Finset V} (hT : TotalDominating G T) : 2 ≤ T.card := by
  obtain ⟨a,ha,_⟩ := hT (Classical.choice ‹Nonempty V›)
  obtain ⟨b,hb,he⟩ := hT a
  have h : ({a,b} : Finset V) ⊆ T := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact ha
    · simpa only [mem_singleton.mp hz] using hb
  have hh := card_le_card h
  simpa [he.ne] using hh

omit [Fintype V] [DecidableEq V] in
private theorem walk_closed {G : SimpleGraph V} {P : V → Prop}
    (hstep : ∀ {a b}, G.Adj a b → P a → P b) {a b : V}
    (p : G.Walk a b) (ha : P a) : P b := by
  induction p with
  | nil => exact ha
  | cons h q ih => exact ih (hstep h ha)

omit [DecidableEq V] in
private theorem unique_leaf_neighbor {G : SimpleGraph V} [DecidableRel G.Adj]
    {x a b : V} (h : G.degree x = 1) (ha : G.Adj x a) (hb : G.Adj x b) : a = b := by
  apply card_le_one.mp (show (G.neighborFinset x).card ≤ 1 by rw [card_neighborFinset_eq_degree,h])
  · exact (G.mem_neighborFinset _ _).mpr ha
  · exact (G.mem_neighborFinset _ _).mpr hb

omit [DecidableEq V] in
private theorem leaf_neighbor_exists {G : SimpleGraph V} [DecidableRel G.Adj]
    {x : V} (h : G.degree x = 1) : ∃ a, G.Adj x a := by
  have hh : (G.neighborFinset x).Nonempty := card_pos.mp (by rw [card_neighborFinset_eq_degree,h]; decide)
  obtain ⟨a,ha⟩ := hh
  exact ⟨a,(G.mem_neighborFinset _ _).mp ha⟩

private theorem leaves_not_adjacent {G : SimpleGraph V} [DecidableRel G.Adj]
    (hc : G.Connected) (hn : 2 < Fintype.card V)
    {a b : V} (ha : G.degree a = 1) (hb : G.degree b = 1) : ¬G.Adj a b := by
  intro hab
  have Hall (x : V) : x = a ∨ x = b := by
    obtain ⟨p⟩ := hc.preconnected a x
    apply walk_closed (P := fun z => z = a ∨ z = b) ?_ p (Or.inl rfl)
    intro x y h hx
    rcases hx with rfl | rfl
    · exact Or.inr (unique_leaf_neighbor ha h hab)
    · exact Or.inl (unique_leaf_neighbor hb h hab.symm)
  have hi : (univ : Finset V) ⊆ {a,b} := by
    intro x _
    simpa only [mem_insert,mem_singleton] using Hall x
  have hh := card_le_card hi
  simp [hab.ne] at hh
  omega

noncomputable def pendants (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  (univ : Finset V).filter (fun x => G.degree x = 1)

/-- Exact full statement of Graffiti.pc #315. -/
theorem conjecture315 (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hn : 1 < Fintype.card V) (hα : G.indepNum = (pendants G).card) :
    WellTotalDominated G := by
  classical
  letI := hc.nonempty
  intro S hS hmin T hT
  have hT2 := total_dom_card_ge_two hT
  by_cases h2 : Fintype.card V ≤ 2
  · have hh : S.card ≤ Fintype.card V := card_le_univ _
    omega
  have h3 : 2 < Fintype.card V := by omega
  let P := pendants G
  let C := (univ : Finset V) \ P
  have hP (x : V) : x ∈ P ↔ G.degree x = 1 := by simp [P,pendants]
  have hC (x : V) : x ∈ C ↔ G.degree x ≠ 1 := by simp [C,hP]
  have hd (x : V) (hx : x ∈ C) : ∃ y ∈ P, G.Adj x y := by
    by_cases h : ∃ y ∈ P, G.Adj x y
    · exact h
    exfalso
    have hi : G.IsIndepSet (↑(insert x P) : Set V) := by
      intro a ha b hb hne hab
      change a ∈ insert x P at ha
      change b ∈ insert x P at hb
      rcases mem_insert.mp ha with hax | ha
      · rcases mem_insert.mp hb with hbx | hb
        · exact hne (hax.trans hbx.symm)
        · exact h ⟨b,hb,hax ▸ hab⟩
      · rcases mem_insert.mp hb with hbx | hb
        · exact h ⟨a,ha,hbx ▸ hab.symm⟩
        · exact leaves_not_adjacent hc h3 ((hP _).mp ha) ((hP _).mp hb) hab
    have hle := hi.card_le_indepNum
    have hnP : x ∉ P := fun hx' => (hC x).mp hx ((hP x).mp hx')
    rw [card_insert_of_not_mem hnP,hα] at hle
    change P.card+1 ≤ P.card at hle
    omega
  have forced (U : Finset V) (hU : TotalDominating G U) : C ⊆ U := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hd x hx
    obtain ⟨z,hz,hyz⟩ := hU y
    have ez := unique_leaf_neighbor ((hP _).mp hy) hyz he.symm
    exact ez ▸ hz
  by_cases hcore : ∀ x ∈ C, ∃ y ∈ C, G.Adj x y
  · have hdom : TotalDominating G C := by
      intro x
      by_cases hx : x ∈ C
      · exact hcore x hx
      · have hx1 : G.degree x = 1 := by
          by_cases e : G.degree x = 1
          · exact e
          · exact (hx ((hC _).mpr e)).elim
        obtain ⟨y,he⟩ := leaf_neighbor_exists hx1
        refine ⟨y,(hC _).mpr ?_,he⟩
        exact fun hy => leaves_not_adjacent hc h3 hx1 hy he
    rw [← hmin _ (forced S hS) hdom]
    exact card_le_card (forced T hT)
  · push_neg at hcore
    obtain ⟨c,hcC,hcn⟩ := hcore
    have star (x : V) : x = c ∨ G.Adj c x := by
      obtain ⟨p⟩ := hc.preconnected c x
      apply walk_closed (P := fun z => z = c ∨ G.Adj c z) ?_ p (Or.inl rfl)
      intro x y he hx
      rcases hx with rfl | hcadj
      · exact Or.inr he
      · have hx1 : G.degree x = 1 := by
          by_cases hn1 : G.degree x = 1
          · exact hn1
          · exact (hcn _ ((hC _).mpr hn1) hcadj).elim
        exact Or.inl (unique_leaf_neighbor hx1 he hcadj.symm)
    have hcS := forced S hS hcC
    obtain ⟨a,ha,hca⟩ := hS c
    have sub : ({c,a} : Finset V) ⊆ S := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hcS
      · simpa only [mem_singleton.mp hx] using ha
    have hdom : TotalDominating G ({c,a} : Finset V) := by
      intro x
      rcases star x with rfl | hx
      · exact ⟨a,by simp,hca⟩
      · exact ⟨c,by simp,hx.symm⟩
    rw [← hmin _ sub hdom]
    simpa [hca.ne] using hT2

#print axioms conjecture315
end Graffiti315
