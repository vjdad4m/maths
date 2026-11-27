import BatchRepair

namespace Graffiti384b
open Finset SimpleGraph
open private cut cut_symm cut_insert from Proof384b
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
private theorem nm (x : V) {a b : Finset V} (h : a ⊆ b) : nbr G x a ≤ nbr G x b :=
  card_le_card (filter_subset_filter _ h)

omit [Fintype V] in
private theorem half_cross {B A : Finset V} (s : A ⊆ B)
    (m : ∀ D ⊆ B, cut G D (B \ D) ≤ cut G A (B \ A)) {x : V} (xa : x ∈ A) :
    nbr G x B ≤ 2 * nbr G x (B \ A) := by
  classical
  have hh := m (A.erase x) ((erase_subset _ _).trans s)
  have split : B \ A.erase x = insert x (B \ A) := by
    ext y
    by_cases h : y = x
    · subst y
      simp [s xa]
    · simp [h]
  have xx : x ∉ B \ A := fun h => (mem_sdiff.mp h).2 xa
  rw [split, cut_symm G (A.erase x), cut_insert G xx, cut_symm G (B \ A)] at hh
  have ins := cut_insert G (not_mem_erase x A) (B \ A)
  rw [insert_erase xa] at ins
  have self : nbr G x (A.erase x) = nbr G x A := by
    unfold nbr
    congr 1
    ext y
    by_cases h : y = x
    · subst y; simp
    · simp [h]
  have union : A ∪ (B \ A) = B := by
    ext y
    by_cases h : y ∈ A
    · simp [h, s h]
    · simp [h]
  have dj : Disjoint (A.filter (G.Adj x)) ((B \ A).filter (G.Adj x)) :=
    disjoint_left.mpr fun y ya yd => (mem_sdiff.mp (mem_filter.mp yd).1).2 (mem_filter.mp ya).1
  have add : nbr G x B = nbr G x A + nbr G x (B \ A) := by
    unfold nbr
    rw [← union, filter_union, card_union_of_disjoint dj]
    simp only [union]
  omega

/-- A cut of the deficient graph saves at least half the vertices that
have enough internal neighbors for their outstanding deficit. -/
theorem maxcut_repair_saves (s : Finset V) :
    let B := univ.filter (fun v => v ∉ s ∧ nbr G v s < 2)
    let E := B.filter (fun v => (nbr G v s = 1 ∧ 1 ≤ nbr G v B) ∨ 3 ≤ nbr G v B)
    gamma G ≤ s.card + B.card - (E.card + 1) / 2 := by
  classical
  dsimp only
  let B := univ.filter (fun v => v ∉ s ∧ nbr G v s < 2)
  let E := B.filter (fun v => (nbr G v s = 1 ∧ 1 ≤ nbr G v B) ∨ 3 ≤ nbr G v B)
  have es : E ⊆ B := filter_subset _ _
  obtain ⟨A, am, mx⟩ := exists_max_image B.powerset (fun a => cut G a (B \ a))
    ⟨∅, mem_powerset.mpr (empty_subset _)⟩
  have sa := mem_powerset.mp am
  let C := B \ A
  have sc : C ⊆ B := sdiff_subset
  have bc : B \ C = A := by
    ext x
    by_cases h : x ∈ A
    · simp [C, h, sa h]
    · by_cases b : x ∈ B <;> simp [C, h, b]
  have ha : ∀ D ⊆ B, cut G D (B \ D) ≤ cut G A (B \ A) :=
    fun D ds => mx _ (mem_powerset.mpr ds)
  have hc : ∀ D ⊆ B, cut G D (B \ D) ≤ cut G C (B \ C) := by
    intro D ds
    rw [bc, cut_symm G C A]
    exact ha D ds
  have supported (D : Finset V) (ds : D ⊆ B)
      (h : ∀ F ⊆ B, cut G F (B \ F) ≤ cut G D (B \ D)) :
      gamma G ≤ s.card + B.card - (E ∩ D).card := by
    apply batch_repair_saves G s (E ∩ D)
    · exact inter_subset_left.trans es
    intro x xm
    obtain ⟨xe,xd⟩ := mem_inter.mp xm
    have cross := half_cross G ds h xd
    have cov : nbr G x (B \ D) ≤ nbr G x (B \ (E ∩ D)) :=
      nm G x (by
        intro y hy
        exact mem_sdiff.mpr ⟨(mem_sdiff.mp hy).1, fun hi => (mem_sdiff.mp hy).2 (mem_inter.mp hi).2⟩)
    change 2 ≤ nbr G x s + nbr G x (B \ (E ∩ D))
    rcases (mem_filter.mp xe).2 with ⟨one,p⟩|hdeg <;> omega
  have estr : (E ∩ A).card + (E ∩ C).card = E.card := by
    have ee : (E ∩ A) ∪ (E ∩ C) = E := by
      ext x
      by_cases ha' : x ∈ A
      · simp [C, ha']
      · by_cases he : x ∈ E
        · simp [C, ha', he, es he]
        · simp [he]
    have dd : Disjoint (E ∩ A) (E ∩ C) := disjoint_left.mpr fun x a c =>
      (mem_sdiff.mp (mem_inter.mp c).2).2 (mem_inter.mp a).2
    rw [← card_union_of_disjoint dd, ee]
  change gamma G ≤ s.card + B.card - (E.card + 1) / 2
  have a := supported A sa ha
  have c := supported C sc hc
  omega

#print axioms maxcut_repair_saves
end Graffiti384b
