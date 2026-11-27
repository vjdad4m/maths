import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open Finset SimpleGraph
namespace CazenaveRank
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
private theorem leaf_unique {v a b : V} (hv : G.degree v = 1)
    (ha : G.Adj v a) (hb : G.Adj v b) : a = b := by
  apply (Finset.card_le_one_iff.mp (show (G.neighborFinset v).card ≤ 1 from hv.le))
  · exact (G.mem_neighborFinset _ _).2 ha
  · exact (G.mem_neighborFinset _ _).2 hb

omit [DecidableEq V] in
theorem positive_of_connected (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    ∀ v, 0 < G.degree v := by
  intro v
  by_contra! h
  have all (w : V) : w = v := by
    obtain ⟨p⟩ := hc.preconnected v w
    cases p with
    | nil => rfl
    | cons ha _ => exact (not_lt_of_ge h
        ((G.degree_pos_iff_exists_adj v).2 ⟨_,ha⟩)).elim
  have hsub : (univ : Finset V) ⊆ {v} := by intro w _; simp [all w]
  have hcard := Finset.card_le_card hsub
  simp at hcard
  omega

theorem nonadjacent_leaves (hc : G.Connected) (hn : 3 ≤ Fintype.card V)
    (v w : V) (ha : G.Adj v w) (hv : G.degree v = 1) : G.degree w ≠ 1 := by
  intro hw
  have forbid {a b : V} (p : G.Walk a b) (hs : a = v ∨ a = w) : b = v ∨ b = w := by
    induction p with
    | nil => exact hs
    | @cons a c b e _ ih =>
      apply ih
      rcases hs with rfl | rfl
      · exact Or.inr (leaf_unique G hv e ha)
      · exact Or.inl (leaf_unique G hw e ha.symm)
  have hsub : (univ : Finset V) ⊆ {v,w} := by
    intro b _
    obtain ⟨p⟩ := hc.preconnected v b
    simpa using forbid p (Or.inl rfl)
  have h := Finset.card_le_card hsub
  rw [Finset.card_univ, Finset.card_insert_of_not_mem (by simpa using G.ne_of_adj ha),
    Finset.card_singleton] at h
  omega

/-- Bounds used after all leaves with a repeated support have been removed. -/
theorem separate_leaf_supports (hc : G.Connected) (hn : 3 ≤ Fintype.card V)
    (ht : ∀ v a b, G.Adj v a → G.Adj v b →
      G.degree a = 1 → G.degree b = 1 → a = b) :
    let p := (univ.filter (fun v : V => G.degree v = 1)).card
    2*p ≤ Fintype.card V ∧
    (∀ v, G.degree v ≤ if p = 0 then Fintype.card V - 1 else Fintype.card V - p) ∧
    (Fintype.card V = 3 → p = 0) := by
  classical
  let L := (univ : Finset V).filter (fun v => G.degree v = 1)
  let H := (univ : Finset V) \ L
  change 2*L.card ≤ _ ∧ (∀ v, G.degree v ≤ if L.card = 0 then Fintype.card V - 1 else Fintype.card V - L.card) ∧ (Fintype.card V = 3 → L.card = 0)
  have hp := positive_of_connected G hc (by omega)
  have hsplit : H.card + L.card = Fintype.card V := by
    dsimp [H]
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ L), Finset.card_univ]
  have hchoose (a : L) : ∃ v, G.Adj a.val v :=
    (G.degree_pos_iff_exists_adj a.val).mp (hp a)
  choose f hf using hchoose
  let g (a : L) : H := ⟨f a, by
    simp [H,L]
    exact nonadjacent_leaves G hc hn _ _ (hf a) ((Finset.mem_filter.mp a.property).2)⟩
  have inj : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    change f x = f y at hh
    have hy := (hf y).symm
    rw [← hh] at hy
    exact ht (f x) x y (hf x).symm hy
      ((Finset.mem_filter.mp x.property).2) ((Finset.mem_filter.mp y.property).2)
  have hLH : L.card ≤ H.card := by simpa using Fintype.card_le_of_injective g inj
  refine ⟨by omega, ?_, ?_⟩
  · intro v
    change (G.neighborFinset v).card ≤ if L.card = 0 then _ else _
    by_cases hz : L.card = 0
    · rw [if_pos hz]
      have subs : G.neighborFinset v ⊆ univ.erase v := by
        intro w hw; exact mem_erase.mpr
          ⟨(G.ne_of_adj ((G.mem_neighborFinset v w).mp hw)).symm,mem_univ w⟩
      exact (card_le_card subs).trans_eq (by simp)
    rw [if_neg hz]
    let D := G.neighborFinset v
    by_cases hv : v ∈ L
    · have ht1 : G.degree v = 1 := by simpa [L] using hv
      change G.degree v ≤ _
      omega
    · have nonleaves : D \ L ⊆ H.erase v := by
        intro w hw
        have hw' := mem_sdiff.mp hw
        have ne : w ≠ v := (G.ne_of_adj ((G.mem_neighborFinset v w).mp hw'.1)).symm
        exact mem_erase.mpr ⟨ne,mem_sdiff.mpr ⟨mem_univ _,hw'.2⟩⟩
      have leaves : (D ∩ L).card ≤ 1 := Finset.card_le_one_iff.mpr fun a b => by
        have ha := mem_inter.mp a
        have hb := mem_inter.mp b
        exact ht v _ _ ((G.mem_neighborFinset _ _).mp ha.1)
          ((G.mem_neighborFinset _ _).mp hb.1) (by simpa [L] using ha.2)
          (by simpa [L] using hb.2)
      have un : D \ L ∪ (D ∩ L) = D := by ext w; simp; tauto
      have sum := Finset.card_union_le (D \ L) (D ∩ L)
      rw [un] at sum
      have h1 := card_le_card nonleaves
      have vh : v ∈ H := mem_sdiff.mpr ⟨mem_univ _,hv⟩
      have eh := card_erase_add_one vh
      change D.card ≤ _
      omega
  · intro hn3
    by_cases bad : L.card = 0
    · exact bad
    exfalso
    have p1 : L.card = 1 := by omega
    have hz := Finset.card_pos.mp (show 0 < L.card by omega)
    obtain ⟨u,hu⟩ := hz
    have degU : G.degree u = 1 := by simpa [L] using hu
    let w := f ⟨u,hu⟩
    have huw : G.Adj u w := hf ⟨u,hu⟩
    have hHw : w ∈ H := (g ⟨u,hu⟩).property
    have hH : H.card = 2 := by omega
    have hcH : (H.erase w).card = 1 := by
      have := Finset.card_erase_add_one hHw
      omega
    obtain ⟨t,htm⟩ := Finset.card_pos.mp (show 0 < (H.erase w).card by omega)
    have htm' := mem_erase.mp htm
    have hnt : G.degree t ≠ 1 := by simpa [H,L] using htm'.2
    have hnotU : ¬G.Adj t u := fun a => htm'.1 (leaf_unique G degU a.symm huw)
    have tsub : G.neighborFinset t ⊆ {w} := by
      intro z hz
      have htz := (G.mem_neighborFinset t z).mp hz
      have nzU : z ≠ u := fun e => hnotU (e ▸ htz)
      have nzT : z ≠ t := (G.ne_of_adj htz).symm
      by_contra! hin
      have hzL : z ∉ L := by
        intro hzl
        exact nzU (Finset.card_le_one_iff.mp p1.le hzl hu)
      have hzH : z ∈ H := mem_sdiff.mpr ⟨mem_univ _,hzL⟩
      exact nzT (Finset.card_le_one_iff.mp hcH.le
        (mem_erase.mpr ⟨by simpa using hin,hzH⟩) htm)
    have ct := Finset.card_le_card tsub
    rw [card_singleton] at ct
    change G.degree t ≤ 1 at ct
    have tpos := hp t
    exact hnt (by omega)

#print axioms CazenaveRank.separate_leaf_supports
end CazenaveRank
