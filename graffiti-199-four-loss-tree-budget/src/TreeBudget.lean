import CatalogueInterface
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Graffiti199Depleted.Catalogue

open SimpleGraph
open scoped Sym2

/-
The rank lemma and the catalogue parameter are from the public #199
low-connectivity file, Proof199K13.lean, in vjdad4m/maths.
-/
lemma tree_of_rank {V : Type*} [Fintype V] {G : SimpleGraph V}
    (r : V) (rank : V → ℕ)
    (hne : ∀ ⦃x y⦄, G.Adj x y → rank x ≠ rank y)
    (hr : ∀ ⦃x⦄, ¬(G.Adj r x ∧ rank x < rank r))
    (hp : ∀ x, x ≠ r → ∃! y, G.Adj x y ∧ rank y < rank x) :
    G.IsTree := by
  classical
  let p : {x // x ≠ r} → V := fun x => Classical.choose (ExistsUnique.exists (hp x x.prop))
  have pp (x : {x // x ≠ r}) : G.Adj x (p x) ∧ rank (p x) < rank x :=
    Classical.choose_spec (ExistsUnique.exists (hp x x.prop))
  have pu (x : {x // x ≠ r}) {y : V} (hy : G.Adj x y ∧ rank y < rank x) : y = p x :=
    (hp x x.prop).unique hy (pp x)
  have reach (x : V) : G.Reachable r x := by
    induction h : rank x using Nat.strong_induction_on generalizing x with
    | h n ih =>
      by_cases hx : x = r
      · subst x; exact SimpleGraph.Reachable.rfl
      · exact (ih _ (by rw [← h]; exact (pp ⟨x,hx⟩).2) _ rfl).trans (pp ⟨x,hx⟩).1.symm.reachable
  haveI : Nonempty V := ⟨r⟩
  have hcon : G.Connected := ⟨fun x y => (reach x).symm.trans (reach y)⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hcon, ?_⟩
  let f : {x // x ≠ r} → G.edgeSet :=
    fun x => ⟨s((x : V), p x), (G.mem_edgeSet).mpr (pp x).1⟩
  have hfi : Function.Injective f := by
    intro a b h
    have hab : s((a : V), p a) = s((b : V), p b) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hab with hsame | hrev
    · exact Subtype.ext hsame.1
    · have ha := (pp a).2
      have hb := (pp b).2
      rw [hrev.2, hrev.1] at ha
      omega
  have hfs : Function.Surjective f := by
    rintro ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e ?_
    intro a b he
    have had : G.Adj a b := (G.mem_edgeSet).mp he
    rcases lt_or_gt_of_ne (hne had) with hab | hab
    · have hbr : b ≠ r := by intro h; subst b; exact hr ⟨had.symm,hab⟩
      refine ⟨⟨b,hbr⟩, Subtype.ext ?_⟩
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,(pu ⟨b,hbr⟩ ⟨had.symm,hab⟩).symm⟩)
    · have har : a ≠ r := by intro h; subst a; exact hr ⟨had,hab⟩
      refine ⟨⟨a,har⟩, Subtype.ext ?_⟩
      exact Sym2.eq_iff.mpr (Or.inl ⟨rfl,(pu ⟨a,har⟩ ⟨had,hab⟩).symm⟩)
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hfi,hfs⟩)]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x => x = r)]
  have hr1 : Fintype.card {x // x = r} = 1 := Fintype.card_unique
  have hv1 : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
  omega

noncomputable def treeNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset V)).filter
    (fun S : Finset V => (G.induce (↑S : Set V)).IsTree)).sup Finset.card

theorem card_le_treeNumber {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Finset V) (hS : (G.induce (↑S : Set V)).IsTree) : S.card ≤ treeNumber G := by
  classical
  unfold treeNumber
  apply Finset.le_sup (b := S)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS⟩

/-- A six-vertex embedding with a unique earlier neighbor at each
nonfirst index gives an induced tree occupying exactly six vertices. -/
theorem six_le_treeNumber_of_ordering {V : Type*} [Fintype V] {G : SimpleGraph V}
    (e : Fin 6 ↪ V) (earlier : ∀ i : Fin 6, i ≠ 0 →
      ∃ j : Fin 6, G.Adj (e i) (e j) ∧ j < i ∧
        ∀ k : Fin 6, G.Adj (e i) (e k) → k < i → k = j) :
    6 ≤ treeNumber G := by
  classical
  let S := Finset.univ.map e
  let g : Fin 6 → (↑S : Set V) := fun i =>
    ⟨e i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have ginj : Function.Injective g := fun _ _ h => e.injective (congrArg Subtype.val h)
  have gsurj : Function.Surjective g := by
    rintro ⟨x,hx⟩
    obtain ⟨i,_,eq⟩ := Finset.mem_map.mp hx
    exact ⟨i,Subtype.ext eq⟩
  let b := Equiv.ofBijective g ⟨ginj,gsurj⟩
  let H := G.induce (↑S : Set V)
  have cardS : S.card = 6 := by simp [S]
  rw [← cardS]
  apply card_le_treeNumber S
  apply tree_of_rank (G := H) (b 0) (fun x => (b.symm x).val)
  · intro x y h eq
    exact H.loopless x ((b.symm.injective (Fin.ext eq)).symm ▸ h)
  · intro x h
    have zero : (b.symm (b 0)).val = 0 := by simp
    exact (Nat.not_lt_zero _ (zero ▸ h.2))
  · intro x hx
    obtain ⟨i,rfl⟩ := b.surjective x
    have i0 : i ≠ 0 := fun eq => hx (congrArg b eq)
    obtain ⟨j,ij,lt,only⟩ := earlier i i0
    refine ⟨b j,⟨ij,by simpa using lt⟩,?_⟩
    intro y hy
    obtain ⟨k,rfl⟩ := b.surjective y
    exact congrArg b (only k hy.1 (by simpa using hy.2))

#print axioms six_le_treeNumber_of_ordering

end Graffiti199Depleted.Catalogue
