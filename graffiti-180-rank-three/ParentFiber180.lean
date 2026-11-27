import CutEntry180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The descending parent edges of a spanning tree exhaust its edge set. -/
theorem parent_image (T : SimpleGraph V) [DecidableRel T.Adj] (tree : T.IsTree)
    (r : V) (p : V→V) (d : V→ℕ) (down : ∀ x≠r, d (p x)<d x)
    (take : ∀ x≠r, T.Adj x (p x)) :
    (univ.erase r).image (fun x => s(x,p x))=T.edgeFinset := by
  classical
  let S : Finset V := univ.erase r
  let f (x : V) := s(x,p x)
  change S.image f=T.edgeFinset
  apply eq_of_subset_of_card_le
  · intro e he
    obtain ⟨x,h,rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr (take x (mem_erase.mp h).1)
  · have inj : Set.InjOn f (S : Set V) := by
      intro x hx y hy eq
      rcases Sym2.eq_iff.mp eq with a|⟨a,b⟩
      · exact a.1
      · have dx := down x (mem_erase.mp hx).1
        have dy := down y (mem_erase.mp hy).1
        rw [b] at dx
        rw [←a] at dy
        omega
    rw [card_image_of_injOn inj]
    have e := tree.card_edgeFinset
    have eq := card_erase_add_one (mem_univ r)
    rw [card_univ] at eq
    change _≤(univ.erase r).card
    omega

/-- In a tree containing one descending parent edge for every nonroot, this
list gives every edge. Thus the nonroot degree is one plus its child count. -/
theorem parent_neighbors (T : SimpleGraph V) [DecidableRel T.Adj] (tree : T.IsTree)
    (r : V) (p : V→V) (d : V→ℕ) (down : ∀ x≠r, d (p x)<d x)
    (take : ∀ x≠r, T.Adj x (p x)) (v : V) (vr : v≠r) :
    T.degree v=(((univ.erase r).filter (fun x => p x=v)).card+1) := by
  classical
  let S : Finset V := univ.erase r
  let f (x : V) := s(x,p x)
  have whole : S.image f=T.edgeFinset := parent_image T tree r p d down take
  let C := S.filter (fun x => p x=v)
  have neigh : T.neighborFinset v=insert (p v) C := by
    ext x
    simp only [mem_neighborFinset,mem_insert]
    constructor
    · intro e
      have he : s(v,x)∈T.edgeFinset := mem_edgeFinset.mpr e
      rw [←whole] at he
      obtain ⟨y,hy,eq⟩ := mem_image.mp he
      rcases Sym2.eq_iff.mp eq with ⟨h,k⟩|⟨h,k⟩
      · subst y; exact Or.inl k.symm
      · subst y; exact Or.inr (mem_filter.mpr ⟨hy,k⟩)
    · rintro (h|h)
      · simpa only [h] using take v vr
      · obtain ⟨xn,px⟩ := mem_filter.mp h
        simpa only [px] using (take x (mem_erase.mp xn).1).symm
  have no : p v∉C := by
    intro z
    obtain ⟨nz,eq⟩ := mem_filter.mp z
    have l := down (p v) (mem_erase.mp nz).1
    rw [eq] at l
    exact (Nat.lt_asymm (down v vr)) l
  rw [←card_neighborFinset_eq_degree,neigh,card_insert_of_not_mem no]

#print axioms parent_image
#print axioms parent_neighbors
end Minimal180.HigherRank
