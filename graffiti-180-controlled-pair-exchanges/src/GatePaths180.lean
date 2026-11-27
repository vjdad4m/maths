import AbsorbedGate180
set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The auxiliary old leaves F exist exactly when each component reached
from an unhelpful contact, outside H and its gate z, remains in the
allowed old leaves A. -/
theorem absorption_iff_paths (J : SimpleGraph V) (A H : Finset V) (x z : V)
    (away : Disjoint A H) (za : z∉A) :
    (∃ F⊆A,(∀ i∈F,∀ j,J.Adj i j → j∈H∪F ∨ j=z) ∧
      (∀ b∈A,b∉F → Dominates J H b → J.Adj x b)) ↔
    (∀ b∈A,Dominates J H b → ¬J.Adj x b →
      ∀ t,(within J ((univ\H).erase z)).Reachable b t → t∈A) := by
  classical
  let T := (univ\H).erase z
  constructor
  · rintro ⟨F,fa,sealed,useful⟩ b ba contact unhelpful t ⟨p⟩
    have bf : b∈F := by
      by_contra out
      exact unhelpful (useful b ba out contact)
    have travel {i j : V} (q : (within J T).Walk i j) : i∈F → j∈F := by
      induction q with
      | nil => exact id
      | @cons i j k e _ ih =>
        intro fi
        apply ih
        obtain ⟨jz,jh⟩ := mem_erase.mp e.2.2
        rcases sealed i fi j e.1 with h|h
        · exact (mem_union.mp h).resolve_left (mem_sdiff.mp jh).2
        · exact (jz h).elim
    exact fa (travel p bf)
  · intro confined
    let bad (b:V) := b∈A ∧ Dominates J H b ∧ ¬J.Adj x b
    let F := T.filter (fun i => ∃ b,bad b ∧ (within J T).Reachable b i)
    have fa : F⊆A := by
      intro i h
      obtain ⟨_,b,⟨ba,c,n⟩,p⟩ := mem_filter.mp h
      exact confined b ba c n i p
    refine ⟨F,fa,?_,?_⟩
    · intro i fi j e
      by_cases jz : j=z
      · exact Or.inr jz
      by_cases jh : j∈H
      · exact Or.inl (mem_union_left _ jh)
      have jt : j∈T := mem_erase.mpr ⟨jz,mem_sdiff.mpr ⟨mem_univ _,jh⟩⟩
      obtain ⟨it,b,bb,p⟩ := mem_filter.mp fi
      have edge : (within J T).Adj i j := ⟨e,it,jt⟩
      exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨jt,b,bb,p.trans edge.reachable⟩))
    · intro b ba out contact
      by_contra unhelpful
      have bt : b∈T := mem_erase.mpr ⟨fun e => za (e ▸ ba),mem_sdiff.mpr ⟨mem_univ _,disjoint_left.mp away ba⟩⟩
      exact out (mem_filter.mpr ⟨bt,b,⟨ba,contact,unhelpful⟩,.refl _⟩)

/-- A path-only sufficient condition for controlled repair. No set of
return vertices or absorbable old leaves is an input. -/
theorem controlled_of_confined_paths (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C Z : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (zs : Z⊆(U\C).erase y)
    (nc : NoCut (J⊔SimpleGraph.edge x y)) (empty : demand J ((univ\C)\Z) C Z x=∅)
    (paths : ∀ H∈remote J ((univ\C)\Z) y,∃ z∈Z,
      (∀ i∈H,∀ j∈Z,J.Adj i j → j=z) ∧
      (∀ b∈C.erase x,Dominates J H b → ¬J.Adj x b →
        ∀ t,(within J ((univ\H).erase z)).Reachable b t → t∈C.erase x)) :
    ∃ B⊆C.erase x, B.card≤(remote J ((univ\C)\Z) y).card ∧ Z.card≤B.card+1 ∧
      (B.card<Z.card → FirstForm J U x y w) ∧
      let L := (C.erase x\B)∪Z
      Con (J⊔SimpleGraph.edge x y) (univ\L) ∧ ∀ q∈L,Dominates (J⊔SimpleGraph.edge x y) (univ\L) q := by
  apply controlled_of_absorbed_gates J hc hn x y w xy old xw wy U C Z cu count tip zs nc empty
  intro H h
  obtain ⟨z,zin,gate,confined⟩ := paths H h
  have away : Disjoint (C.erase x) H := by
    apply disjoint_left.mpr
    intro b bc bh
    obtain ⟨a,_,eq⟩ := mem_image.mp (mem_of_mem_erase h)
    have ir := ((mem_part ..).mp (eq ▸ bh)).1
    exact (mem_sdiff.mp (mem_sdiff.mp ir).1).2 (mem_of_mem_erase bc)
  have za : z∉C.erase x := fun k => (mem_sdiff.mp (mem_of_mem_erase (zs zin))).2 (mem_of_mem_erase k)
  obtain ⟨F,fa,shield,good⟩ := (absorption_iff_paths J (C.erase x) H x z away za).mpr confined
  exact ⟨z,zin,F,fa,gate,shield,good⟩

#print axioms absorption_iff_paths
#print axioms controlled_of_confined_paths
end Minimal180.Controlled
