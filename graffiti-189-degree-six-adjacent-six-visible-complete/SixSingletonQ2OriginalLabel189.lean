import SixSingletonQ2Data189
import SixSingletonQ1PortBoard189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
open SimpleGraph Finset ArticulationPair
open private Cmp from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common strictA strictB from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
open private common_count from SixSingletonQ1PortBoard189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

structure OriginalLabel (D : Cmp G a b) (s : V) where
  e : Vertex ≃ V
  aEq : e 6=a
  bEq : e 7=b
  sEq : e 8=s
  mA : ∀ i, e i∈EA D ↔ i=0
  mB : ∀ i, e i∈EB D ↔ i=1 ∨ i=2
  mC : ∀ i, e i∈Common D ↔ i=3 ∨ i=4 ∨ i=5
  mL : ∀ i, e i∈strictA D ↔ i=9 ∨ i=10
  mR : ∀ i, e i∈strictB D ↔ i=11 ∨ i=12 ∨ i=13
  mW : ∀ i, e i∈nearBal D ↔ i=14 ∨ i=15

theorem choose_original_label (F : SixVisibleData G D s) (n : Fintype.card V=16)
    (v6 : (Vis D).card=6) (ea : (EA D).card=1) (eb : (EB D).card=2)
    (l2 : (strictA D).card=2) (r3 : (strictB D).card=3) (w2 : (nearBal D).card=2) :
    Nonempty (OriginalLabel D s) := by
  classical
  have c3 : (Common D).card=3 := by have h:=common_count F; omega
  obtain ⟨x, xs⟩ := card_eq_one.mp ea
  obtain ⟨y,y', _,ys⟩ := card_eq_two.mp eb
  obtain ⟨c,c',c'', _,_,_,cs⟩ := card_eq_three.mp c3
  obtain ⟨l,l', _,ls⟩ := card_eq_two.mp l2
  obtain ⟨r,r',r'', _,_,_,rs⟩ := card_eq_three.mp r3
  obtain ⟨w,w', _,ws⟩ := card_eq_two.mp w2

  let f : Vertex→V := ![x,y,y',c,c',c'',a,b,s,l,l',r,r',r'',w,w']
  have sur : Function.Surjective f := by
    intro t
    rcases F.cover t with h|h|h|hv|hd
    · exact ⟨6,h.symm⟩
    · exact ⟨7,h.symm⟩
    · exact ⟨8,h.symm⟩
    · rw [←F.visiblePart,xs,ys,cs] at hv
      simp only [mem_union,mem_insert,mem_singleton] at hv
      rcases hv with ((h|h|h)|h|h|h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
      · exact ⟨2,h.symm⟩
      · exact ⟨3,h.symm⟩
      · exact ⟨4,h.symm⟩
      exact ⟨5,h.symm⟩

    rw [←F.darkPart,ls,rs,ws] at hd
    simp only [mem_union,mem_insert,mem_singleton] at hd
    rcases hd with (((h|h)|(h|h|h))|h|h)
    · exact ⟨9,h.symm⟩
    · exact ⟨10,h.symm⟩
    · exact ⟨11,h.symm⟩
    · exact ⟨12,h.symm⟩
    · exact ⟨13,h.symm⟩
    · exact ⟨14,h.symm⟩
    exact ⟨15,h.symm⟩

  let e : Vertex≃V := Equiv.ofBijective f
    ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨sur,by rw [n]; simp⟩)
  refine ⟨⟨e,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i
    rw [xs]
    simp only [mem_insert,mem_singleton]
    constructor
    · intro h
      exact e.injective (show e i=e 0 from h)
    rintro rfl; simp [e,f]
  · intro i
    rw [ys]
    simp only [mem_insert,mem_singleton]
    constructor
    · intro h
      rcases h with h|h
      · exact Or.inl (e.injective (show e i=e 1 from h))
      exact Or.inr (e.injective (show e i=e 2 from h))
    rintro (rfl|rfl) <;> simp [e,f]
  · intro i
    rw [cs]
    simp only [mem_insert,mem_singleton]
    constructor
    · intro h
      rcases h with h|h|h
      · exact Or.inl (e.injective (show e i=e 3 from h))
      · exact Or.inr (Or.inl (e.injective (show e i=e 4 from h)))
      exact Or.inr (Or.inr (e.injective (show e i=e 5 from h)))
    rintro (rfl|rfl|rfl) <;> simp [e,f]
  · intro i
    rw [ls]
    simp only [mem_insert,mem_singleton]
    constructor
    · intro h
      rcases h with h|h
      · exact Or.inl (e.injective (show e i=e 9 from h))
      exact Or.inr (e.injective (show e i=e 10 from h))
    rintro (rfl|rfl) <;> simp [e,f]
  · intro i
    rw [rs]
    simp only [mem_insert,mem_singleton]
    constructor
    · intro h
      rcases h with h|h|h
      · exact Or.inl (e.injective (show e i=e 11 from h))
      · exact Or.inr (Or.inl (e.injective (show e i=e 12 from h)))
      exact Or.inr (Or.inr (e.injective (show e i=e 13 from h)))
    rintro (rfl|rfl|rfl) <;> simp [e,f]
  · intro i
    rw [ws]
    simp only [mem_insert,mem_singleton]
    constructor
    · intro h
      rcases h with h|h
      · exact Or.inl (e.injective (show e i=e 14 from h))
      exact Or.inr (e.injective (show e i=e 15 from h))
    rintro (rfl|rfl) <;> simp [e,f]

#print axioms choose_original_label
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2
