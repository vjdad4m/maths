import UpperTenBoard384b
import T11TenNormalize384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph OddStars OddStars.LeafCritical
open CutTen
open private Repair.triangles_le_choose from Repair384b

private theorem exact_motif : ∀ k : Fin 4,∀ i j : Fin 10,
    staticMotif k i j = T11TenNormalize.motif k i j := by decide
private theorem exact_cuts : ∀ k : Fin 4,cuts k=T11TenNormalize.allowedCuts k := by decide

theorem finite_upper_ten (K : SimpleGraph (Fin 10)) (dec : DecidableRel K.Adj) :
    letI := dec
    ∀ (u v : Fin 10) (B : Finset (Fin 10)), TenFrame K u v B →
      ∃ D : Finset (Fin 10), D.card≤4 ∧ TwoDominates K D := by
  letI := dec
  intro u v B f
  have filterEq (x : Fin 10) :
      (K.neighborFinset x).filter (T11TenNormalize.opposite B x) = crossed K B x := by
    ext y
    by_cases h : x∈B <;> simp [crossed,T11TenNormalize.opposite,h]
  have uo : ((K.neighborFinset u).filter (T11TenNormalize.opposite B u)).card=2 :=
    (congrArg Finset.card (filterEq u)).trans f.uCross
  have vo : ((K.neighborFinset v).filter (T11TenNormalize.opposite B v)).card=2 :=
    (congrArg Finset.card (filterEq v)).trans f.vCross
  obtain ⟨k,p,m,p0,p4,allowed,color,fixed⟩ :=
    T11TenNormalize.normalize K u v f.distinct f.apart f.uDegree f.uScore f.vDegree f.vScore
      B f.balanced f.rootLeft uo vo
  exact cover_from_normal_form K u v B f
    ⟨k,m,p,(exact_cuts k).symm ▸ allowed,p0,p4,color,fun i j b e=>fixed i j b ((exact_motif k i j).symm.trans e)⟩

/-- Diversity eleven in the upper (ten high) triangle-skeleton profile,
with no connectivity restriction. -/
theorem exact_upper_ten {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : (types G).card=11)
    (ten : (high (patch G ∅)).card=10) : gamma G≤bound G :=
  exact_of_upper_ten_certificate G t ten finite_upper_ten

theorem exact_of_supported_no_ears {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (support : Supported G)
    (noEars : nonleaves G=high G) (t : (types G).card=11) :
    gamma G≤bound G := by
  by_contra! bad
  have low := (ten_to_fifteen G t bad).1
  have hi := (high_profile G t bad).2
  rw [noEars] at low
  have d (x : V) : (patch G ∅).degree x=G.degree x := by
    rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
    congr 1
    ext y
    simp only [mem_neighborFinset]
    exact ⟨fun e=>e.1,fun e=>⟨e,Or.inl (support e)⟩⟩
  have eq : high (patch G ∅)=high G := by
    ext v
    simp only [high,mem_filter,mem_univ,true_and,d]
  have win := exact_upper_ten G t (by rw [eq]; omega)
  exact (not_lt_of_ge win) bad

/-- The entire missing-score-one subcase at diversity eleven, without
a connectedness assumption. -/
theorem exact_of_no_score_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : (types G).card=11) (one : 1∉types G) :
    gamma G≤bound G := by
  by_contra! failure
  obtain ⟨J,dec,_,sup,_,eq,bad⟩ := triangle_supported_reduction G t failure
  letI := dec
  have h : nonleaves J=high J := by
    apply Finset.Subset.antisymm
    · intro v vm
      by_contra n
      have d : J.degree v≤2 := by by_contra! big; exact n (mem_filter.mpr ⟨mem_univ _,big⟩)
      have p := positive_of_nonleaf J sup vm
      have cap := (Repair.triangles_le_choose J v).trans (Nat.choose_le_choose 2 d)
      rw [Nat.choose_self] at cap
      have m : 1∈types J := mem_image.mpr ⟨v,mem_univ _,by omega⟩
      exact one (eq ▸ m)
    · intro v vm
      have d : 3≤J.degree v := (mem_filter.mp vm).2
      exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have win := exact_of_supported_no_ears J sup h (by rw [eq]; exact t)
  exact (not_lt_of_ge win) bad

#print axioms finite_upper_ten
#print axioms exact_upper_ten
#print axioms exact_of_supported_no_ears
#print axioms exact_of_no_score_one
end Graffiti384b.DiversityEleven
