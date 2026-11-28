import DiversityElevenProfile384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private TrianglePrune.Closed TrianglePrune.scores_closed TrianglePrune.induced_cost from TrianglePrune384b
open private Repair.nbr_mono Repair.omit_set from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def localPositive (A : Finset V) : Finset Nat := (A.image (trianglesAt G)).erase 0

theorem local_positive_budget (A : Finset V) (closed : TrianglePrune.Closed G A) :
    (localPositive G A).card≤2*Capacity.value G A ∅ := by
  let H := G.induce (A : Set V)
  have same : types H = A.image (trianglesAt G) := by
    ext k
    constructor
    · intro hk
      obtain ⟨v,_,rfl⟩ := mem_image.mp hk
      exact mem_image.mpr ⟨v.val,v.property,(TrianglePrune.scores_closed G A closed v).symm⟩
    · intro hk
      obtain ⟨v,va,rfl⟩ := mem_image.mp hk
      exact mem_image.mpr ⟨⟨v,va⟩,mem_univ _,TrianglePrune.scores_closed G A closed ⟨v,va⟩⟩
  have pos := PositivePalette.positive_bound H
  have ca : Fintype.card (↑(A : Set V)) = A.card := Fintype.card_coe A
  rw [same,ca] at pos
  have need := TrianglePrune.induced_cost G A
  change A.card≤gamma H+Capacity.value G A ∅ at need
  unfold localPositive
  omega

/-- A split of the positive palette into two closed pieces gives the
missing odd-palette omission whenever either local palette is odd, or
a positive score is realized on both pieces. -/
theorem exact_of_positive_split {A B : Finset V} (dis : Disjoint A B)
    (ca : TrianglePrune.Closed G A) (cb : TrianglePrune.Closed G B)
    (cover : ∀ v, 0<trianglesAt G v → v∈A∪B)
    (gain : (localPositive G A).card%2=1 ∨ (localPositive G B).card%2=1 ∨
      (localPositive G A∩localPositive G B).Nonempty) :
    gamma G≤bound G := by
  by_contra! bad
  have zero := (PositivePalette.failure_requires_odd_zero G bad).2
  have tp : ((types G).erase 0).card + 1=(types G).card := by
    rw [card_erase_of_mem zero]
    have z : 0<(types G).card := card_pos.mpr ⟨0,zero⟩
    omega
  have exactUnion : (types G).erase 0=localPositive G A∪localPositive G B := by
    ext k
    simp only [localPositive,types,mem_erase,mem_union,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨k0,v,rfl⟩
      rcases mem_union.mp (cover v (Nat.pos_of_ne_zero k0)) with va|vb
      · exact Or.inl ⟨k0,v,va,rfl⟩
      · exact Or.inr ⟨k0,v,vb,rfl⟩
    · rintro (⟨n,v,_,rfl⟩|⟨n,v,_,rfl⟩) <;> exact ⟨n,v,rfl⟩
  have mass := card_union_add_card_inter (localPositive G A) (localPositive G B)
  rw [←exactUnion] at mass
  have a := local_positive_budget G A ca
  have b := local_positive_budget G B cb
  have sep : ∀ u∈A, ∀ v∈B, ¬G.Adj u v :=
    fun u ua v vb adj => disjoint_left.mp dis (ca u ua v adj) vb
  have add := Capacity.separated_add G A B ∅ dis sep
  have cost : (types G).card≤2*Capacity.value G (A∪B) ∅ := by
    rcases gain with g|g|g
    · omega
    · omega
    · have sz := card_pos.mpr g
      omega
  obtain ⟨O,feas,num⟩ := Capacity.attained G (A∪B) ∅
  have save := Repair.omit_set G O (fun v vo=>(feas.2 v vo).trans
    (Repair.nbr_mono G v (by
      intro w hw
      simp only [empty_union,mem_sdiff] at hw
      exact mem_compl.mpr hw.2)))
  have small := card_le_univ O
  unfold bound at bad
  omega

#print axioms local_positive_budget
#print axioms exact_of_positive_split
end Graffiti384b.DiversityEleven
