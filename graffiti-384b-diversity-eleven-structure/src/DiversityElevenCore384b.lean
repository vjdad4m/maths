import BookCut384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private TrianglePrune.skeleton TrianglePrune.scores TrianglePrune.triangle_iff from TrianglePrune384b
open private Prune.outside_zero from Prune384b
open private Repair.triangles_le_choose from Repair384b

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Supported : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z

theorem triangle_supported_reduction (t : (types G).card=11) (bad : bound G<gamma G) :
    ∃ (J : SimpleGraph V) (dec : DecidableRel J.Adj),
      letI := dec
      J ≤ G ∧ Supported J ∧ (∀ v, trianglesAt J v=trianglesAt G v) ∧
        types J=types G ∧ bound J<gamma J := by
  classical
  obtain ⟨k,hk⟩ := card_pos.mp (by omega : 0<(types G).card)
  obtain ⟨a,_,_⟩ := mem_image.mp hk
  let J := TrianglePrune.skeleton G a ∅
  let dec : DecidableRel J.Adj := inferInstanceAs (DecidableRel (TrianglePrune.skeleton G a ∅).Adj)
  letI := dec
  have sub : J≤G := fun _ _ edge=>edge.1
  have sc (v : V) : trianglesAt J v=trianglesAt G v := TrianglePrune.scores G a ∅ v
  have tp : types J=types G :=
    congrArg (fun f : V→Nat => univ.image f) (funext sc)
  have sb : Supported J := by
    intro x y edge
    obtain ⟨xy,w⟩ := edge
    rcases w with ⟨z,xz,yz⟩|h|h
    · exact ⟨z,⟨xz,Or.inl ⟨y,xy,yz.symm⟩⟩,⟨yz,Or.inl ⟨x,xy.symm,xz.symm⟩⟩⟩
    · exact (Finset.not_mem_empty _ h.1).elim
    · exact (Finset.not_mem_empty _ h.1).elim
  have m := PositivePalette.Prerequisites.gamma_mono G J sub
  have b : bound J=bound G := by unfold bound; rw [tp]
  exact ⟨J,dec,sub,sb,sc,tp,b ▸ bad.trans_le m⟩

theorem ten_to_fifteen (t : (types G).card=11) (bad : bound G<gamma G) :
    10≤(nonleaves G).card ∧ (nonleaves G).card≤15 := by
  have sub : types G ⊆ insert 0 ((nonleaves G).image (trianglesAt G)) := by
    intro a ha
    obtain ⟨v,_,rfl⟩ := mem_image.mp ha
    by_cases inside : v∈nonleaves G
    · exact mem_insert_of_mem (mem_image.mpr ⟨v,inside,rfl⟩)
    · rw [Prune.outside_zero G inside]
      exact mem_insert_self _ _
  have c : (types G).card≤(nonleaves G).card+1 :=
    (card_le_card sub).trans ((card_insert_le _ _).trans (Nat.succ_le_succ card_image_le))
  have low := nonleaf_bound G
  unfold bound at bad
  omega

theorem high_profile (t : (types G).card=11) (bad : bound G<gamma G) :
    9≤(high G).card ∧ (high G).card≤10 := by
  have cap := type_bound G
  have win := high_bound G
  unfold bound at bad
  omega

/-- With a triangular ear, the high palette is exactly nine distinct
scores, none equal to 0 or 1. -/
theorem ear_profile (support : Supported G) (t : (types G).card=11) (bad : bound G<gamma G)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : G.Adj a b) :
    (high G).card=9 ∧ Set.InjOn (trianglesAt G) (high G : Set V) ∧
      (∀ v∈high G, 2≤trianglesAt G v) := by
  have de : G.degree e=2 := by
    rw [←card_neighborFinset_eq_degree,ear,card_pair ab.ne]
  have eout : e∉high G := by simp [high,de]
  have cov := PositivePalette.protect_ear G (fun {_ _} adj => support adj) ear ab
  have budget := PositivePalette.count_covered G cov
  rw [card_insert_of_not_mem eout] at budget
  have profile := high_profile G t bad
  have hcard : (high G).card=9 := by unfold bound at bad; omega
  have p : ({0,1}:Finset Nat) ⊆ types G := by
    intro k hk
    simp only [mem_insert,mem_singleton] at hk
    rcases hk with rfl|rfl
    · exact (PositivePalette.failure_requires_odd_zero G bad).2
    · have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_self ..)
      have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
      have pos := (TrianglePrune.triangle_iff G e).mpr ⟨a,b,ea,eb,ab⟩

      have cap := Repair.triangles_le_choose G e
      rw [de, Nat.choose_self] at cap
      exact mem_image.mpr ⟨e,mem_univ _,by omega⟩
  let S := types G \ {0,1}
  have sz : S.card=9 := by
    rw [card_sdiff p,t]
    decide
  have sub : S ⊆ (high G).image (trianglesAt G) := by
    intro k hk
    obtain ⟨ka,kn⟩ := mem_sdiff.mp hk
    obtain ⟨v,_,rfl⟩ := mem_image.mp ka
    refine mem_image.mpr ⟨v,?_,rfl⟩
    by_contra out
    have ds : G.degree v≤2 := by
      by_contra! z
      exact out (mem_filter.mpr ⟨mem_univ _,z⟩)

    have lim := (Repair.triangles_le_choose G v).trans (Nat.choose_le_choose 2 ds)
    rw [Nat.choose_self] at lim
    simp only [mem_insert,mem_singleton,not_or] at kn
    omega
  have eqc : ((high G).image (trianglesAt G)).card=(high G).card := by
    have low := card_le_card sub
    have up := card_image_le (s:=high G) (f:=trianglesAt G)
    omega
  have eq : S=(high G).image (trianglesAt G) := eq_of_subset_of_card_le sub (by omega)
  refine ⟨hcard,card_image_iff.mp eqc,?_⟩
  intro v hv
  have m : trianglesAt G v∈S := eq.symm ▸ mem_image.mpr ⟨v,hv,rfl⟩
  have n := (mem_sdiff.mp m).2
  simp only [mem_insert,mem_singleton,not_or] at n
  omega

#print axioms triangle_supported_reduction
#print axioms ten_to_fifteen
#print axioms ear_profile
end Graffiti384b.DiversityEleven
