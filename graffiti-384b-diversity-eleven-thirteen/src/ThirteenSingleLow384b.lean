import ThreeUntouched384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The 13-nonleaf lower profile with one low-low edge satisfies the exact bound. -/
theorem exact_thirteen_single_low_edge
    (t : (types G).card=11) (nine : (high G).card=9)
    (count : (nonleaves G).card=13)
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (min : ∀ x∈high G,2≤trianglesAt G x)
    {e f : V} (ef : G.Adj e f)
    (eL : e∈nonleaves G \ high G) (fL : f∈nonleaves G \ high G)
    (pair : ∀ x∈nonleaves G \ high G,∀ y∈nonleaves G \ high G,
      G.Adj x y → (x=e ∧ y=f) ∨ (x=f ∧ y=e)) :
    gamma G≤bound G := by
  classical
  let L := nonleaves G \ high G
  let O := L.erase f
  let Ord := O.erase e
  have em : e∈O := mem_erase.mpr ⟨ef.ne,eL⟩
  have lo : Disjoint O (high G) :=
    Finset.disjoint_left.mpr (fun _ xo xh => (mem_sdiff.mp (mem_erase.mp xo).2).2 xh)
  have sub : high G ⊆ nonleaves G := by
    intro x xh
    have dg := (mem_filter.mp xh).2
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have counts : O.card+10=(nonleaves G).card := by
    have c := card_sdiff_add_card_eq_card sub
    change L.card + (high G).card=(nonleaves G).card at c
    have er : O.card=L.card-1 := card_erase_of_mem fL
    have pos := card_pos.mpr ⟨f,fL⟩
    change 0<L.card at pos
    omega
  have ordcard : Ord.card=O.card-1 := card_erase_of_mem em
  have dg (x : V) (xm : x∈O) : G.degree x=2 := by
    obtain ⟨xn,xh⟩ := mem_sdiff.mp (mem_erase.mp xm).2
    have up : ¬3≤G.degree x := fun d => xh (mem_filter.mpr ⟨mem_univ _,d⟩)
    have dn := (mem_filter.mp xn).2
    omega
  have ind : ∀ x∈O,∀ y∈O,¬G.Adj x y := by
    intro x xm y ym xy
    rcases pair x (mem_erase.mp xm).2 y (mem_erase.mp ym).2 xy with ⟨_,h⟩|⟨h,_⟩
    · exact (mem_erase.mp ym).1 h
    · exact (mem_erase.mp xm).1 h
  have three : O.card=3 := by omega
  let N := fun x => G.neighborFinset x ∩ high G
  let P := O.biUnion N
  have all (x : V) (xm : x∈O) : (N x).card≤2 := by
    have c := card_le_card (show N x ⊆ G.neighborFinset x from inter_subset_left)
    rwa [card_neighborFinset_eq_degree,dg x xm] at c
  have one : (N e).card≤1 := by
    have sub : N e ⊆ (G.neighborFinset e).erase f := by
      intro x xm
      obtain ⟨xe,xh⟩ := mem_inter.mp xm
      exact mem_erase.mpr ⟨fun eq => (mem_sdiff.mp fL).2 (eq ▸ xh),xe⟩
    have c := card_le_card sub
    rw [card_erase_of_mem ((G.mem_neighborFinset ..).mpr ef),
      card_neighborFinset_eq_degree,dg e em] at c
    simpa using c
  have five : P.card≤5 := by
    have c := card_biUnion_le (s:=O) (t:=N)
    have sum : (∑ x ∈ Ord,(N x).card)≤4 := by
      calc
        (∑ x ∈ Ord,(N x).card)≤∑ _ ∈ Ord,2 :=
          sum_le_sum (fun x xm => all x (mem_erase.mp xm).2)
        _≤4 := by simp; omega
    have se := sum_erase_add O (fun x => (N x).card) em
    change (∑ x ∈ Ord,(N x).card)+(N e).card=(∑ x ∈ O,(N x).card) at se
    change P.card≤(∑ x ∈ O,(N x).card) at c
    omega
  exact exact_of_three_low_footprint_five G t nine scores min three.ge
    lo (fun x xm=>(dg x xm).ge) ind
    (fun z zh ⟨x,xm,xz⟩ => mem_biUnion.mpr ⟨x,xm,mem_inter.mpr
      ⟨(G.mem_neighborFinset ..).mpr xz,zh⟩⟩) five

#print axioms exact_thirteen_single_low_edge
end Graffiti384b.DiversityEleven
