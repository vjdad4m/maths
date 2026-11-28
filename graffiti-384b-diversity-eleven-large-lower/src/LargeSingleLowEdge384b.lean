import FiveLowEars384b
import HighTwoUntouched384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- If the low exterior of a 14- or 15-nonleaf supported lower profile
contains exactly one low-low edge, it satisfies the exact bound. -/
theorem exact_large_single_low_edge (sup : Supported G)
    (t : (types G).card=11) (nine : (high G).card=9)
    (large : 14≤(nonleaves G).card)
    {e f : V} (ef : G.Adj e f)
    (eL : e∈nonleaves G \ high G) (fL : f∈nonleaves G \ high G)
    (pair : ∀ x∈nonleaves G \ high G,∀ y∈nonleaves G \ high G,
      G.Adj x y → (x=e ∧ y=f) ∨ (x=f ∧ y=e)) :
    gamma G≤bound G := by
  classical
  by_contra! bad
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
  have anch : ∀ x∈Ord,∀ y,G.Adj x y → y∈high G := by
    intro x xm y xy
    obtain ⟨z,xz,yz⟩ := sup xy
    have p : ({x,z} : Finset V) ⊆ G.neighborFinset y := insert_subset
      ((G.mem_neighborFinset ..).mpr xy.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr yz))
    have d := card_le_card p
    rw [card_pair xz.ne,card_neighborFinset_eq_degree] at d
    have yn : y∈nonleaves G := mem_filter.mpr ⟨mem_univ _,d⟩
    by_contra yh
    have xO := (mem_erase.mp xm).2
    rcases pair x (mem_erase.mp xO).2 y (mem_sdiff.mpr ⟨yn,yh⟩) xy with ⟨h,_⟩|⟨h,_⟩
    · exact (mem_erase.mp xm).1 h
    · exact (mem_erase.mp xO).1 h
  have maxq := (ten_to_fifteen G t bad).2
  have case_ : O.card=4 ∨ O.card=5 := by omega
  rcases case_ with four|five
  · let N := fun x => G.neighborFinset x ∩ high G
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
    have seven : P.card≤7 := by
      have c := card_biUnion_le (s:=O) (t:=N)
      have sum : (∑ x ∈ Ord,(N x).card)≤6 := by
        calc
          (∑ x ∈ Ord,(N x).card)≤∑ _ ∈ Ord,2 :=
            sum_le_sum (fun x xm => all x (mem_erase.mp xm).2)
          _≤6 := by simp; omega
      have se := sum_erase_add O (fun x => (N x).card) em
      change (∑ x ∈ Ord,(N x).card)+(N e).card=(∑ x ∈ O,(N x).card) at se
      change P.card≤(∑ x ∈ O,(N x).card) at c
      omega
    exact (not_le_of_gt bad) (exact_of_four_low_footprint_seven G t nine four.ge
      lo (fun x xm=>(dg x xm).ge) ind
      (fun z zh ⟨x,xm,xz⟩ => mem_biUnion.mpr ⟨x,xm,mem_inter.mpr
        ⟨(G.mem_neighborFinset ..).mpr xz,zh⟩⟩) seven)
  · exact (not_le_of_gt bad) (exact_of_five_with_three_ordinary G t nine five lo dg ind (Ord:=Ord)
      (erase_subset _ _) (by omega) anch)

#print axioms exact_large_single_low_edge
end Graffiti384b.DiversityEleven
