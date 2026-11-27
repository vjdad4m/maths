import CubicExtra
namespace Graffiti384b.TwoEars
open Finset SimpleGraph
open private Repair.linkEdges Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The two nonadjacent neighbors of a cubic score-two vertex protect the
vertex and its remaining neighbor simultaneously. -/
def Protects (v : V) (A : Finset V) := A.card=2 ∧ A⊆G.neighborFinset v ∧
    ∀ w∈G.neighborFinset v,w∉A → A⊆G.neighborFinset w

theorem protecting_pair {v : V} (d : G.degree v=3) (s : trianglesAt G v=2) :
    ∃ A,Protects G v A := by
  classical
  let N := G.neighborFinset v
  have ns : N.card=3 := (card_neighborFinset_eq_degree ..).trans d
  have miss : ∃ x∈N,∃ y∈N,x≠y ∧ ¬G.Adj x y := by
    by_contra! full
    have sub : N.powersetCard 2⊆Repair.linkEdges G v := fun p pm => mem_filter.mpr
      ⟨pm,fun x xm y ym xy => full x ((mem_powersetCard.mp pm).1 xm) y ((mem_powersetCard.mp pm).1 ym) xy⟩
    have ct := card_le_card sub
    rw [card_powersetCard,ns] at ct
    change (3:ℕ).choose 2≤trianglesAt G v at ct
    rw [s] at ct; exact (by decide : ¬(3:ℕ).choose 2≤2) ct
  obtain ⟨x,xm,y,ym,xy,miss⟩ := miss
  let A : Finset V := {x,y}
  have inc : A⊆N := insert_subset xm (singleton_subset_iff.mpr ym)
  have size : (N\A).card=1 := by rw [card_sdiff inc,ns,show A.card=2 from card_pair xy]
  refine ⟨A,card_pair xy,inc,?_⟩
  intro w wn wa i ia
  have vi := (G.mem_neighborFinset ..).mp (inc ia)
  obtain ⟨j,vj,ij⟩ := PositiveCore33.cubic_supported G d s.ge vi
  have jo : j∉A := by
    intro ja
    simp only [A,mem_insert,mem_singleton] at ia ja
    rcases ia with rfl|rfl <;> rcases ja with rfl|rfl <;>
      first | exact (G.loopless _ ij) | exact miss ij | exact miss ij.symm
  have jw := card_le_one.mp size.le j (mem_sdiff.mpr ⟨(G.mem_neighborFinset ..).mpr vj,jo⟩) w (mem_sdiff.mpr ⟨wn,wa⟩)
  exact (G.mem_neighborFinset ..).mpr (jw ▸ ij.symm)

end Graffiti384b.TwoEars
#print axioms Graffiti384b.TwoEars.protecting_pair
