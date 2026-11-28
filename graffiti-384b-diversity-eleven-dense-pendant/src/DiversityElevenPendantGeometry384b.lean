import DiversityElevenPendantBoard384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private Repair.nbr_add Repair.edge_info Repair.linkEdges from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem nonleaf_of_supported_adj (sup : Supported G) {x y : V} (xy : G.Adj x y) :
    y∈nonleaves G := by
  obtain ⟨z,xz,yz⟩ := sup xy
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  have inc : ({x,z}:Finset V) ⊆ G.neighborFinset y := by
    intro v vm
    simp only [mem_insert,mem_singleton] at vm
    rcases vm with rfl|rfl
    · exact (G.mem_neighborFinset ..).mpr xy.symm
    · exact (G.mem_neighborFinset ..).mpr yz
  have n := card_le_card inc
  rwa [card_pair xz.ne,card_neighborFinset_eq_degree] at n

/-- Outside the high pendant anchor, no board vertex can see either low
vertex, and each board vertex has at least two neighbors on the board.
A vertex missing the anchor retains its full degree and neighborhood. -/
theorem pendant_board_local (sup : Supported G)
    {e f a : V} (ah : a∈high G) (low : nonleaves G \ high G={e,f})
    (en : G.neighborFinset e={f,a}) (fn : G.neighborFinset f={e,a})
    {v : V} (vm : v∈(high G).erase a) :
    (∀ w,G.Adj v w → w∈high G) ∧
      nbr G v ((high G).erase a)+(if G.Adj v a then 1 else 0)=G.degree v := by
  classical
  obtain ⟨va,vh⟩ := mem_erase.mp vm
  have el : e∉high G := (mem_sdiff.mp (low ▸ mem_insert_self _ _)).2
  have fl : f∉high G := (mem_sdiff.mp (low ▸ mem_insert_of_mem (mem_singleton_self _))).2
  have hn : ∀ w,G.Adj v w → w∈high G := by
    intro w vw
    by_cases wh : w∈high G
    · exact wh
    exfalso
    have wl := mem_sdiff.mpr ⟨nonleaf_of_supported_adj G sup vw,wh⟩
    rw [low,mem_insert,mem_singleton] at wl
    rcases wl with rfl|rfl
    · have m := (G.mem_neighborFinset ..).mpr vw.symm
      rw [en,mem_insert,mem_singleton] at m
      exact m.elim (fun vf => fl (vf ▸ vh)) va
    · have m := (G.mem_neighborFinset ..).mpr vw.symm
      rw [fn,mem_insert,mem_singleton] at m
      exact m.elim (fun ve => el (ve ▸ vh)) va
  refine ⟨hn,?_⟩
  have d : Disjoint ((high G).erase a) ({a}:Finset V) :=
    disjoint_left.mpr (fun _ x y => (mem_erase.mp x).1 (mem_singleton.mp y))
  have all : (high G).erase a ∪ {a}=high G := by
    rw [union_comm,←insert_eq]
    exact insert_erase ah
  have fset : (high G).filter (G.Adj v)=G.neighborFinset v := by
    ext w
    rw [mem_filter,G.mem_neighborFinset]
    exact ⟨And.right,fun h => ⟨hn w h,h⟩⟩
  have one : nbr G v {a}=(if G.Adj v a then 1 else 0) := by
    unfold nbr
    rw [filter_singleton]
    split <;> simp
  rw [←one,←Repair.nbr_add G v d,all]
  exact (congrArg card fset).trans (G.card_neighborFinset_eq_degree v)

#print axioms pendant_board_local
end Graffiti384b.DiversityEleven
