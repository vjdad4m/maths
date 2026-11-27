import RootPorts180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In any failed rank-two marking, every tree with internal root pays for
both its leaves and the internal vertices outside the two marks. -/
theorem internal_budget {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) {T : SimpleGraph V} (tg : T≤G) (tree : T.IsTree)
    (root : r∉leaves T) :
    let P := parity G r odd
    (leaves T).card + ((univ \ (A∪P)) \ leaves T).card ≤ (A∩P).card+2 := by
  classical
  intro P
  let U := eligible A P r
  let O := univ \ (A∪P)
  let L := leaves T
  have budget : (U∩L).card ≤ weightedLeaves G U :=
    le_sup (f:=fun M => (U∩leaves M).card) (mem_filter.mpr ⟨mem_univ _,tg,tree⟩)
  have equal : L\O=U∩L := by
    ext i
    constructor
    · intro hi
      obtain ⟨il,out⟩ := mem_sdiff.mp hi
      have marked : i∈A∪P := Classical.byContradiction (fun no => out (mem_sdiff.mpr ⟨mem_univ _,no⟩))
      exact mem_inter.mpr ⟨eligible_iff.mpr ⟨mem_union.mp marked,Or.inl (fun eq => root (eq ▸ il))⟩,il⟩
    · intro hi
      obtain ⟨iu,il⟩ := mem_inter.mp hi
      exact mem_sdiff.mpr ⟨il,fun io => (mem_sdiff.mp io).2 (mem_union.mpr (eligible_iff.mp iu).1)⟩
  have split := card_sdiff_add_card_inter L O
  rw [equal,inter_comm L O] at split
  have outside := card_sdiff_add_card_inter O L
  have order : O.card + (A∪P).card = Fintype.card V := by
    simpa [O] using card_sdiff_add_card_inter (univ : Finset V) (A∪P)
  have marks := card_union_add_card_inter A P
  have rk := h.rank
  have fail := h.bad
  change weightedLeaves G U+bipartiteNum G<1+A.card+P.card at fail
  change L.card + (O\L).card ≤ (A∩P).card+2
  omega

/-- Once all other edges at u are removed, u is a leaf and its neighbor r
is internal in every spanning tree, for graphs of order at least three. -/
theorem port_internal {G T : SimpleGraph V} {r u : V} (tg : T≤prune G u {r})
    (tree : T.IsTree) (order : 2<Fintype.card V) : u∈leaves T ∧ r∉leaves T := by
  classical
  have only {z : V} (e : T.Adj u z) : z=r := mem_singleton.mp ((tg e).2.1 rfl)
  have leaf := leaf_of_unique T tree.isConnected (by omega) u (fun a b => (only a).trans (only b).symm)
  obtain ⟨z,uz⟩ := exists_adj T tree.isConnected (by omega) u
  exact ⟨leaf,leaves_nonadjacent T tree order (only uz ▸ uz) leaf⟩

/-- Each of the root's neighbors separately gives an unrestricted ordinary
maximum-leaf bound in the graph obtained by pruning that neighbor to r. -/
theorem port_leaves {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) (u : V) :
    Short177.maxLeaves (prune G u {r}) ≤ (A∩parity G r odd).card+2 := by
  classical
  apply Finset.sup_le
  intro T mem
  obtain ⟨tj,tree⟩ := (mem_filter.mp mem).2
  have root := (port_internal tj tree h.order).2
  have bound := internal_budget h (tj.trans (prune_le ..)) tree root
  change (leaves T).card≤_
  omega

#print axioms internal_budget
#print axioms port_internal
#print axioms port_leaves
end Minimal180.RootEar
