import EightFinite180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
namespace Minimal180.PairRepair.Eight
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 Substitution Transversals
theorem leaves : weightedLeaves G P=3 := by
  let C : Finset V := {0,5,7}
  have con : Con G C := con_insert G (con_insert G (con_single G (7:V)) (mem_singleton_self _) (by decide : G.Adj 5 7))
    (show (7:V)∈({5,7}:Finset V) by decide) (by decide : G.Adj 0 7)
  have low := weightedCore G C P con (by dsimp [C,Dominates];decide)
  have val : (P\C).card=3 := by decide
  rw [val] at low
  obtain ⟨T,sub,tr,opt⟩ := tree_opt G data.1 P
  let L := P∩Graffiti177.leaves T
  have ct : L.card=weightedLeaves G P := opt
  by_contra neq
  have lp : L⊆P := inter_subset_left
  have five : P.card=5 := by decide
  have nmiss : (P\L).card≤1 := by have := card_sdiff_add_card_eq_card lp;omega
  have other {a b : V} (ap : a∈P) (bp : b∈P) (ne : a≠b) (miss : a∉L) : b∈L := by
    apply Classical.byContradiction
    intro bm
    have sub : ({a,b}:Finset V)⊆P\L := insert_subset (mem_sdiff.mpr ⟨ap,miss⟩)
      (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨bp,bm⟩))
    have sz := card_le_card sub
    rw [card_pair ne] at sz
    omega
  have cc := (leaf_core G T sub tr (by decide) L inter_subset_right).1
  have isolated (u v : V) (up : u∉P) (vp : v∉P) (uv : u≠v) (allN : G.neighborFinset u⊆L) : False := by
    have um : u∈univ\L := mem_sdiff.mpr ⟨mem_univ _,fun m => up (lp m)⟩
    have vm : v∈univ\L := mem_sdiff.mpr ⟨mem_univ _,fun m => vp (lp m)⟩
    have no (z : V) (zm : z∈univ\L) (ed : G.Adj u z) : False :=
      (mem_sdiff.mp zm).2 (allN ((G.mem_neighborFinset u z).mpr ed))
    have same := ((connected_cuts G _).mp cc).2 (fun x => decide (x=u))
    have stable : OnEdges G (univ\L) (fun x => decide (x=u)) := by
      intro x xm y ym ed
      have nx : x≠u := fun eq => no y ym (eq ▸ ed)
      have ny : y≠u := fun eq => no x xm (eq ▸ ed.symm)
      simp [nx,ny]
    have eq := same stable u um v vm
    simp [uv.symm] at eq
  by_cases zero : (0:V)∈L
  · by_cases seven : (7:V)∈L
    · apply isolated 3 5 (by decide) (by decide) (by decide)
      rw [show G.neighborFinset 3=({0,7}:Finset V) by decide]
      exact insert_subset zero (singleton_subset_iff.mpr seven)
    · apply isolated 6 3 (by decide) (by decide) (by decide)
      rw [show G.neighborFinset 6=({0,2,4}:Finset V) by decide]
      exact insert_subset zero (insert_subset (other (by decide) (by decide) (by decide) seven)
        (singleton_subset_iff.mpr (other (by decide) (by decide) (by decide) seven)))
  · apply isolated 5 3 (by decide) (by decide) (by decide)
    rw [show G.neighborFinset 5=({1,2,7}:Finset V) by decide]
    exact insert_subset (other (by decide) (by decide) (by decide) zero)
      (insert_subset (other (by decide) (by decide) (by decide) zero)
        (singleton_subset_iff.mpr (other (by decide) (by decide) (by decide) zero)))

#print axioms Eight.leaves
end Minimal180.PairRepair.Eight
