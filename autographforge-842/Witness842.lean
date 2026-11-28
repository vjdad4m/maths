import StarCone
import Proof324

namespace AutoGraphForge842
open SimpleGraph Finset

abbrev V := Fin 2 × Fin 7

def Hub (v : V) : Prop := v.2.val < 2
instance (v : V) : Decidable (Hub v) := by unfold Hub; infer_instance

def adj (u v : V) : Prop :=
  (u.1 = v.1 ∧ ((Hub u ∧ ¬ Hub v) ∨ (Hub v ∧ ¬ Hub u))) ∨
    (u = (0,1) ∧ v = (1,0)) ∨ (v = (0,1) ∧ u = (1,0))

instance (u v : V) : Decidable (adj u v) := by unfold adj; infer_instance

def graph : SimpleGraph V where
  Adj := adj
  symm := by intro u v; unfold adj; rw [eq_comm (a := u.1)]; tauto
  loopless := by intro u; unfold adj; have hn : ((0,1) : V) ≠ (1,0) := by decide
                 aesop

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (adj u v))

theorem order : Fintype.card V = 14 := by decide

theorem triangle_free : ∀ a b c : V, graph.Adj a b → graph.Adj b c → ¬graph.Adj c a := by
  decide

def leaves (i : Fin 2) : Finset V :=
  univ.filter (fun v => v.1 = i ∧ ¬ Hub v)

theorem leaves_card : ∀ i, (leaves i).card = 5 := by decide

private theorem same_neighbors :
    ∀ (i : Fin 2) (x y z : V), x ∈ leaves i → y ∈ leaves i →
      graph.Adj z x → graph.Adj z y := by decide

private theorem leaves_disjoint : Disjoint (leaves 0) (leaves 1) := by decide

private theorem disjoint_step {i : Fin 2} {F S : Finset V} (hF : F ⊆ leaves i)
    (large : 2 < F.card) (hS : Disjoint F S) :
    Disjoint F (StarCone.step graph 2 S) := by
  rw [Finset.disjoint_left] at hS ⊢
  intro w hw hit
  rw [StarCone.step,mem_union] at hit
  rcases hit with old | new
  · exact hS hw old
  rcases (mem_filter.mp new).2 with ⟨_,z,_,ez,num⟩
  have sub : F ⊆ graph.neighborFinset z \ S := by
    intro u hu
    exact mem_sdiff.mpr ⟨(graph.mem_neighborFinset z u).mpr
      (same_neighbors i w u z (hF hw) (hF hu) ez),hS hu⟩
  exact (not_le_of_gt large) ((card_le_card sub).trans num)

private theorem disjoint_iterate {i : Fin 2} {F S : Finset V} (hF : F ⊆ leaves i)
    (large : 2 < F.card) (hS : Disjoint F S) (j : ℕ) :
    Disjoint F ((StarCone.step graph 2)^[j] S) := by
  induction j with
  | zero => exact hS
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact disjoint_step hF large ih

theorem each_side_needs_three (S : Finset V) (full : StarCone.full graph 2 S) (i : Fin 2) :
    3 ≤ (leaves i ∩ S).card := by
  by_contra! small
  let F := leaves i \ S
  have sum := card_sdiff_add_card_inter (leaves i) S
  have big : 2 < F.card := by rw [leaves_card] at sum; dsimp [F]; omega
  have miss : Disjoint F S := by
    rw [Finset.disjoint_left]
    exact fun _ hw => (mem_sdiff.mp hw).2
  have dis := disjoint_iterate (F := F) (S := S) sdiff_subset big miss (Fintype.card V)
  change (StarCone.step graph 2)^[Fintype.card V] S = univ at full
  rw [full,Finset.disjoint_left] at dis
  obtain ⟨w,hw⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
  exact dis hw (mem_univ _)

private def seeds : Finset V := {(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)}

theorem forcing_exact : StarCone.forcing graph 2 = 6 := by
  let sizes := {r : ℕ | ∃ S : Finset V, S.card = r ∧ StarCone.full graph 2 S ∧ True}
  have hc : seeds.card = 6 := by decide
  have hf : StarCone.full graph 2 seeds := by unfold StarCone.full; decide
  have mem : 6 ∈ sizes := ⟨seeds,hc,hf,trivial⟩
  change sInf sizes = 6
  refine le_antisymm (Nat.sInf_le mem) ?_
  obtain ⟨S,hs,full,_⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨6,mem⟩)
  have n0 := each_side_needs_three S full 0
  have n1 := each_side_needs_three S full 1
  have dis : Disjoint (leaves 0 ∩ S) (leaves 1 ∩ S) :=
    leaves_disjoint.mono inter_subset_left inter_subset_left
  have sub : (leaves 0 ∩ S) ∪ (leaves 1 ∩ S) ⊆ S :=
    union_subset inter_subset_right inter_subset_right
  have le := card_le_card sub
  rw [card_union_of_disjoint dis,hs] at le
  omega

open private residueAux descending descending_perm descending_sorted from Proof324

private def degrees : List ℕ := [6,6,5,5,2,2,2,2,2,2,2,2,2,2]

private theorem sorted_degrees : descending (Graffiti324.degreeList graph) = degrees := by
  let L := Graffiti324.degreeList graph
  have bag : (L : Multiset ℕ) = (degrees : Multiset ℕ) := by
    dsimp [L,Graffiti324.degreeList]
    rw [← Multiset.map_coe,Finset.coe_toList]
    have exactBag : (univ.val.map (fun v : V => graph.degree v)) = (degrees : Multiset ℕ) := by decide
    convert exactBag using 2; (congr 1; exact Subsingleton.elim _ _)
  exact List.eq_of_perm_of_sorted ((descending_perm L).trans (Multiset.coe_eq_coe.mp bag))
    (descending_sorted L) (by unfold degrees; decide)

theorem residue_exact : Graffiti324.residue graph = 5 := by
  have len : (Graffiti324.degreeList graph).length = 14 := by
    simp [Graffiti324.degreeList,order]
  change residueAux (Graffiti324.degreeList graph).length (Graffiti324.degreeList graph) = _
  rw [len,residueAux,sorted_degrees]
  unfold degrees
  change residueAux 13 [5, 4, 4, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2] = 5
  have s0 : descending [5, 4, 4, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2] = [5, 4, 4, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s0]
  change residueAux 12 [3, 3, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1] = 5
  have s1 : descending [3, 3, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1] = [3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s1]
  change residueAux 11 [2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1] = 5
  have s2 : descending [2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1] = [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s2]
  change residueAux 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = 5
  have s3 : descending [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s3]
  change residueAux 9 [0, 1, 1, 1, 1, 1, 1, 1, 1] = 5
  have s4 : descending [0, 1, 1, 1, 1, 1, 1, 1, 1] = [1, 1, 1, 1, 1, 1, 1, 1, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s4]
  change residueAux 8 [0, 1, 1, 1, 1, 1, 1, 0] = 5
  have s5 : descending [0, 1, 1, 1, 1, 1, 1, 0] = [1, 1, 1, 1, 1, 1, 0, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s5]
  change residueAux 7 [0, 1, 1, 1, 1, 0, 0] = 5
  have s6 : descending [0, 1, 1, 1, 1, 0, 0] = [1, 1, 1, 1, 0, 0, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s6]
  change residueAux 6 [0, 1, 1, 0, 0, 0] = 5
  have s7 : descending [0, 1, 1, 0, 0, 0] = [1, 1, 0, 0, 0, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s7]
  change residueAux 5 [0, 0, 0, 0, 0] = 5
  have s8 : descending [0, 0, 0, 0, 0] = [0, 0, 0, 0, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s8]
  rfl

theorem connected : graph.Connected := by
  have stepSide : ∀ x : V, Hub x → graph.Adj x ((x.1,2) : V) := by decide
  have leafStep : ∀ x : V, ¬Hub x → graph.Adj x ((x.1,0) : V) := by decide
  have bridge : graph.Adj (0,1) (1,0) := by decide
  have path01 : graph.Reachable (0,0) (0,1) :=
    (show graph.Adj (0,0) (0,2) from by decide).reachable.trans
      (show graph.Adj (0,2) (0,1) from by decide).reachable
  have reach0 : ∀ x : V, graph.Reachable x ((x.1,0) : V) := by
    intro x
    by_cases hx : Hub x
    · exact (stepSide x hx).reachable.trans (leafStep (x.1,2) (by intro q; change 2 < 2 at q; omega)).reachable
    · exact (leafStep x hx).reachable
  have finish (x : V) : graph.Reachable x (0,0) := by
    have cases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    rcases cases x.1 with h|h
    · simpa [h] using reach0 x
    · exact (by simpa [h] using reach0 x : graph.Reachable x (1,0)).trans
        (bridge.symm.reachable.trans path01.symm)
  exact ⟨fun x y => (finish x).trans (finish y).symm⟩

#print axioms forcing_exact
#print axioms residue_exact
#print axioms connected
end AutoGraphForge842
