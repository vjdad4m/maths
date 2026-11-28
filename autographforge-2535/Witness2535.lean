import StarCone
import Proof324

namespace AutoGraphForge2535
open SimpleGraph Finset
set_option maxHeartbeats 0
set_option maxRecDepth 16384

abbrev V := Fin 3 × Fin 8

def Hub (v : V) : Prop := v.2.val < 2
instance (v : V) : Decidable (Hub v) := by unfold Hub; infer_instance

def adj (u v : V) : Prop :=
  (u.1 = v.1 ∧ ((Hub u ∧ ¬ Hub v) ∨ (Hub v ∧ ¬ Hub u))) ∨
    (u = (0,1) ∧ v = (1,0)) ∨ (v = (0,1) ∧ u = (1,0)) ∨
    (u = (1,1) ∧ v = (2,0)) ∨ (v = (1,1) ∧ u = (2,0))

instance (u v : V) : Decidable (adj u v) := by unfold adj; infer_instance

def graph : SimpleGraph V where
  Adj := adj
  symm := by intro u v; unfold adj; rw [eq_comm (a := u.1)]; tauto
  loopless := by intro u; unfold adj; have hn : ((0,1) : V) ≠ (1,0) := by decide
                 have hm : ((1,1) : V) ≠ (2,0) := by decide
                 aesop

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (adj u v))

theorem order : Fintype.card V = 24 := by decide

def leaves (i : Fin 3) : Finset V :=
  univ.filter (fun v => v.1 = i ∧ ¬ Hub v)

theorem leaves_card : ∀ i, (leaves i).card = 6 := by decide

private theorem same_neighbors :
    ∀ (i : Fin 3) (x y z : V), x ∈ leaves i → y ∈ leaves i →
      graph.Adj z x → graph.Adj z y := by decide

private theorem leaves_disjoint : ∀ i j : Fin 3, i ≠ j →
    Disjoint (leaves i) (leaves j) := by decide

private theorem disjoint_step {i : Fin 3} {F S : Finset V} (hF : F ⊆ leaves i)
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

private theorem disjoint_iterate {i : Fin 3} {F S : Finset V} (hF : F ⊆ leaves i)
    (large : 2 < F.card) (hS : Disjoint F S) (j : ℕ) :
    Disjoint F ((StarCone.step graph 2)^[j] S) := by
  induction j with
  | zero => exact hS
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact disjoint_step hF large ih

theorem each_side_needs_four (S : Finset V) (full : StarCone.full graph 2 S) (i : Fin 3) :
    4 ≤ (leaves i ∩ S).card := by
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

private def seeds : Finset V := {(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5)}

theorem forcing_exact : StarCone.forcing graph 2 = 12 := by
  let sizes := {r : ℕ | ∃ S : Finset V, S.card = r ∧ StarCone.full graph 2 S ∧ True}
  have hc : seeds.card = 12 := by decide
  have hf : StarCone.full graph 2 seeds := by unfold StarCone.full; decide
  have mem : 12 ∈ sizes := ⟨seeds,hc,hf,trivial⟩
  change sInf sizes = 12
  refine le_antisymm (Nat.sInf_le mem) ?_
  obtain ⟨S,hs,full,_⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨12,mem⟩)
  have n0 := each_side_needs_four S full 0
  have n1 := each_side_needs_four S full 1
  have n2 := each_side_needs_four S full 2
  have d01 : Disjoint (leaves 0 ∩ S) (leaves 1 ∩ S) :=
    (leaves_disjoint 0 1 (by decide)).mono inter_subset_left inter_subset_left
  have d02 : Disjoint (leaves 0 ∩ S) (leaves 2 ∩ S) :=
    (leaves_disjoint 0 2 (by decide)).mono inter_subset_left inter_subset_left
  have d12 : Disjoint (leaves 1 ∩ S) (leaves 2 ∩ S) :=
    (leaves_disjoint 1 2 (by decide)).mono inter_subset_left inter_subset_left
  have d : Disjoint ((leaves 0 ∩ S) ∪ (leaves 1 ∩ S)) (leaves 2 ∩ S) :=
    Finset.disjoint_union_left.mpr ⟨d02,d12⟩
  have sub : (leaves 0 ∩ S) ∪ (leaves 1 ∩ S) ∪ (leaves 2 ∩ S) ⊆ S :=
    union_subset (union_subset inter_subset_right inter_subset_right) inter_subset_right
  have le := card_le_card sub
  rw [card_union_of_disjoint d,card_union_of_disjoint d01,hs] at le
  omega

open private residueAux descending descending_perm descending_sorted from Proof324

private def degrees : List ℕ := [7, 7, 7, 7, 6, 6, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

private theorem sorted_degrees : descending (Graffiti324.degreeList graph) = degrees := by
  let L := Graffiti324.degreeList graph
  have bag : (L : Multiset ℕ) = (degrees : Multiset ℕ) := by
    dsimp [L,Graffiti324.degreeList]
    rw [← Multiset.map_coe,Finset.coe_toList]
    have exactBag : (univ.val.map (fun v : V => graph.degree v)) = (degrees : Multiset ℕ) := by decide
    convert exactBag using 2; (congr 1; exact Subsingleton.elim _ _)
  exact List.eq_of_perm_of_sorted ((descending_perm L).trans (Multiset.coe_eq_coe.mp bag))
    (descending_sorted L) (by unfold degrees; decide)

theorem residue_exact : Graffiti324.residue graph = 8 := by
  have len : (Graffiti324.degreeList graph).length = 24 := by
    simp [Graffiti324.degreeList,order]
  change residueAux (Graffiti324.degreeList graph).length (Graffiti324.degreeList graph) = _
  rw [len,residueAux,sorted_degrees]
  unfold degrees
  change residueAux 23 [6, 6, 6, 5, 5, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] = 8
  have s23 : descending [6, 6, 6, 5, 5, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] = [6, 6, 6, 5, 5, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s23]
  change residueAux 22 [5, 5, 4, 4, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1] = 8
  have s22 : descending [5, 5, 4, 4, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1] = [5, 5, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s22]
  change residueAux 21 [4, 3, 3, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1] = 8
  have s21 : descending [4, 3, 3, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1] = [4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s21]
  change residueAux 20 [2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1] = 8
  have s20 : descending [2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1] = [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s20]
  change residueAux 19 [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1] = 8
  have s19 : descending [1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1] = [2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s19]
  change residueAux 18 [1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = 8
  have s18 : descending [1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = [2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s18]
  change residueAux 17 [1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = 8
  have s17 : descending [1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s17]
  change residueAux 16 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = 8
  have s16 : descending [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s16]
  change residueAux 15 [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = 8
  have s15 : descending [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s15]
  change residueAux 14 [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] = 8
  have s14 : descending [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s14]
  change residueAux 13 [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0] = 8
  have s13 : descending [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0] = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s13]
  change residueAux 12 [0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0] = 8
  have s12 : descending [0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0] = [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s12]
  change residueAux 11 [0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0] = 8
  have s11 : descending [0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0] = [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s11]
  change residueAux 10 [0, 1, 1, 1, 1, 0, 0, 0, 0, 0] = 8
  have s10 : descending [0, 1, 1, 1, 1, 0, 0, 0, 0, 0] = [1, 1, 1, 1, 0, 0, 0, 0, 0, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s10]
  change residueAux 9 [0, 1, 1, 0, 0, 0, 0, 0, 0] = 8
  have s9 : descending [0, 1, 1, 0, 0, 0, 0, 0, 0] = [1, 1, 0, 0, 0, 0, 0, 0, 0] := by
    apply List.eq_of_perm_of_sorted ((descending_perm _).trans ?_) (descending_sorted _)
    · decide +kernel
    · decide +kernel
  rw [residueAux,s9]
  change residueAux 8 [0, 0, 0, 0, 0, 0, 0, 0] = 8
  have s8 : descending [0, 0, 0, 0, 0, 0, 0, 0] = [0, 0, 0, 0, 0, 0, 0, 0] := by
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
  have secondBridge : graph.Adj (1,1) (2,0) := by decide
  have middlePath : graph.Reachable (1,0) (1,1) :=
    (show graph.Adj (1,0) (1,2) from by decide).reachable.trans
      (show graph.Adj (1,2) (1,1) from by decide).reachable
  have finish (x : V) : graph.Reachable x (0,0) := by
    have cases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases cases x.1 with h|h|h
    · simpa [h] using reach0 x
    · exact (by simpa [h] using reach0 x : graph.Reachable x (1,0)).trans
        (bridge.symm.reachable.trans path01.symm)
    · exact (by simpa [h] using reach0 x : graph.Reachable x (2,0)).trans
        (secondBridge.symm.reachable.trans (middlePath.symm.trans
          (bridge.symm.reachable.trans path01.symm)))
  exact ⟨fun x y => (finish x).trans (finish y).symm⟩

#print axioms forcing_exact
#print axioms residue_exact
#print axioms connected
end AutoGraphForge2535
