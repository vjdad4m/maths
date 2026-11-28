import SixOrder24ThirdDeficient189
import SixOrder25BThreeExcluded189
import SixUniversalOrder25Middle189

namespace Graffiti189LongestPath
open SimpleGraph Finset
open private order_sum_odd_shells_of_radius_six from SixThreeRadiusFive189
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem no_order24_second_shell_three_at_degree_six
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : Fintype.card V=24)
    (b3 : (Shell G x 2).card=3) : False := by
  classical
  let A := Shell G x 1
  let B := Shell G x 2
  let C := Shell G x 3
  let D := Shell G x 4
  have n24 : 24≤Fintype.card V := n.ge
  have rad := eccentricity_le_four_of_order_ge_twenty_four_at_degree_six hc cap conn high dx n24
  have e0 : Shell G x 5=∅ := eq_empty_iff_forall_not_mem.mpr (fun w wm=>by
    have k := mem_shell.mp wm
    have r := rad w
    omega)
  have cover : (univ : Finset V) ⊆ insert x (A∪B∪C∪D) := by
    intro w _
    have r := rad w
    have cases : G.dist x w=0 ∨ G.dist x w=1 ∨ G.dist x w=2 ∨ G.dist x w=3 ∨ G.dist x w=4 := by omega
    rcases cases with d|d|d|d|d
    · exact mem_insert.mpr (.inl ((hc.dist_eq_zero_iff.mp d).symm))
    · exact mem_insert.mpr (.inr (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_shell.mpr d)))))
    · exact mem_insert.mpr (.inr (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_shell.mpr d)))))
    · exact mem_insert.mpr (.inr (mem_union_left _ (mem_union_right _ (mem_shell.mpr d))))
    · exact mem_insert.mpr (.inr (mem_union_right _ (mem_shell.mpr d)))
  have a6 : A.card≤6 := by
    have eq : A=G.neighborFinset x := by
      ext z
      change z∈Shell G x 1 ↔ _
      rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
    rw [eq,G.card_neighborFinset_eq_degree]
    exact dx
  have d3 : D.card≤3 := by
    have w := shell_two_four_le_of_even (cap x)
    change B.card+D.card≤6 at w
    change B.card=3 at b3
    omega
  have c12 : C.card≤12 := third_shell_le_twelve_at_degree_six hc cap x dx
  have s := (card_le_card cover).trans (card_insert_le x (A∪B∪C∪D))
  rw [card_univ,n] at s
  have u := card_union_le (A∪B∪C) D
  have v := card_union_le (A∪B) C
  have w := card_union_le A B
  change B.card=3 at b3
  have cMin : 11≤C.card := by omega
  obtain ⟨Q⟩ := radius_five_near_equality hc cap x dx b3 (by rw [e0,card_empty,add_zero]; exact cMin)
  by_cases c11 : C.card=11
  · have ax : A.card=6 := by omega
    have dd : D.card=3 := by omega
    by_cases full : ∀ a∈Q.T,(JointFarGroup G x a).card=4
    · exact Q.no_order24_one_shared_third hc cap conn high dx n24 e0 ax c11 dd full
    push_neg at full
    obtain ⟨k,kT,kN⟩ := full
    have l := Q.far_card k kT
    exact Q.no_order24_one_deficient_third hc cap conn high dx n24 e0 ax c11 dd kT (by omega)
  have cEq : C.card=12 := by omega
  have s' : A.card=6 ∧ D.card=2 ∨ A.card=5 ∧ D.card=3 ∨ A.card=6 ∧ D.card=3 := by omega
  rcases s' with h|h|h
  · exact Q.no_order24_full_near_family hc cap conn high dx n24 e0 cEq (.inl h)
  · exact Q.no_order24_full_near_family hc cap conn high dx n24 e0 cEq (.inr h)
  -- When the bounded sum is 25 rather than 24, the shells would
  -- be pairwise disjoint and have order 25, contradicting the premise.
  have depthDis {i j : ℕ} (ij : i≠j) : Disjoint (Shell G x i) (Shell G x j) := by
    apply disjoint_left.mpr
    intro z zi zj
    exact ij ((mem_shell.mp zi).symm.trans (mem_shell.mp zj))
  have xnot : x∉A∪B∪C∪D := by
    intro e
    have bad : G.dist x x=1 ∨ G.dist x x=2 ∨ G.dist x x=3 ∨ G.dist x x=4 := by
      rcases mem_union.mp e with e|e
      · rcases mem_union.mp e with e|e
        · rcases mem_union.mp e with e|e
          · exact .inl (mem_shell.mp e)
          · exact .inr (.inl (mem_shell.mp e))
        · exact .inr (.inr (.inl (mem_shell.mp e)))
      · exact .inr (.inr (.inr (mem_shell.mp e)))
    rw [dist_self] at bad
    omega
  have ac : Disjoint A C := depthDis (by decide : (1:ℕ)≠3)
  have ad : Disjoint A D := depthDis (by decide : (1:ℕ)≠4)
  have ab : Disjoint A B := depthDis (by decide : (1:ℕ)≠2)
  have bc : Disjoint B C := depthDis (by decide : (2:ℕ)≠3)
  have bd : Disjoint B D := depthDis (by decide : (2:ℕ)≠4)
  have cd : Disjoint C D := depthDis (by decide : (3:ℕ)≠4)
  have hi := card_le_univ (insert x (A∪B∪C∪D))
  rw [card_insert_of_not_mem xnot,
    card_union_of_disjoint (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨ad,bd⟩,cd⟩),
    card_union_of_disjoint (disjoint_union_left.mpr ⟨ac,bc⟩),card_union_of_disjoint ab,n] at hi
  omega

theorem four_le_second_shell_of_order_ge_twenty_four_at_degree_six
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {x : V} (dx : G.degree x≤6) (n : 24≤Fintype.card V) :
    4≤(Shell G x 2).card := by
  by_cases n25 : Fintype.card V=25
  · exact four_le_second_shell_at_order25_degree_six hc cap conn high dx n25
  have hi := order_le_twenty_five_at_degree_six hc cap x dx
  have n24 : Fintype.card V=24 := by omega
  have rad := eccentricity_le_four_of_order_ge_twenty_four_at_degree_six hc cap conn high dx n
  have e0 : Shell G x 5=∅ := eq_empty_iff_forall_not_mem.mpr (fun w wm=>by
    have k := mem_shell.mp wm
    have r := rad w
    omega)
  have b := order_sum_odd_shells_of_radius_six cap x dx (fun y=>(rad y).trans (by decide))
  rw [n24,e0,card_empty] at b
  obtain ⟨y,ym⟩ := card_pos.mp (show 0<(Shell G x 3).card by omega)
  have yd := mem_shell.mp ym
  have h := shell_card_of_far hc 3 conn (x:=x) (y:=y) (i:=2) (by decide) (by omega)
  by_contra! bad
  exact no_order24_second_shell_three_at_degree_six hc cap conn high dx n24 (by omega)

#print axioms no_order24_second_shell_three_at_degree_six
#print axioms four_le_second_shell_of_order_ge_twenty_four_at_degree_six
end Graffiti189LongestPath
