import ShellModel189
import EJSlackClosure189
import ArticulationGeneralClosure189
import CertPrefix2250189
import CertPrefix2350189
import CertPrefix3250189
import CertPrefix3350189
import CertRoute2340189
import CertRoute2241189
import CertRoute3330189
import CertRoute3240189
import CertRoute3231189
import CertRoute3340189
import CertRoute3241189

open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.LowDegreeOrders Graffiti189LongestPath.SmallOrder
open private Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189

set_option maxHeartbeats 10000000
namespace Graffiti189LongestPath.GraphSat
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

-- Local copy of the prior separator degree-floor argument.
private theorem degree_floor_when_enough_vertices (k : Nat)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (enough : k+1≤Fintype.card V) (t : V) : k≤G.degree t := by
  classical
  by_cases h : ∃ z,z≠t ∧ ¬G.Adj t z
  · obtain ⟨z,zt,n⟩ := h
    rw [←G.card_neighborFinset_eq_degree]
    exact Graffiti189LongestPath.boundary_card_of_connectivity k conn
      (mem_singleton_self t) (fun e => zt (mem_singleton.mp e))
      (fun e => n ((G.mem_neighborFinset _ _).mp e))
      (disjoint_left.mpr (fun _ a b => ((G.mem_neighborFinset _ _).mp b).ne
        (mem_singleton.mp a).symm))
      (fun a ha v _ ed => (G.mem_neighborFinset _ _).mpr ((mem_singleton.mp ha) ▸ ed))
  · have hV : (univ : Finset V)⊆insert t (G.neighborFinset t) := by
      intro z _
      by_cases zt : z=t
      · exact mem_insert.mpr (Or.inl zt)
      exact mem_insert.mpr (Or.inr ((G.mem_neighborFinset _ _).mpr
        (Classical.byContradiction (fun no => h ⟨z,zt,no⟩))))
    have e := (card_le_card hV).trans (card_insert_le _ _)
    rw [card_univ,G.card_neighborFinset_eq_degree] at e
    omega

/-- At actual second degree three, all connected finite graphs satisfying
the original even-distance budget have a spanning simple path. -/
theorem traceable_at_actual_degree_three (hc : G.Connected)
    (cap : ∀ u,(EvenFrom G u).card≤4)
    (degree : ∀ u v : V,u≠v → 3≤G.degree u ∨ 3≤G.degree v)
    (attain : ∃ u : V,G.degree u≤3) : Graffiti189Ore.Traceable G := by
  classical
  by_cases conn : DeletionTwoConnected G
  · by_cases small : Fintype.card V≤9
    · exact traceable_at_order_le_two_d_add_three hc conn 3 cap degree small
    apply Classical.byContradiction
    intro noPath
    have floor := degree_floor_when_enough_vertices 2 conn (by omega : 3≤Fintype.card V)
    have root : ∃ r,(G.degree r=2 ∨ G.degree r=3) ∧ ∀ z≠r,3≤G.degree z := by
      by_cases low : ∃ r : V,G.degree r<3
      · obtain ⟨r,lr⟩ := low
        have f := floor r
        exact ⟨r,Or.inl (by omega),fun z zr => (degree z r zr).resolve_right (by omega)⟩
      · obtain ⟨r,dr⟩ := attain
        have q (z : V) : 3≤G.degree z := Nat.le_of_not_gt (fun e => low ⟨z,e⟩)
        exact ⟨r,Or.inr (by have := q r; omega),fun z _ => q z⟩
    obtain ⟨r,roots,high⟩ := root
    let A := Shell G r 1
    let B := Shell G r 2
    let C := Shell G r 3
    let D := Shell G r 4
    have asize : A.card=G.degree r := by
      rw [←G.card_neighborFinset_eq_degree]
      congr 1
      ext x
      rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
    have AS : A.card=2 ∨ A.card=3 := by rwa [asize]
    have diam := diameter_at_most_four_of_even_four hc cap conn
    have capture (z : V) : z=r ∨ z∈A ∨ z∈B ∨ z∈C ∨ z∈D := by
      have top := diam r z
      have cc : G.dist r z=0 ∨ G.dist r z=1 ∨ G.dist r z=2 ∨
          G.dist r z=3 ∨ G.dist r z=4 := by omega
      rcases cc with e|e|e|e|e
      · exact Or.inl (hc.dist_eq_zero_iff.mp e).symm
      · exact Or.inr (Or.inl (mem_shell.mpr e))
      · exact Or.inr (Or.inr (Or.inl (mem_shell.mpr e)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_shell.mpr e))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_shell.mpr e))))
    have order : Fintype.card V≤1+A.card+B.card+C.card+D.card := by
      let S := A∪B∪C∪D
      have sub : (univ:Finset V)⊆insert r S := by
        intro v _
        simpa only [S,mem_insert,mem_union,or_assoc] using capture v
      have t := card_le_card sub
      rw [card_univ] at t
      have x := card_insert_le r S
      have y := card_union_le (A∪B∪C) D
      change S.card≤_ at y
      have z := card_union_le (A∪B) C
      have w := card_union_le A B
      omega
    have BD : B.card+D.card≤3 := shell_two_four_le_of_even (cap r)
    have b2 : 2≤B.card := by
      have non : 0<C.card := by omega
      obtain ⟨z,zc⟩ := card_pos.mp non
      have d3 := mem_shell.mp zc
      exact shell_card_of_far hc 2 conn (x:=r) (y:=z) (i:=2) (by decide) (by omega)
    have BS : B.card=2 ∨ B.card=3 := by omega
    have dist2Bound (z : V) := distanceTwo_le_of_even 3 z (cap z)
    have CL : C.card≤4 := by
      apply Nat.le_of_not_gt
      intro outside
      obtain ⟨C',sub,c5⟩ := Finset.exists_subset_card_eq (show 5≤C.card by omega)
      rcases AS with as2|as3 <;> rcases BS with bs2|bs3
      · obtain ⟨f,M⟩ := exists_shell_model hc r C' ∅ sub (empty_subset _)
          2 2 5 0 as2 bs2 c5 (by simp) false (fun _ => rfl)
          (fun h => Bool.false_ne_true h |>.elim) high dist2Bound noPath
        exact Prefix2250.impossible M
      · obtain ⟨f,M⟩ := exists_shell_model hc r C' ∅ sub (empty_subset _)
          2 3 5 0 as2 bs3 c5 (by simp) false (fun _ => rfl)
          (fun h => Bool.false_ne_true h |>.elim) high dist2Bound noPath
        exact Prefix2350.impossible M
      · obtain ⟨f,M⟩ := exists_shell_model hc r C' ∅ sub (empty_subset _)
          3 2 5 0 as3 bs2 c5 (by simp) false (fun _ => rfl)
          (fun h => Bool.false_ne_true h |>.elim) high dist2Bound noPath
        exact Prefix3250.impossible M
      · obtain ⟨f,M⟩ := exists_shell_model hc r C' ∅ sub (empty_subset _)
          3 3 5 0 as3 bs3 c5 (by simp) false (fun _ => rfl)
          (fun h => Bool.false_ne_true h |>.elim) high dist2Bound noPath
        exact Prefix3350.impossible M
    have shapes :
        (A.card=2 ∧ B.card=3 ∧ C.card=4 ∧ D.card=0) ∨
        (A.card=2 ∧ B.card=2 ∧ C.card=4 ∧ D.card=1) ∨
        (A.card=3 ∧ B.card=3 ∧ C.card=3 ∧ D.card=0) ∨
        (A.card=3 ∧ B.card=2 ∧ C.card=4 ∧ D.card=0) ∨
        (A.card=3 ∧ B.card=2 ∧ C.card=3 ∧ D.card=1) ∨
        (A.card=3 ∧ B.card=3 ∧ C.card=4 ∧ D.card=0) ∨
        (A.card=3 ∧ B.card=2 ∧ C.card=4 ∧ D.card=1) := by omega
    rcases shapes with ⟨a0,b0,c0,d0⟩|⟨a1,b1,c1,d1⟩|⟨a2,b2,c2,d2⟩|⟨a3,b3,c3,d3⟩|⟨a4,b4,c4,d4⟩|⟨a5,b5,c5,d5⟩|⟨a6,b6,c6,d6⟩
    · obtain ⟨f,M⟩ := exists_shell_model hc r C D Subset.rfl Subset.rfl
        2 3 4 0 a0 b0 c0 d0 true
        (fun h => (Bool.false_ne_true h.symm).elim) (fun _ => capture) high dist2Bound noPath
      exact Route2340.impossible M
    · obtain ⟨f,M⟩ := exists_shell_model hc r C D Subset.rfl Subset.rfl
        2 2 4 1 a1 b1 c1 d1 true
        (fun h => (Bool.false_ne_true h.symm).elim) (fun _ => capture) high dist2Bound noPath
      exact Route2241.impossible M
    · obtain ⟨f,M⟩ := exists_shell_model hc r C D Subset.rfl Subset.rfl
        3 3 3 0 a2 b2 c2 d2 true
        (fun h => (Bool.false_ne_true h.symm).elim) (fun _ => capture) high dist2Bound noPath
      exact Route3330.impossible M
    · obtain ⟨f,M⟩ := exists_shell_model hc r C D Subset.rfl Subset.rfl
        3 2 4 0 a3 b3 c3 d3 true
        (fun h => (Bool.false_ne_true h.symm).elim) (fun _ => capture) high dist2Bound noPath
      exact Route3240.impossible M
    · obtain ⟨f,M⟩ := exists_shell_model hc r C D Subset.rfl Subset.rfl
        3 2 3 1 a4 b4 c4 d4 true
        (fun h => (Bool.false_ne_true h.symm).elim) (fun _ => capture) high dist2Bound noPath
      exact Route3231.impossible M
    · obtain ⟨f,M⟩ := exists_shell_model hc r C D Subset.rfl Subset.rfl
        3 3 4 0 a5 b5 c5 d5 true
        (fun h => (Bool.false_ne_true h.symm).elim) (fun _ => capture) high dist2Bound noPath
      exact Route3340.impossible M
    · obtain ⟨f,M⟩ := exists_shell_model hc r C D Subset.rfl Subset.rfl
        3 2 4 1 a6 b6 c6 d6 true
        (fun h => (Bool.false_ne_true h.symm).elim) (fun _ => capture) high dist2Bound noPath
      exact Route3241.impossible M
  · obtain ⟨S,S2,bad⟩ : ∃ S : Finset V,S.card<2 ∧ ¬(G.induce ((↑S:Set V)ᶜ)).Connected := by
      apply Classical.byContradiction
      intro no
      apply conn
      intro S small
      exact Classical.byContradiction (fun z => no ⟨S,small,z⟩)
    have one : S.card=1 := by
      by_cases zero : S.card=0
      · have empty : S=∅ := card_eq_zero.mp zero
        exfalso
        apply bad
        rw [empty,coe_empty,Set.compl_empty]
        exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hc
      · omega
    obtain ⟨u,eq⟩ := card_eq_one.mp one
    have setEq : (↑S:Set V)ᶜ={z : V | z≠u} := by rw [eq]; ext z; simp
    exact Graffiti189LongestPath.CrossSaturation.traceable_at_articulation_general
      hc 3 (by decide) cap degree u (by rw [←setEq]; exact bad)

#print axioms traceable_at_actual_degree_three
end Graffiti189LongestPath.GraphSat
