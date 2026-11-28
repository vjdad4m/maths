import SixTwelveCoarse189
import SixTwelveTable189
import SixDistanceThreeTwentyReduction189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut)
open Graffiti189LongestPath.SixTwelveSat (profileAt profileShape lowCode fiberCard
  profile_matches profile_not_hidden each_profile_impossible role_preserving_equiv_with_exception)
set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {C D : Cmp G a b}

theorem card_shore_fiber (S : Finset V) (k : Fin 8) :
    Fintype.card {z : ↑(↑S : Set V) // sixClass G a b z.val=k} =
      (sixBucket G a b S k).card := by
  classical
  let E : {z : ↑(↑S : Set V) // sixClass G a b z.val=k} ≃ ↑(sixBucket G a b S k) := {
    toFun := fun z=>⟨z.val.val,mem_filter.mpr ⟨z.val.property,z.property⟩⟩
    invFun := fun z=>⟨⟨z.val,(mem_filter.mp z.property).1⟩,(mem_filter.mp z.property).2⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl }
  rw [Fintype.card_congr E,Fintype.card_coe]

theorem no_six_twelve_shores_sorted
    (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ v,(EvenFrom G v).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (six : (Shore C).card=6) (twelve : (Shore D).card=12)
    (norm : (cutPorts G (Shore C) a).card≤(cutPorts G (Shore C) b).card) : False := by
  classical
  obtain ⟨i,l,hshape,hidden,lowShape⟩ := classified_six_twelve_shape hc far ab even conn degree cd cover six twelve norm
  let P := profileAt i
  have same := (profile_matches i).trans hshape
  have pEq : P.p=(cutPorts G (Shore C) a).card :=
    congrArg (fun s : List ℕ=>s[0]!) same
  have qEq : P.q=(cutPorts G (Shore C) b).card :=
    congrArg (fun s : List ℕ=>s[1]!) same
  have lEq : lowCode P=l :=
    congrArg (fun s : List ℕ=>s[9]!) same
  have cards (k : Fin 8) :
      fiberCard P k=(sixBucket G a b (Shore D) k).card := by
    fin_cases k
    · exact congrArg (fun s : List ℕ=>s[2]!) same
    · exact congrArg (fun s : List ℕ=>s[3]!) same
    · exact congrArg (fun s : List ℕ=>s[4]!) same
    · exact congrArg (fun s : List ℕ=>s[5]!) same
    · exact congrArg (fun s : List ℕ=>s[6]!) same
    · exact congrArg (fun s : List ℕ=>s[7]!) same
    · exact congrArg (fun s : List ℕ=>s[8]!) same
    · change fiberCard P 7=(sixBucket G a b (Shore D) 7).card
      rw [hidden]
      unfold fiberCard
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_not_mem.mpr
      intro z mz
      have eq := (mem_filter.mp mz).2
      have h := profile_not_hidden i z
      change (P.role z).val<7 at h
      rw [eq] at h
      exact (by decide : ¬((7:Fin 8).val<7)) h
  let g (z : ↑(↑(Shore D) : Set V)) := sixClass G a b z.val
  let high (z : ↑(↑(Shore D) : Set V)) := 6≤G.degree z.val
  have cardst (k : Fin 8) : Fintype.card {x : Fin 12 // P.role x=k} =
      Fintype.card {z : ↑(↑(Shore D):Set V) // g z=k} := by
    rw [Fintype.card_subtype]
    change fiberCard P k=Fintype.card {z : ↑(↑(Shore D):Set V) // sixClass G a b z.val=k}
    rw [card_shore_fiber]
    exact cards k
  have unique : ∀ y z,¬high y → ¬high z → y=z := by
    intro y z hy hz
    apply Classical.byContradiction
    intro h
    have ne : y.val≠z.val := fun eq=>h (Subtype.ext eq)
    exact (degree y.val z.val ne).elim hy hz
  have sel : ∀ y,¬high y → ∃ j,P.low=some j ∧ P.role j=g y := by
    intro y h
    have cc := lowShape y.val y.property (Nat.lt_of_not_ge h)
    have eq : lowCode P=(g y).val+1 := lEq.trans cc
    cases k : P.low with
    | none =>
      unfold lowCode at eq
      rw [k] at eq
      change 0=(g y).val+1 at eq
      omega
    | some j =>
      refine ⟨j,rfl,?_⟩
      apply Fin.ext
      unfold lowCode at eq
      rw [k] at eq
      exact Nat.add_right_cancel eq
  obtain ⟨lab,roles,hl⟩ := role_preserving_equiv_with_exception P.role g high P.low cardst unique sel
  have model := model_of_label hc far ab conn even degree cd six P lab pEq qEq roles (profile_not_hidden i) hl
  exact each_profile_impossible i model

theorem no_six_twelve_shores
    (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ v,(EvenFrom G v).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (six : (Shore C).card=6) (twelve : (Shore D).card=12) : False := by
  by_cases norm : (cutPorts G (Shore C) a).card≤(cutPorts G (Shore C) b).card
  · exact no_six_twelve_shores_sorted hc far ab even conn degree cd cover six twelve norm
  have far' : 3≤G.dist b a := by rwa [dist_comm]
  have cd' : swapCut C≠swapCut D := fun e=>cd (swapCut.injective e)
  have cover' : ∀ {z : V},z≠b → z≠a → z∈Shore (swapCut C) ∨ z∈Shore (swapCut D) :=
    fun zb za=>by simpa only [shore_swapCut] using cover za zb
  exact no_six_twelve_shores_sorted hc far' ab.symm even conn degree cd' cover'
    (by rwa [shore_swapCut]) (by rwa [shore_swapCut])
    (by rw [shore_swapCut]; exact Nat.le_of_lt (Nat.lt_of_not_ge norm))

theorem traceable_at_six_distance_three_order_twenty
    (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ v,(EvenFrom G v).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) (n : Fintype.card V≤20) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  rcases traceable_or_six_twelve_at_six_distance_three_order_twenty hc far ab even conn degree cut n with h|h
  · exact h
  obtain ⟨C,D,cd,six,twelve,cover,_⟩ := h
  exact (no_six_twelve_shores hc far ab even conn degree cd cover six twelve).elim

#print axioms no_six_twelve_shores
#print axioms traceable_at_six_distance_three_order_twenty
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
