import P5CliqueWedgeSlack133
import P5CliqueMultiPortBudget133
import P5CliqueSmallCoreLocal133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

/-- Boundary-independent inequality for a partition with four independent
ports. Each crossing is counted at most twice. -/
theorem local_sum_le_nonports_add_twice_crossings (P : Finset V)
    (ind : ∀ a∈P,∀ b∈P,¬G.Adj a b) :
    let U := (Finset.univ : Finset V)\P
    (∑ v : V,localIndependence G v)≤
      (∑ u : (U : Set V),localIndependence (G.induce (U : Set V)) u)+
      2*(∑ x∈P,(U.filter (G.Adj x)).card) := by
  classical
  let U := (Finset.univ : Finset V)\P
  have eq : (Finset.univ : Finset V)\U=P := by ext x; simp [U]
  have lb := core_and_exterior_independence_sum (G:=G) U
  dsimp only at lb
  rw [eq] at lb
  letI : DecidableRel G.Adj := Classical.decRel _
  have c (v : V) (vm : v∈P) : localIndependence G v≤(U.filter (G.Adj v)).card := by
    have e : U.filter (G.Adj v)=G.neighborFinset v := by
      ext a
      rw [Finset.mem_filter,G.mem_neighborFinset]
      exact ⟨fun h=>h.2,fun h=>⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun ha=>ind v vm a ha h⟩,h⟩⟩
    rw [e,G.card_neighborFinset_eq_degree]
    exact small_local_le_degree (G:=G) v
  have cb := Finset.sum_le_sum c
  change _≤(∑ u : (U : Set V),localIndependence (G.induce (U : Set V)) u)+2*(∑ x∈P,(U.filter (G.Adj x)).card)
  omega

/-- Small independent-palette cores of order four or five have at least
twelve units of slack. -/
theorem independent_four_ports_small_core_twelve_slack (P : Finset V) (p4 : P.card=4)
    (ind : ∀ a∈P,∀ b∈P,¬G.Adj a b) (n5 : Fintype.card V≤5) :
    (∑ v : V,localIndependence G v)+12≤4*Fintype.card V := by
  classical
  let U := (Finset.univ : Finset V)\P
  have sizes := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
  rw [Finset.card_univ,p4] at sizes
  change U.card+4=Fintype.card V at sizes
  have u1 : U.card≤1 := by omega
  let H := G.induce (U : Set V)
  have none (a b : (U : Set V)) : ¬H.Adj a b := by
    intro ab
    apply ab.ne
    exact Subtype.ext (Finset.card_le_one.mp u1 a.val a.property b.val b.property)
  letI : DecidableRel H.Adj := Classical.decRel _
  have loc (x : (U : Set V)) : localIndependence H x=0 := by
    have emp : H.neighborFinset x=∅ := by
      ext y
      rw [H.mem_neighborFinset]
      simp only [Finset.not_mem_empty,iff_false]
      exact none x y
    have le := small_local_le_degree (G:=H) x
    rw [←H.card_neighborFinset_eq_degree,emp,Finset.card_empty] at le
    exact Nat.eq_zero_of_le_zero le
  have au : (∑ v : (U : Set V),localIndependence H v)=0 := by simp [loc]
  have z : (∑ x∈P,(U.filter (G.Adj x)).card)≤4*U.card := by
    calc
      _≤∑ _x∈P,U.card := Finset.sum_le_sum (fun _ _=>Finset.card_filter_le _ _)
      _=4*U.card := by simp [p4,Nat.mul_comm]
  have zz := local_sum_le_nonports_add_twice_crossings (G:=G) P ind
  change (∑ v : V,localIndependence G v)≤
    (∑ u : (U : Set V),localIndependence H u)+2*(∑ x∈P,(U.filter (G.Adj x)).card) at zz
  omega

/-- At order ten or eleven, very sparse port-to-nonport incidence recovers
twelve units of signed slack independently of core connectivity or P7. -/
theorem independent_four_ports_mid_core_twelve_slack (P : Finset V) (p4 : P.card=4)
    (ind : ∀ a∈P,∀ b∈P,¬G.Adj a b) (h4 : FourCycleFree G)
    (n10 : 10≤Fintype.card V) (n11 : Fintype.card V≤11)
    (sparse : let U := (Finset.univ : Finset V)\P
      (∑ x∈P,(U.filter (G.Adj x)).card)≤U.card+1) :
    (∑ v : V,localIndependence G v)+12≤4*Fintype.card V := by
  classical
  let U := (Finset.univ : Finset V)\P
  let H := G.induce (U : Set V)
  letI : DecidableRel H.Adj := Classical.decRel _
  have sz := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
  rw [p4,Finset.card_univ] at sz
  change U.card+4=Fintype.card V at sz
  have sz' : Fintype.card (U : Set V)=U.card := Fintype.card_coe _
  have hu : FourCycleFree H := by
    intro a b x y ne ax bx ay by'
    exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
  have z := small_core_twelve_signed_slack H (by omega) (by omega) hu
  have q := local_sum_le_nonports_add_twice_crossings (G:=G) P ind
  change (∑ v : V,localIndependence G v)≤
    (∑ u : (U : Set V),localIndependence H u)+2*(∑ x∈P,(U.filter (G.Adj x)).card) at q
  change (∑ x∈P,(U.filter (G.Adj x)).card)≤U.card+1 at sparse
  omega

#print axioms local_sum_le_nonports_add_twice_crossings
#print axioms independent_four_ports_small_core_twelve_slack
#print axioms independent_four_ports_mid_core_twelve_slack
end Graffiti133P5CliqueArms
