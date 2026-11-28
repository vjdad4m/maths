import AdjacentCutFiveMixedCapFifteen189
import AdjacentCutFiveFifteenSingletonComplete189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_disjoint shore_off shore_nonempty from AdjacentCutFiveActual189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev RouteCmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

/-- All degree-five graphs of order fifteen with an exact two-shore adjacent cut
are traceable, including when one shore is a singleton. -/
theorem traceable_of_actual_adjacent_two_shores_order_fifteen
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (two : Nat.card (RouteCmp G a b)=2)
    (n : Fintype.card V=15) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores two
  have oneCase {C D : RouteCmp G a b} (cd : C≠D)
      (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
      (one : (Shore C).card=1) :
      ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
    have sum := shore_sum_with_cover ab.ne cd cover
    have big : (Shore D).card=12 := by omega
    exact traceable_of_adjacent_singleton_twelve_shores hc ab even conn degree cd cover one big
  by_cases C1 : (Shore C).card=1
  · exact oneCase cd cover C1
  by_cases D1 : (Shore D).card=1
  · exact oneCase cd.symm (fun za zb=>(cover za zb).symm) D1
  have ns (K : RouteCmp G a b) : 2≤(Shore K).card := by
    obtain ⟨z,zK⟩ := shore_nonempty K
    have za : z≠a := fun h=>(shore_off K).1 (h ▸ zK)
    have zb : z≠b := fun h=>(shore_off K).2 (h ▸ zK)
    rcases cover za zb with zC|zD
    · have e : K=C := by
        by_contra no
        exact disjoint_left.mp (shore_disjoint no) zK zC
      subst K
      have p := card_pos.mpr (show (Shore C).Nonempty from ⟨z,zK⟩)
      omega
    · have e : K=D := by
        by_contra no
        exact disjoint_left.mp (shore_disjoint no) zK zD
      subst K
      have p := card_pos.mpr (show (Shore D).Nonempty from ⟨z,zK⟩)
      omega
  exact traceable_of_actual_adjacent_nonsingleton_two_shores_fourteen_sixteen hc ab even conn degree two ns
    (by omega) (by omega)

#print axioms traceable_of_actual_adjacent_two_shores_order_fifteen
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open CrossSaturation.FiveAdjacent
open private CutGraph from AdjacentCutFiveActual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Any connected counterexample at the degree-five threshold has order ≤14. -/
theorem order_le_fourteen_of_degree_five_counterexample
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (fail : ¬∃ a b,∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support) :
    Fintype.card V≤14 := by
  classical
  by_contra large
  have small := order_le_fifteen_of_degree_five_counterexample hc even degree fail
  have n : Fintype.card V=15 := by omega
  obtain ⟨conn,a,b,ab,cut⟩ := degree_five_counterexample_has_adjacent_cut hc even degree fail
  let J := CutGraph (G:=G) a b
  have notSub : ¬ ((univ : Finset V) ⊆ ({a,b} : Finset V)) := by
    intro sub
    have c := card_le_card sub
    rw [card_univ,card_insert_of_not_mem (by simpa using ab.ne),card_singleton] at c
    omega
  obtain ⟨z,_,zab⟩ := not_subset.mp notSub
  have nz : z≠a ∧ z≠b := by simpa [not_or] using zab
  letI : Nonempty {z : V | z≠a ∧ z≠b} := ⟨⟨z,nz⟩⟩
  have h : 2≤Nat.card J.ConnectedComponent := by
    by_contra few
    have ss : Subsingleton J.ConnectedComponent := by
      by_contra no
      have nt := not_subsingleton_iff_nontrivial.mp no
      apply few
      haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
      letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card_iff_nontrivial.mpr nt
    apply cut
    constructor
    intro u v
    exact ConnectedComponent.exact (ss.allEq (J.connectedComponentMk u) (J.connectedComponentMk v))
  have two := component_card_eq_two_at_genuine_adjacent_cut hc ab even conn degree h
  exact fail (traceable_of_actual_adjacent_two_shores_order_fifteen hc ab even conn degree two n)

theorem traceable_at_degree_five_of_order_ge_fifteen
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (big : 15≤Fintype.card V) :
    ∃ a b,∃ p : G.Walk a b,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_contra no
  have small := order_le_fourteen_of_degree_five_counterexample hc even degree no
  omega

#print axioms order_le_fourteen_of_degree_five_counterexample
#print axioms traceable_at_degree_five_of_order_ge_fifteen
end Graffiti189LongestPath
