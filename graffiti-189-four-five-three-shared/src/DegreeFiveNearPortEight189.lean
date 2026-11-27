import RootedOreExceptPair189
import DegreeFiveBothFiveResidual189
import WingSignature189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset ArticulationPair
open private Shore shore_connected from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- An order-five-to-eight shore with near-universal common porters
has a free mask at some cut, regardless of how many porters are shared. -/
theorem port_rooted_of_near_shore_at_most_eight
    (hc : G.Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (min : 5≤(Shore C).card) (max : (Shore C).card≤8)
    (port : 3≤(cutPorts C).card)
    (near : ∀ w∈sharedPortSet C,(secondShore C w).card≤1 ∧
      ∀ t∈Shore C,G.dist w t≤2) :
    ∃ r∈cutPorts C,∃ t,RouteOn G (Shore C) r t := by
  classical
  let S := Shore C
  let K := sharedPortSet C
  let P := cutPorts C
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let A : Finset U := univ.filter (fun u=>u.val∈P)
  let high (u : U) := 5≤G.degree u.val
  have n : Fintype.card U=S.card := Fintype.card_coe S
  have lower : 5≤S.card := min
  have upper : S.card≤8 := max
  have app (u : U) : u∈A ↔ u.val∈P := by simp [A]
  have aCard : A.card=P.card := by
    apply card_bij (fun u _=>u.val)
    · intro u h
      exact (app u).mp h
    · intro u _ v _ h
      exact Subtype.ext h
    intro v vp
    have vs : v∈S := (mem_filter.mp vp).1
    exact ⟨⟨v,vs⟩,(app ⟨v,vs⟩).mpr vp,rfl⟩
  have pair (u v : U) (uv : u≠v) : high u ∨ high v :=
    degree u.val v.val (fun e=>uv (Subtype.ext e))
  have indeg (u : U) : (inside G S u.val).card=J.degree u :=
    inside_card_eq_degree_induce (G:=G) S u
  have cm (u : U) (uk : u.val∈K) : S.card≤J.degree u+2 := by
    let N := inside G S u.val
    let Q := secondShore C u.val
    have sub : S⊆insert u.val (N∪Q) := by
      intro w ws
      by_cases e : w=u.val
      · exact mem_insert.mpr (.inl e)
      apply mem_insert_of_mem
      by_cases adj : G.Adj u.val w
      · exact mem_union_left _ (mem_filter.mpr ⟨ws,adj⟩)
      have lo := hc.one_lt_dist_of_ne_of_not_adj (show u.val≠w from fun h=>e h.symm) adj
      have hi := (near _ uk).2 w ws
      exact mem_union_right _ (mem_inter.mpr ⟨ws,
        by simp [DistanceTwo,show G.dist u.val w=2 by omega]⟩)
    have q := (card_le_card sub).trans (card_insert_le _ _)
    have r := card_union_le N Q
    have ne := (near _ uk).1
    change Q.card≤1 at ne
    have h : N.card=J.degree u := indeg u
    omega
  have p4 (u : U) (hh : high u) (notK : u.val∉K) : 4≤J.degree u := by
    have nk : ¬(G.Adj a u.val ∧ G.Adj b u.val) := fun h=>notK
      (mem_filter.mpr ⟨u.property,h⟩)
    exact (indeg u) ▸ inside_high_at_least_four_if_exclusive u.property hh nk
  have cap (u v : U) (uh : high u) (vh : high v) (_ : u≠v)
      (_ : ¬(u∈(∅ : Finset U) ∧ v∈(∅ : Finset U))) :
      Fintype.card U≤J.degree u+J.degree v := by
    have all (w : U) (wh : high w) : S.card≤J.degree w+2 ∨ 4≤J.degree w := by
      by_cases wk : w.val∈K
      · exact .inl (cm w wk)
      exact .inr (p4 w wh wk)
    rcases all u uh with u'|u' <;> rcases all v vh with v'|v' <;> omega
  obtain ⟨r,rA,t,p,pp,ps⟩ := rooted_Ore_except_pair (shore_connected C) A ∅
    (by rwa [aCard]) (by simp) (.inl (by simp)) high pair cap
  exact ⟨r.val,(app r).mp rA,t.val,lift_side_path S p pp ps⟩

#print axioms port_rooted_of_near_shore_at_most_eight
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
