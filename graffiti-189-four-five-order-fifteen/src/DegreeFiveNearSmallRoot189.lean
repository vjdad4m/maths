import RootedOreExceptPair189
import DegreeFiveBothFiveResidual189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset ArticulationPair
open private Shore shore_closed shore_connected from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff common_sub_ports from DegreeFiveBothFiveResidual189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Near-universal shared porters give a common-rooted route at order
at most nine. In the possible order-nine high closure, the only
excepted pair consists of the at most two exclusive porters. -/
theorem common_rooted_of_small_near_universal_shore
    (hc : G.Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (min : 5≤(Shore C).card) (max : (Shore C).card≤9)
    (portCap : (cutPorts C).card≤5) (shared : 3≤(sharedPortSet C).card)
    (near : ∀ w∈sharedPortSet C,(secondShore C w).card≤1 ∧
      ∀ t∈Shore C,G.dist w t≤2) :
    ∃ r∈sharedPortSet C,∃ t,RouteOn G (Shore C) r t := by
  classical
  let S := Shore C
  let K := sharedPortSet C
  let P := cutPorts C
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let A : Finset U := univ.filter (fun u=>u.val∈K)
  let E : Finset U := univ.filter (fun u=>S.card=9 ∧ u.val∈P ∧ u.val∉K)
  let high (u : U) := 5≤G.degree u.val
  have n : Fintype.card U=S.card := Fintype.card_coe S
  have lower : 5≤S.card := min
  have upper : S.card≤9 := max
  have app (u : U) : u∈A ↔ u.val∈K := by simp [A]
  have exc (u : U) : u∈E ↔ S.card=9 ∧ u.val∈P ∧ u.val∉K := by simp [E]
  have aCard : A.card=K.card := by
    apply card_bij (fun u _=>u.val)
    · intro u h
      exact (app u).mp h
    · intro u _ v _ h
      exact Subtype.ext h
    intro v vk
    have vs : v∈S := (mem_filter.mp vk).1
    exact ⟨⟨v,vs⟩,(app ⟨v,vs⟩).mpr vk,rfl⟩
  have eCard : E.card≤2 := by
    have q : (P\K).card+K.card=P.card := card_sdiff_add_card_eq_card (common_sub_ports C)
    let emb : U ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    have sub : E.map emb⊆P\K := by
      intro v vm
      obtain ⟨u,um,rfl⟩ := mem_map.mp vm
      have h := (exc u).mp um
      exact mem_sdiff.mpr ⟨h.2.1,h.2.2⟩
    have b := card_le_card sub
    rw [card_map] at b
    change P.card≤5 at portCap
    change 3≤K.card at shared
    omega
  have enough : E.card≤1 ∨ 6≤Fintype.card U := by
    by_cases h : S.card=9
    · exact .inr (by omega)
    have eq : E=∅ := by ext w; simp [E,h]
    exact .inl (by simp [eq])
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
  have p5 (u : U) (hh : high u) (notP : u.val∉P) : 5≤J.degree u := by
    have na : ¬G.Adj a u.val := fun h=>notP (cut_mem_iff.mpr ⟨u.property,.inl h⟩)
    have nb : ¬G.Adj b u.val := fun h=>notP (cut_mem_iff.mpr ⟨u.property,.inr h⟩)
    have sub : G.neighborFinset u.val⊆inside G S u.val := by
      intro w wm
      have uw := (mem_neighborFinset G _ _).mp wm
      rcases shore_closed C u.val u.property w uw with rfl|rfl|ws
      · exact (na uw.symm).elim
      · exact (nb uw.symm).elim
      exact mem_filter.mpr ⟨ws,uw⟩
    have q := card_le_card sub
    rw [card_neighborFinset_eq_degree] at q
    exact hh.trans (q.trans (le_of_eq (indeg u)))
  have cap (u v : U) (uh : high u) (vh : high v) (uv : u≠v) (avoid : ¬(u∈E ∧ v∈E)) :
      Fintype.card U≤J.degree u+J.degree v := by
    have all (w : U) (wh : high w) : S.card≤J.degree w+2 ∨ 4≤J.degree w := by
      by_cases wk : w.val∈K
      · exact .inl (cm w wk)
      exact .inr (p4 w wh wk)
    have u' := all u uh
    have v' := all v vh
    by_cases big : S.card=9
    · have q (w : U) (wh : high w) (we : w∉E) : 5≤J.degree w := by
        by_cases wk : w.val∈K
        · have c := cm w wk
          omega
        have wp : w.val∉P := fun h=>we ((exc w).mpr ⟨big,h,wk⟩)
        exact p5 w wh wp
      by_cases ue : u∈E
      · have h := q v vh (fun e=>avoid ⟨ue,e⟩)
        rcases u' with u'|u' <;> omega
      have h := q u uh ue
      rcases v' with v'|v' <;> omega
    rcases u' with u'|u' <;> rcases v' with v'|v' <;> omega
  obtain ⟨r,rA,t,p,pp,ps⟩ := rooted_Ore_except_pair (shore_connected C) A E
    (by rwa [aCard]) eCard enough high pair cap
  exact ⟨r.val,(app r).mp rA,t.val,lift_side_path S p pp ps⟩

#print axioms common_rooted_of_small_near_universal_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
