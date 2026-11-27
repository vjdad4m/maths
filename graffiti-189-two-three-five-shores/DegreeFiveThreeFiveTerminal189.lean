import DegreeFiveThreeFiveShapes189
import UniversalRouteSingletons189
import WingSignature189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private inside_high_at_least_four_if_exclusive inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open ArticulationPair
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem terminal_route_on_three_port_small_shore
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C3 : (cutPorts C).card=3) (D5 : (cutPorts D).card=5)
    (small : (Shore C).card=4 ∨ (Shore C).card=6)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let S := Shore C
  let E := S \ cutPorts C
  have eCount : E.card+3=S.card := by
    have h : E.card+(cutPorts C).card=S.card := card_sdiff_add_card_eq_card (filter_subset _ _)
    rwa [C3] at h
  have xP : x∈cutPorts C := mem_filter.mpr ⟨xc,.inl ax⟩
  have other : ∃ t∈cutPorts C,t≠x := by
    apply Classical.byContradiction
    intro no
    have sub : cutPorts C⊆{x} := fun t tp=>mem_singleton.mpr
      (Classical.byContradiction (fun h=>no ⟨t,tp,h⟩))
    have h := card_le_card sub
    rw [C3,card_singleton] at h
    omega
  obtain ⟨t,tp,tx⟩ := other
  obtain ⟨ts,tHit⟩ := mem_filter.mp tp
  have xUniv := common_universal_in_shore_at_five hc even cd xc ax bx D5
  have result : RouteOn G S x t := by
    rcases small with s4|s6
    · have cap : S.card=4 := s4
      have univ (v : V) (vs : v∈S) (vh : 5≤G.degree v) :
          ∀ w∈S,v≠w → G.Adj v w := by
        have sub : inside G S v⊆S.erase v := by
          intro q h
          obtain ⟨qs,e⟩ := mem_filter.mp h
          exact mem_erase.mpr ⟨e.ne.symm,qs⟩
        have lower : 3≤(inside G S v).card := inside_high_at_least_three vs vh
        have eq : inside G S v=S.erase v := eq_of_subset_of_card_le sub (by
          rw [card_erase_of_mem vs]
          omega)
        intro w ws vw
        have t : w∈inside G S v := by rw [eq]; exact mem_erase.mpr ⟨vw.symm,ws⟩
        exact (mem_filter.mp t).2
      have cl : CompleteOn G S := by
        intro v vs w ws vw
        rcases degree v w vw with v5|w5
        · exact univ v vs v5 w ws vw
        exact (univ w ws w5 v vs vw.symm).symm
      obtain ⟨q,qp,qs⟩ := path_between_in_clique S cl xc ts tx.symm
      exact ⟨q,qp,qs⟩
    have sz : S.card=6 := s6
    obtain ⟨u,ue,uh⟩ := anywhere_high_of_two degree (show 2≤E.card by omega)
    have eraseTwo : 2≤(E.erase u).card := by rw [card_erase_of_mem ue]; omega
    obtain ⟨v,ve',vh⟩ := anywhere_high_of_two degree eraseTwo
    obtain ⟨vu,ve⟩ := mem_erase.mp ve'
    obtain ⟨us,un⟩ := mem_sdiff.mp ue
    obtain ⟨vs,vn⟩ := mem_sdiff.mp ve
    have ux : u≠x := fun h=>un (h.symm ▸ xP)
    have vx : v≠x := fun h=>vn (h.symm ▸ xP)
    have tu : t≠u := fun e=>un (e ▸ tp)
    have tv : t≠v := fun e=>vn (e ▸ tp)
    have outsideUniv (q : V) (qs : q∈S) (qn : q∉cutPorts C) (qh : 5≤G.degree q) :
        ∀ w∈S,q≠w → G.Adj q w := by
      have sub := nonport_neighbors_subset qs qn
      have eql : G.neighborFinset q=S.erase q := eq_of_subset_of_card_le sub (by
        rw [card_erase_of_mem qs,card_neighborFinset_eq_degree]
        omega)
      intro w ws qw
      apply (mem_neighborFinset G q w).mp
      rw [eql]
      exact mem_erase.mpr ⟨qw.symm,ws⟩
    let K : Finset V := {x,u,v}
    let A := S.erase t
    let R := A \ K
    have k3 : K.card=3 := by
      change (insert x ({u,v} : Finset V)).card=3
      rw [card_insert_of_not_mem (by simp [ux.symm,vx.symm])]
      simp [vu.symm]
    have kA : K⊆A := by
      intro w hw
      simp only [K,mem_insert,mem_singleton] at hw
      rcases hw with h|h|h
      · exact h.symm ▸ mem_erase.mpr ⟨tx.symm,xc⟩
      · exact h.symm ▸ mem_erase.mpr ⟨tu.symm,us⟩
      exact h.symm ▸ mem_erase.mpr ⟨tv.symm,vs⟩
    have all : K∪R=A := union_sdiff_of_subset kA
    have count : R.card+K.card=A.card := card_sdiff_add_card_eq_card kA
    have a5 : A.card=5 := by rw [card_erase_of_mem (show t∈S from ts),sz]
    have every (z : V) (zk : z∈K) (w : V) (ws : w∈S) (zw : z≠w) : G.Adj z w := by
      simp only [K,mem_insert,mem_singleton] at zk
      rcases zk with h|h|h
      · exact h.symm ▸ xUniv w ws (h ▸ zw)
      · exact h.symm ▸ outsideUniv u us un uh w ws (h ▸ zw)
      exact h.symm ▸ outsideUniv v vs vn vh w ws (h ▸ zw)
    obtain ⟨z,path,zK⟩ := universal_route_from_singletons K R
      (show x∈K by simp [K]) disjoint_sdiff_self_right
      (fun z zk w wk zw=>every z zk w (mem_of_mem_erase (all ▸ wk)) zw) (by omega)
    have ze := zK (by omega)
    have notT : t∉A := by simp [A]
    have zt : z≠t := fun e=>notT (e ▸ kA ze)
    have q := (show RouteOn G A x z from all ▸ path).suffix (every z ze t ts zt) notT
    exact (show insert t A=S from insert_erase ts) ▸ q
  rcases tHit with at'|bt
  · exact ⟨t,x,at',bx,result.reverse⟩
  exact ⟨x,t,ax,bt,result⟩

#print axioms terminal_route_on_three_port_small_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
