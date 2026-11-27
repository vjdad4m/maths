import DegreeFiveTwoFourShapes189
import DegreeFiveRouteBasic189
import WingSignature189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private inside_high_at_least_four_if_exclusive inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open ArticulationPair
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem terminal_route_on_two_or_three_port_near_six
    (hc : G.Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (C2 : 2≤(cutPorts C).card) (C3 : (cutPorts C).card≤3)
    (size : (Shore C).card=6)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (near : (secondShore C x).card≤1 ∧ ∀ v∈Shore C,G.dist x v≤2) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let S := Shore C
  let E := S \ cutPorts C
  have eCount : E.card+(cutPorts C).card=S.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have xP : x∈cutPorts C := mem_filter.mpr ⟨xc,.inl ax⟩
  have other : ∃ t∈cutPorts C,t≠x := by
    apply Classical.byContradiction
    intro no
    have sub : cutPorts C⊆{x} := fun t tp=>mem_singleton.mpr
      (Classical.byContradiction (fun h=>no ⟨t,tp,h⟩))
    have h := card_le_card sub
    rw [card_singleton] at h
    omega
  obtain ⟨t,tp,tx⟩ := other
  obtain ⟨ts,tHit⟩ := mem_filter.mp tp
  have sz : S.card=6 := size
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
  have r2 : R.card=2 := by omega
  have pack {r s : V} (rr : r∈R) (sr : s∈R) (rs : r≠s) (eq : R={r,s})
      (xr : G.Adj x r) : RouteOn G S x t := by
    have re := (mem_sdiff.mp rr).1
    have se := (mem_sdiff.mp sr).1
    have rsS : r∈S := mem_of_mem_erase re
    have ssS : s∈S := mem_of_mem_erase se
    have rK := (mem_sdiff.mp rr).2
    have sK := (mem_sdiff.mp sr).2
    have rx : r≠x := fun e=>rK (e.symm ▸ (show x∈K by simp [K]))
    have ru : r≠u := fun e=>rK (e.symm ▸ (show u∈K by simp [K]))
    have rv : r≠v := fun e=>rK (e.symm ▸ (show v∈K by simp [K]))
    have sx : s≠x := fun e=>sK (e.symm ▸ (show x∈K by simp [K]))
    have su : s≠u := fun e=>sK (e.symm ▸ (show u∈K by simp [K]))
    have sv : s≠v := fun e=>sK (e.symm ▸ (show v∈K by simp [K]))
    have rt : r≠t := (mem_erase.mp re).1
    have st : s≠t := (mem_erase.mp se).1
    have p := RouteOn.three xr (outsideUniv u us un uh r rsS ru.symm).symm ux.symm
    have q := ((p.suffix (outsideUniv u us un uh s ssS su.symm) (by simp [sx,rs.symm,su])).suffix
      (outsideUniv v vs vn vh s ssS sv.symm).symm (by simp [sv.symm,vx,rv.symm,vu])).suffix
        (outsideUniv v vs vn vh t ts tv.symm) (by simp [tv,st.symm,tx,rt.symm,tu])
    have total : insert t (insert v (insert s ({x,r,u} : Finset V)))=S := by
      rw [←insert_erase (show t∈S from ts),←show K∪R=S.erase t from all,eq]
      ext w
      simp [K,or_left_comm,or_assoc,or_comm]
    exact total ▸ q
  obtain ⟨r,s,rs,eq⟩ := card_eq_two.mp r2
  have rr : r∈R := by simp [eq]
  have sr : s∈R := by simp [eq]
  have good : G.Adj x r ∨ G.Adj x s := by
    apply Classical.byContradiction
    intro h
    have see {w : V} (wr : w∈R) : w∈secondShore C x := by
      have base := (mem_sdiff.mp wr).1
      have ws := mem_of_mem_erase base
      have wK := (mem_sdiff.mp wr).2
      have ne : x≠w := fun e=>wK (e ▸ (show x∈K by simp [K]))
      have no : ¬G.Adj x w := by
        intro e
        have choice : w=r ∨ w=s := by simpa [eq] using wr
        exact choice.elim (fun f=>h (.inl (f ▸ e))) (fun f=>h (.inr (f ▸ e)))
      have lo := hc.one_lt_dist_of_ne_of_not_adj ne no
      have hi := near.2 w ws
      exact mem_inter.mpr ⟨ws,by simp [DistanceTwo,show G.dist x w=2 by omega]⟩
    have many := one_lt_card.mpr ⟨r,see rr,s,see sr,rs⟩
    have on := near.1
    omega
  have route : RouteOn G S x t := good.elim (pack rr sr rs eq)
    (pack sr rr rs.symm (eq.trans (by ext w; simp [or_comm])))
  rcases tHit with at'|bt
  · exact ⟨t,x,at',bx,route.reverse⟩
  exact ⟨x,t,ax,bt,route⟩

#print axioms terminal_route_on_two_or_three_port_near_six
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
