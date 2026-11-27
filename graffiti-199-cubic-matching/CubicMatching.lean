import CubicMatchingLower
import ConnectivitySplice

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

private def forkEdges : List (Fin 6 × Fin 6) := [(0,1),(1,2),(0,3),(3,4),(0,5)]

private def forkAdj (i j : Fin 6) : Bool :=
  forkEdges.contains (i,j) || forkEdges.contains (j,i)

private theorem forkEarlier : ∀ i : Fin 6, i ≠ 0 →
    ∃ j : Fin 6, forkAdj i j = true ∧ j < i ∧
      ∀ k : Fin 6, forkAdj i k = true → k < i → k = j := by decide

namespace CubicEdge

variable {P Q : CubicEdge G}

/-- The local shared-port trapping argument works with arbitrary
degrees and edges on the port sets. -/
theorem shared_port_no_exits (apart : P.Apart Q) (budget : Catalogue.treeNumber G ≤ 5)
    {x y : V} (xp : x ∈ P.ports) (xq : x ∈ Q.ports)
    (yp : y ∉ P.region) (yq : y ∉ Q.region) :
    ¬ G.Adj x y := by
  intro xy
  classical
  obtain ⟨p,px,pOff⟩ := P.neighbor_half xp
  obtain ⟨q,qx,qOff⟩ := Q.neighbor_half xq
  have pNe := (P.mem_ports.mp xp).1
  have qNe := (Q.mem_ports.mp xq).1
  have pyNe (s : Bool) : P.low s ≠ y := fun e => yp (e ▸ P.low_mem_region s)
  have qyNe (s : Bool) : Q.low s ≠ y := fun e => yq (e ▸ Q.low_mem_region s)
  have pyOff (s : Bool) : ¬ G.Adj (P.low s) y := fun edge => yp (P.low_neighbor_mem_region edge)
  have qyOff (s : Bool) : ¬ G.Adj (Q.low s) y := fun edge => yq (Q.low_neighbor_mem_region edge)
  have pp := P.low_adj p
  have qq := Q.low_adj q
  let L := [x,P.low p,P.low (!p),Q.low q,Q.low (!q),y]
  have nd : L.Nodup := by
    simp [L,pNe,qNe,apart.distinct,pyNe,qyNe,xy.ne,pp.ne,qq.ne]
  let f : Fin 6 ↪ V := ⟨L.get,fun _ _ e => nd.get_inj_iff.mp e⟩
  have revNoCross (a b : Bool) : ¬ G.Adj (Q.low b) (P.low a) := fun h => apart.no_cross a b h.symm
  have revPy (s : Bool) : ¬ G.Adj y (P.low s) := fun h => pyOff s h.symm
  have revQy (s : Bool) : ¬ G.Adj y (Q.low s) := fun h => qyOff s h.symm
  have pOff' : ¬ G.Adj (P.low (!p)) x := fun h => pOff h.symm
  have qOff' : ¬ G.Adj (Q.low (!q)) x := fun h => qOff h.symm
  have v0 : f 0 = x := rfl
  have v1 : f 1 = P.low p := rfl
  have v2 : f 2 = P.low (!p) := rfl
  have v3 : f 3 = Q.low q := rfl
  have v4 : f 4 = Q.low (!q) := rfl
  have v5 : f 5 = y := rfl
  have chart (a b : Fin 6) : G.Adj (f a) (f b) ↔ forkAdj a b = true := by
    fin_cases a <;> fin_cases b <;>
      simp [v0,v1,v2,v3,v4,v5,forkAdj,forkEdges,px,px.symm,pOff,pOff',qx,qx.symm,qOff,qOff',
        pp,pp.symm,qq,qq.symm,xy,xy.symm,apart.no_cross,revNoCross,pyOff,qyOff,revPy,revQy] <;> decide
  have six := Catalogue.six_le_treeNumber_of_ordering (G := G) f (by
    intro i hi
    obtain ⟨j,ij,lt,all⟩ := forkEarlier i hi
    exact ⟨j,(chart _ _).mpr ij,lt,fun k e l => all k ((chart _ _).mp e) l⟩)
  omega

/-- If the two cubic edges have at least three shared ports, at most
nine vertices occur in their two regions. The at most two private
ports separate those regions from any vertex outside them. -/
theorem common_ports_lt_three (apart : P.Apart Q)
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card V) :
    (P.commonPorts Q).card < 3 := by
  classical
  let R := P.ports ∩ Q.ports
  let D := (P.ports ∪ Q.ports) \ R
  change R.card < 3
  by_contra! many
  have countP := P.ports_card
  have countQ := Q.ports_card
  have sum := Finset.card_union_add_card_inter P.ports Q.ports
  change (P.ports ∪ Q.ports).card + R.card = P.ports.card + Q.ports.card at sum
  have sub : R ⊆ P.ports ∪ Q.ports := fun _ h =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp h).1)
  have dCard : D.card = (P.ports ∪ Q.ports).card - R.card := Finset.card_sdiff sub
  have few : D.card < 3 := by omega
  let C := P.regionFinset ∪ Q.regionFinset
  have pc := P.region_card_le
  have qc := Q.region_card_le
  have inter : R ⊆ P.regionFinset ∩ Q.regionFinset := fun _ hx =>
    Finset.mem_inter.mpr ⟨P.mem_regionFinset.mpr (Or.inr (Finset.mem_inter.mp hx).1),
      Q.mem_regionFinset.mpr (Or.inr (Finset.mem_inter.mp hx).2)⟩
  have rle := Finset.card_le_card inter
  have union := Finset.card_union_add_card_inter P.regionFinset Q.regionFinset
  have smallC : C.card ≤ 9 := by
    change (P.regionFinset ∪ Q.regionFinset).card ≤ 9
    omega
  have proper : C.card < (Finset.univ : Finset V).card := by simpa using (show C.card < Fintype.card V by omega)
  obtain ⟨z,_,zOff⟩ := Finset.exists_mem_not_mem_of_card_lt_card proper
  let U := P.region ∪ Q.region
  have zOutside : z ∉ U := by
    rintro (p|q)
    · exact zOff (Finset.mem_union.mpr (Or.inl (P.mem_regionFinset.mpr p)))
    · exact zOff (Finset.mem_union.mpr (Or.inr (Q.mem_regionFinset.mpr q)))
  have zKeep : z ∉ D := by
    intro h
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp h).1 with hp|hq
    · exact zOutside (Or.inl (Or.inr hp))
    · exact zOutside (Or.inr (Or.inr hq))
  have pKeep : P.low false ∉ D := by
    intro h
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp h).1 with hp|hq
    · exact P.low_not_port false hp
    · exact apart.symm.no_low_in_other_port false hq
  have below (S : Finset V) (small : S.card < 3) :
      (G.induce {v | v ∉ S}).Preconnected := (conn.2 S small).preconnected
  obtain ⟨x,xU,y,yU,xKeep,_,edge⟩ := cross_after_fewer_than_three below few
    (U := U) (Or.inl (P.low_mem_region false)) zOutside pKeep zKeep
  have yP : y ∉ P.region := fun hp => yU (Or.inl hp)
  have yQ : y ∉ Q.region := fun hq => yU (Or.inr hq)
  have highImpossible (h : x ∈ P.ports ∪ Q.ports) : False := by
    have shared : x ∈ R := Classical.byContradiction fun off =>
      xKeep (Finset.mem_sdiff.mpr ⟨h,off⟩)
    obtain ⟨xp,xq⟩ := Finset.mem_inter.mp shared
    exact shared_port_no_exits apart budget xp xq yP yQ edge
  rcases xU with (lp|hp)|(lq|hq)
  · rcases (show x = P.u ∨ x = P.v from by simpa using lp) with rfl|rfl
    · exact yP (P.low_neighbor_mem_region (b := false) edge)
    · exact yP (P.low_neighbor_mem_region (b := true) edge)
  · exact highImpossible (Finset.mem_union.mpr (Or.inl hp))
  · rcases (show x = Q.u ∨ x = Q.v from by simpa using lq) with rfl|rfl
    · exact yQ (Q.low_neighbor_mem_region (b := false) edge)
    · exact yQ (Q.low_neighbor_mem_region (b := true) edge)
  · exact highImpossible (Finset.mem_union.mpr (Or.inr hq))

end CubicEdge

/-- Under the exact archived cut hypothesis, the degree-three vertices
induce a graph with no induced two-edge matching. -/
theorem no_induced_two_cubic_edges
    (cross : CrossingBetweenSurvivingEdges G)
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card V)
    {u v x y : V}
    (uv : G.Adj u v) (xy : G.Adj x y)
    (du : G.degree u = 3) (dv : G.degree v = 3) (dx : G.degree x = 3) (dy : G.degree y = 3)
    (ux : ¬ G.Adj u x) (uy : ¬ G.Adj u y) (vx : ¬ G.Adj v x) (vy : ¬ G.Adj v y) :
    False := by
  let P : CubicEdge G :=
    ⟨u,v,uv,du,dv,adjacent_cubic_no_common_neighbor cross conn budget order uv du dv⟩
  let Q : CubicEdge G :=
    ⟨x,y,xy,dx,dy,adjacent_cubic_no_common_neighbor cross conn budget order xy dx dy⟩
  have no_cross (a b : Bool) : ¬ G.Adj (P.low a) (Q.low b) := by
    cases a <;> cases b <;> assumption
  have apart : P.Apart Q :=
    ⟨fun a b eq => no_cross (!a) b (eq ▸ (P.low_adj a).symm),no_cross⟩
  exact Nat.not_lt_of_ge (CubicEdge.three_le_common_ports apart conn budget)
    (CubicEdge.common_ports_lt_three apart conn budget order)

/-- All edges induced by the degree-three vertices belong to one
connected component of that induced graph. -/
theorem cubic_edges_in_same_component
    (cross : CrossingBetweenSurvivingEdges G)
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card V)
    {u v x y : {w : V // G.degree w = 3}}
    (uv : (G.induce {w | G.degree w = 3}).Adj u v)
    (xy : (G.induce {w | G.degree w = 3}).Adj x y) :
    (G.induce {w | G.degree w = 3}).Reachable u x := by
  classical
  by_contra no
  let H := G.induce {w | G.degree w = 3}
  have ux (edge : H.Adj u x) : False := no edge.reachable
  have uy (edge : H.Adj u y) : False := no (edge.reachable.trans xy.symm.reachable)
  have vx (edge : H.Adj v x) : False := no (uv.reachable.trans edge.reachable)
  have vy (edge : H.Adj v y) : False :=
    no (uv.reachable.trans (edge.reachable.trans xy.symm.reachable))
  exact no_induced_two_cubic_edges cross conn budget order
    (show G.Adj u.val v.val from uv) (show G.Adj x.val y.val from xy)
    u.property v.property x.property y.property ux uy vx vy

#print axioms CubicEdge.shared_port_no_exits
#print axioms CubicEdge.common_ports_lt_three
#print axioms no_induced_two_cubic_edges
#print axioms cubic_edges_in_same_component

end Graffiti199Depleted
