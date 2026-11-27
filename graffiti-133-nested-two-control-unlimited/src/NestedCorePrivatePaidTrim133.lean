import NestedCoreThreeGate133

namespace Graffiti133NestedCore
open SimpleGraph Finset Graffiti133 Graffiti133ExteriorSlack Graffiti133ExactTriangleCharge
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

def paidTrim (G : SimpleGraph V) (K A : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((x∈K ↔ y∈K) ∨ x∈A ∨ y∈A)
  symm := by intro x y e; exact ⟨e.1.symm,e.2.imp Iff.symm Or.symm⟩
  loopless := by intro x e; exact G.loopless x e.1

theorem paid_trim_le (K A : Finset V) : paidTrim G K A≤G := fun _ _ h=>h.1

theorem paid_trim_base_unchanged (K A : Finset V) :
    (paidTrim G K A).induce (K : Set V)=G.induce (K : Set V) := by
  ext x y
  exact ⟨fun h=>h.1,fun h=>⟨h,Or.inl (iff_of_true x.property y.property)⟩⟩

theorem paid_crossing_trim_dominates_local_sum (K A : Finset V) (ak : A⊆K)
    (h4 : FourCycleFree G)
    (paid : ∀ r∉K,∀ z∈K,z∉A→G.Adj r z→∃ a∈A,G.Adj r a ∧ G.Adj z a) :
    (∑ w : V,localIndependence G w)+
      ((arcSet G.Adj (Finset.univ\K) K)\(arcSet (paidTrim G K A).Adj (Finset.univ\K) K)).card ≤
      ∑ w : V,localIndependence (paidTrim G K A) w := by
  classical
  let J := paidTrim G K A
  let R := (Finset.univ : Finset V)\K
  let L := arcSet G.Adj R K \ arcSet J.Adj R K
  let T := G.cliqueFinset 3 \ J.cliqueFinset 3
  have le : J≤G := paid_trim_le K A
  have j4 : FourCycleFree J := fun a b x y ne ax bx ay byy=>h4 a b x y ne (le ax) (le bx) (le ay) (le byy)
  have rout (r : V) (rm : r∈R) : r∉K := (Finset.mem_sdiff.mp rm).2
  have dis : Disjoint K R := Finset.disjoint_left.mpr (fun r hk hr=>rout r hr hk)
  have union : K∪R=Finset.univ := by ext x; simp [R,or_comm]
  have middle (e : V×V) (m : e∈L) : e.1∈R ∧ e.2∈K ∧ e.2∉A ∧ G.Adj e.1 e.2 ∧ ¬J.Adj e.1 e.2 := by
    obtain ⟨g,j⟩ := Finset.mem_sdiff.mp m
    obtain ⟨xr,yk,ed⟩ := mem_arcSet.mp g
    have no : ¬J.Adj e.1 e.2 := fun r=>j (mem_arcSet.mpr ⟨xr,yk,r⟩)
    have qa : e.2∉A := fun z=>no ⟨ed,Or.inr (Or.inr z)⟩
    exact ⟨xr,yk,qa,ed,no⟩
  have witness (e : (L : Set (V×V))) :
      ∃ a∈A,G.Adj e.val.1 a ∧ G.Adj e.val.2 a := by
    obtain ⟨xr,yk,qa,ed,_⟩ := middle e.val e.property
    exact paid _ (rout _ xr) _ yk qa ed
  choose p hp using witness
  let f (e : V×V) : Finset V := if m : e∈L then {e.1,e.2,p ⟨e,m⟩} else ∅
  have ev (e : V×V) (m : e∈L) : f e={e.1,e.2,p ⟨e,m⟩} := dif_pos m
  have into (e : V×V) (em : e∈L) : f e∈T := by
    have a := hp ⟨e,em⟩
    obtain ⟨xr,yk,_,adj,no⟩ := middle e em
    rw [ev e em]
    apply Finset.mem_sdiff.mpr
    refine ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨adj,a.2.1,a.2.2⟩),?_⟩
    intro tm
    exact no (SimpleGraph.is3Clique_triple_iff.mp (SimpleGraph.mem_cliqueFinset_iff.mp tm)).1
  have inj : Set.InjOn f L := by
    intro e em d dm eq
    have ea := (hp ⟨e,em⟩).1
    have da := (hp ⟨d,dm⟩).1
    obtain ⟨xr,yk,yna,_,_⟩ := middle e em
    obtain ⟨dr,dk,dna,_,_⟩ := middle d dm
    rw [ev e em,ev d dm] at eq
    have r : e.1∈({d.1,d.2,p ⟨d,dm⟩} : Finset V) := by rw [←eq]; simp
    have z : e.2∈({d.1,d.2,p ⟨d,dm⟩} : Finset V) := by rw [←eq]; simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at r z
    have r' : e.1=d.1 := by
      rcases r with q|q|q
      · exact q
      · exact (rout _ xr (q.symm ▸ dk)).elim
      · exact (rout _ xr (q.symm ▸ ak da)).elim
    have z' : e.2=d.2 := by
      rcases z with q|q|q
      · exact (rout _ dr (q ▸ yk)).elim
      · exact q
      · exact (yna (q.symm ▸ da)).elim
    exact Prod.ext r' z'
  have lost := Finset.card_le_card_of_injOn f into inj
  have triangles : T.card+triangleCount J=triangleCount G :=
    Finset.card_sdiff_add_card_eq_card (SimpleGraph.cliqueFinset_mono (G:=J) G (n:=3) le)
  have arcs : L.card+(arcSet J.Adj R K).card=(arcSet G.Adj R K).card := by
    apply Finset.card_sdiff_add_card_eq_card
    intro e em
    obtain ⟨r,k,h⟩ := mem_arcSet.mp em
    exact mem_arcSet.mpr ⟨r,k,le h⟩
  have baseArcs : arcSet J.Adj K K=arcSet G.Adj K K := by
    ext e
    rw [mem_arcSet,mem_arcSet]
    refine ⟨fun h=>⟨h.1,h.2.1,le h.2.2⟩,fun h=>⟨h.1,h.2.1,h.2.2,Or.inl (iff_of_true h.1 h.2.1)⟩⟩
  have baseCount := congrArg Finset.card baseArcs
  rw [card_arcs_core (G:=J),card_arcs_core (G:=G)] at baseCount
  have baseSame : (J.induce (K : Set V)).edgeFinset.card=(G.induce (K : Set V)).edgeFinset.card := by omega
  have outerSame : arcSet J.Adj R R=arcSet G.Adj R R := by
    ext e
    rw [mem_arcSet,mem_arcSet]
    refine ⟨fun h=>⟨h.1,h.2.1,le h.2.2⟩,fun h=>⟨h.1,h.2.1,h.2.2,Or.inl ?_⟩⟩
    exact iff_of_false (rout _ h.1) (rout _ h.2.1)
  have gEdges := degree_score_arcs_decomposition (G:=G) K R dis union
  have jEdges := degree_score_arcs_decomposition (G:=J) K R dis union
  rw [baseSame,outerSame] at jEdges
  have g := sum_degree_eq_local_add_triangles h4
  have j := sum_degree_eq_local_add_triangles j4
  have close {e jE p x xJ k t tJ l s sJ d : Nat}
      (hg : 2*e=p+2*x+k) (hj : 2*jE=p+2*xJ+k) (ha : l+xJ=x)
      (ht : d+tJ=t) (pay : l≤d) (wg : s+3*t=2*e) (wj : sJ+3*tJ=2*jE) :
      s+l≤sJ := by omega
  exact close gEdges jEdges arcs triangles lost g j

theorem three_retained_gates_with_paid_crossings_mean_four (K A : Finset V)
    (ak : A⊆K) (a3 : A.card=3) (h4 : FourCycleFree G)
    (sees : ∀ x∉K,∃ y∈A,G.Adj x y)
    (paid : ∀ r∉K,∀ z∈K,z∉A→G.Adj r z→∃ a∈A,G.Adj r a ∧ G.Adj z a)
    (slack : (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+2≤4*K.card) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  let J := paidTrim G K A
  have le : J≤G := paid_trim_le K A
  have j4 : FourCycleFree J := fun a b x y ne ax bx ay byy=>h4 a b x y ne (le ax) (le bx) (le ay) (le byy)
  have seesJ (x : V) (xo : x∉K) : ∃ y∈A,J.Adj x y := by
    obtain ⟨y,ym,xy⟩ := sees x xo
    exact ⟨y,ym,xy,Or.inr (Or.inr ym)⟩
  have gateJ (x : V) (xo : x∉K) (y : V) (ym : y∈K) (e : J.Adj x y) : y∈A := by
    rcases e.2 with q|q|q
    · exact (xo (q.mpr ym)).elim
    · exact (xo (ak q)).elim
    · exact q
  have trim := paid_crossing_trim_dominates_local_sum K A ak h4 paid
  have result := three_gate_preserves_score_up_to_triples (G:=J) K A ak a3 j4 seesJ gateJ
  have triples := at_most_one_triple_gate_vertex j4 A (Finset.univ\K) a3
  have same : J.induce (K : Set V)=G.induce (K : Set V) := paid_trim_base_unchanged K A
  rw [same] at result
  have aux {g j x n k q l : Nat} (trim : g+l≤j) (jbound : j+4*k≤x+4*n+2*q)
      (qbound : q≤1) (spare : x+2≤4*k) : g≤4*n := by omega
  exact aux trim result triples slack

#print axioms three_retained_gates_with_paid_crossings_mean_four
#print axioms paid_crossing_trim_dominates_local_sum
end Graffiti133NestedCore
