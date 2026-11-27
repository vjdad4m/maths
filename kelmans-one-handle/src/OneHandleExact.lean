import UnhitHandleCut

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open FourRingCutAux HandleExtension HandleExtension.Edges.AtomicHitting FourRingCyclicEquivalence
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem as_shore (minimum : MinBoundaryThree G) (c : V→Bool)
    (low : (boundary G c).card≤3) (non : ¬TrivialCut c) :
    ∃ s,ShoreThree G s ∧ colourOf s=c := by
  let s := univ.filter (fun x=>c x=true)
  have eq : colourOf s=c := by
    funext z
    by_cases h : c z=true
    · have zs : z∈s := mem_filter.mpr ⟨mem_univ _,h⟩
      exact (colour_true.mpr zs).trans h.symm
    · have cf := Bool.eq_false_iff.mpr h
      have zn : z∉s := fun hz=>h (mem_filter.mp hz).2
      exact (colour_false.mpr zn).trans cf.symm
  obtain ⟨p,q⟩ := both_colours_of_nontrivial non
  have large := minimum c p q
  refine ⟨s,⟨?_,?_⟩,eq⟩
  · rw [eq]
    omega
  · rwa [eq]

private theorem shore_has_edge (cub : ∀v,G.degree v=3) {s : Finset V}
    (hs : ShoreThree G s) : ∃ a b,a∈s∧b∈s∧G.Adj a b := by
  classical
  let c := colourOf s
  have acy : ¬(shoreGraph G c).IsAcyclic := by
    intro ac
    apply hs.2
    left
    intro x y hx hy
    refine Classical.byContradiction ?_
    intro ne
    have large := acyclic_shore_large_cut G c cub ac hx hy ne
    have small := hs.1
    change (boundary G c).card=3 at small
    omega
  refine Classical.byContradiction ?_
  intro none
  have h : shoreGraph G c=⊥ := by
    ext a b
    constructor
    · intro e
      exact (none ⟨a.val,b.val,colour_true.mp a.property,colour_true.mp b.property,e⟩).elim
    · exact False.elim
  exact acy (h.symm ▸ isAcyclic_bot)

private theorem edges_from_disjoint_shores (cub : ∀v,G.degree v=3)
    {a b : Finset V} (A : ShoreThree G a) (B : ShoreThree G b) (ab : Disjoint a b) :
    ∃ E : Edges G,(∀x,E.Ends false x→x∈a) ∧ (∀x,E.Ends true x→x∈b) := by
  obtain ⟨u,v,ua,va,ev⟩ := shore_has_edge cub A
  obtain ⟨x,y,xb,yb,ey⟩ := shore_has_edge cub B
  let E : Edges G := {
    a := fun s=>if s then x else u
    b := fun s=>if s then y else v
    edge := by intro s; cases s <;> assumption
    separated := by
      intro s t z hs ht
      cases s <;> cases t
      · rfl
      · have l : z∈a := hs.elim (fun h=>h.symm ▸ ua) (fun h=>h.symm ▸ va)
        have r : z∈b := ht.elim (fun h=>h.symm ▸ xb) (fun h=>h.symm ▸ yb)
        exact (disjoint_left.mp ab l r).elim
      · have l : z∈a := ht.elim (fun h=>h.symm ▸ ua) (fun h=>h.symm ▸ va)
        have r : z∈b := hs.elim (fun h=>h.symm ▸ xb) (fun h=>h.symm ▸ yb)
        exact (disjoint_left.mp ab l r).elim
      · rfl
  }
  exact ⟨E,fun _ h=>h.elim (fun e=>e.symm ▸ ua) (fun e=>e.symm ▸ va),
    fun _ h=>h.elim (fun e=>e.symm ▸ xb) (fun e=>e.symm ▸ yb)⟩

omit [DecidableRel G.Adj] in
private theorem triple_prevents_hitting (E : Edges G) (obstruct : ThreeDisjointShoreThree G) :
    ¬HitsSmallCuts E := by
  obtain ⟨a,b,c,A,B,C,ab,ac,bc⟩ := obstruct
  let f (i : Fin 3) : V→Bool := colourOf (if i=0 then a else if i=1 then b else c)
  have small (i : Fin 3) : (boundary G (f i)).card≤3 := by
    fin_cases i
    · exact A.1.le
    · exact B.1.le
    · exact C.1.le
  have non (i : Fin 3) : ¬TrivialCut (f i) := by
    fin_cases i
    · exact A.2
    · exact B.2
    · exact C.2
  have dj (i j : Fin 3) (ne : i≠j) (v : V) (hp : f i v=true) (hq : f j v=true) : False := by
    fin_cases i <;> fin_cases j
    all_goals
      first
      | exact ne rfl
      | exact disjoint_left.mp ab (colour_true.mp hp) (colour_true.mp hq)
      | exact disjoint_left.mp ab (colour_true.mp hq) (colour_true.mp hp)
      | exact disjoint_left.mp ac (colour_true.mp hp) (colour_true.mp hq)
      | exact disjoint_left.mp ac (colour_true.mp hq) (colour_true.mp hp)
      | exact disjoint_left.mp bc (colour_true.mp hp) (colour_true.mp hq)
      | exact disjoint_left.mp bc (colour_true.mp hq) (colour_true.mp hp)
  exact three_disjoint_shores_block_hitting E f small non dj

theorem exists_hitting_iff_no_three_disjoint
    (cub : ∀v,G.degree v=3) (conn : KelmansStarter.ThreeConnected G) :
    (∃ E : Edges G,HitsSmallCuts E) ↔ ¬ThreeDisjointShoreThree G := by
  classical
  constructor
  · rintro ⟨E,hit⟩ three
    exact triple_prevents_hitting E three hit
  · intro no
    have min := min_boundary_three_of_three_connected G cub conn
    by_cases h : ∃ s,ShoreThree G s
    · obtain ⟨s,S⟩ := h
      obtain ⟨a,b,A,B,dj,all⟩ := minimal_shores_two G min no S
      obtain ⟨E,ea,eb⟩ := edges_from_disjoint_shores cub A.1 B.1 dj
      refine ⟨E,?_⟩
      intro c low non
      obtain ⟨u,U,e⟩ := as_shore min c low non
      obtain ⟨left,right⟩|⟨left,right⟩ := minimal_shores_oppose G all U
      · refine ⟨?_,true,?_,?_⟩
        · rw [←e,U.1]
        · exact fun x hx=>e ▸ colour_true.mpr (left (ea _ hx))
        · exact fun x hx=>e ▸ colour_false.mpr (mem_compl.mp (right (eb _ hx)))
      · refine ⟨?_,false,?_,?_⟩
        · rw [←e,U.1]
        · exact fun x hx=>e ▸ colour_false.mpr (mem_compl.mp (right (ea _ hx)))
        · exact fun x hx=>e ▸ colour_true.mpr (left (eb _ hx))
    · obtain ⟨E⟩ := exists_two_disjoint_edges G cub conn.1
      refine ⟨E,?_⟩
      intro c low non
      obtain ⟨u,U,_⟩ := as_shore min c low non
      exact (h ⟨u,U⟩).elim

/-- Exact one-handle criterion: a choice of independent edges can
make the host cyclically four-edge-connected exactly when no three
pairwise disjoint nontrivial three-cut shores exist. -/
theorem exists_cyclic_handle_iff_no_three_disjoint
    (cub : ∀v,G.degree v=3) (conn : KelmansStarter.ThreeConnected G) :
    (∃ E : Edges G,SmallTrivial E.host) ↔ ¬ThreeDisjointShoreThree G := by
  rw [←exists_hitting_iff_no_three_disjoint cub conn]
  have min := min_boundary_three_of_three_connected G cub conn
  constructor
  · rintro ⟨E,h⟩
    exact ⟨E,(cyclic_host_iff_hits E cub min).mp h⟩
  · rintro ⟨E,h⟩
    exact ⟨E,(cyclic_host_iff_hits E cub min).mpr h⟩

/-- Conditional packing bridge for all nonbranching three-cut
systems, without a specified decomposing edge or fixed atom size. -/
theorem cyclic4_factor_implies_no_three_disjoint_shores
    (promise : CyclicUniversal.{u}) (cub : ∀v,G.degree v=3)
    (conn : KelmansStarter.ThreeConnected G) (dvd : 6∣Fintype.card V)
    (no : ¬ThreeDisjointShoreThree G) : KelmansStarter.HasP3Factor G := by
  obtain ⟨E,hit⟩ := (exists_hitting_iff_no_three_disjoint cub conn).mpr no
  have sub : E.deleteChosen≤G := fun _ _ e=>e.1
  exact factor_mono sub (factor_avoids_hitting_pair E promise cub dvd hit)

#print axioms exists_hitting_iff_no_three_disjoint
#print axioms exists_cyclic_handle_iff_no_three_disjoint
#print axioms cyclic4_factor_implies_no_three_disjoint_shores
end
end KelmansCactus.AtomicBridge.OddUncross
