import FourRingSmallCuts

open Finset SimpleGraph
namespace KelmansCactus.FourRingCutAux
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
variable [DecidableRel G.Adj]

private abbrev survivors (D : Finset V) : Set V := {x | x∉D}

private def component_colour {D : Finset V} (x : survivors D) (v : V) : Bool := by
  classical
  exact if h : v∉D then decide ((G.induce (survivors D)).Reachable x ⟨v,h⟩) else false

omit [Fintype V] [DecidableRel G.Adj] in
private theorem component_colour_true_iff {D : Finset V}
    (x : survivors D) (v : V) :
    component_colour G x v=true ↔ ∃ h : v∉D,(G.induce (survivors D)).Reachable x ⟨v,h⟩ := by
  classical
  by_cases h : v∉D
  · simp [component_colour,h]
  · simp [component_colour,h]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem reach_colour {D : Finset V} (x v : survivors D) :
    component_colour G x v.val=true ↔ (G.induce (survivors D)).Reachable x v := by
  rw [component_colour_true_iff]
  exact ⟨fun ⟨_,r⟩=>r,fun r=>⟨v.property,r⟩⟩

omit [DecidableEq V] in
private theorem survivor_neighbor (cub : ∀v,G.degree v=3) {D : Finset V} (small : D.card≤2)
    (x : survivors D) : ∃ y : survivors D, (G.induce (survivors D)).Adj x y := by
  classical
  by_contra! no
  have sub : G.neighborFinset x.val ⊆ D := by
    intro v mv
    by_contra! h
    exact no ⟨v,h⟩ ((mem_neighborFinset G x.val v).mp mv)
  have b := card_le_card sub
  rw [card_neighborFinset_eq_degree,cub] at b
  omega

private theorem component_cut_big (cub : ∀v,G.degree v=3) (smallCut : SmallTrivial G)
    {D : Finset V} (small : D.card≤2) {x y : survivors D}
    (separate : ¬(G.induce (survivors D)).Reachable x y) :
    4≤(boundary G (component_colour G x)).card := by
  classical
  obtain ⟨u,ed1⟩ := survivor_neighbor G cub small x
  obtain ⟨v,ed2⟩ := survivor_neighbor G cub small y
  have cxx : component_colour G x x.val=true := (reach_colour G x x).mpr (Reachable.refl _)
  have cxy : component_colour G x y.val=false := by
    by_contra! h
    exact separate ((reach_colour G x y).mp (by simpa using h))
  have cxu : component_colour G x u.val=true := (reach_colour G x u).mpr ed1.reachable
  have cxv : component_colour G x v.val=false := by
    by_contra! h
    exact separate (((reach_colour G x v).mp (by simpa using h)).trans ed2.reachable.symm)
  by_contra! tiny
  rcases smallCut (component_colour G x) (by omega) with one|other
  · exact (show G.Adj x.val u.val from ed1).ne (one _ _ cxx cxu)
  · exact (show G.Adj y.val v.val from ed2).ne (other _ _ cxy cxv)

private def incoming (D : Finset V) : Finset (V×V) :=
  D.biUnion (fun v=>(G.neighborFinset v).image (fun w=>(w,v)))

private theorem incoming_card_le (cub : ∀v,G.degree v=3) (D : Finset V) :
    (incoming G D).card≤3*D.card := by
  classical
  unfold incoming
  apply (card_biUnion_le).trans
  have c (v : V) : ((G.neighborFinset v).image (fun w=>(w,v))).card≤3 := by
    apply card_image_le.trans
    rw [card_neighborFinset_eq_degree,cub]
  calc
    (∑ v∈D,((G.neighborFinset v).image (fun w=>(w,v))).card) ≤ ∑ _∈D,3 :=
      sum_le_sum (fun v _=>c v)
    _ = _ := by simp [Nat.mul_comm]

private theorem component_incoming {D : Finset V} (x : survivors D) :
    boundary G (component_colour G x) ⊆ incoming G D := by
  rintro ⟨u,v⟩ h
  obtain ⟨yes,no,e⟩ := mem_boundary.mp h
  obtain ⟨hu,ru⟩ := (component_colour_true_iff G x u).mp yes
  have inD : v∈D := by
    by_contra nd
    have edge : (G.induce (survivors D)).Adj ⟨u,hu⟩ ⟨v,nd⟩ := e
    have y := (component_colour_true_iff G x v).mpr ⟨nd,ru.trans edge.reachable⟩
    rw [no] at y
    contradiction
  exact mem_biUnion.mpr ⟨v,inD,mem_image.mpr
    ⟨u,(mem_neighborFinset G v u).mpr e.symm,rfl⟩⟩

/-- Absence of nontrivial cuts of size at most three implies
3-vertex-connectivity in a simple cubic graph. After deleting at
most two vertices, two different components would each have
at least four edges going into the deletion set of capacity six. -/
theorem three_connected_of_small_trivial (cub : ∀v,G.degree v=3)
    (large : 4≤Fintype.card V) (smallCut : SmallTrivial G) :
    KelmansStarter.ThreeConnected G := by
  classical
  refine ⟨large,?_⟩
  intro D small
  haveI : Nonempty (survivors D) := by
    have lt : D.card<(univ:Finset V).card := by rw [card_univ]; omega
    obtain ⟨v,_,h⟩ := exists_mem_not_mem_of_card_lt_card lt
    exact ⟨⟨v,h⟩⟩
  constructor
  intro x y
  by_contra separate
  let R := G.induce (survivors D)
  let F := boundary G (component_colour G x)
  let H := boundary G (component_colour G y)
  have lx : 4≤F.card := component_cut_big G cub smallCut small separate
  have ly : 4≤H.card := component_cut_big G cub smallCut small (fun r=>separate r.symm)
  have dj : Disjoint F H := by
    apply disjoint_left.mpr
    intro z zF zH
    obtain ⟨e,ex⟩ := (component_colour_true_iff G x z.1).mp (mem_boundary.mp zF).1
    obtain ⟨f,ey⟩ := (component_colour_true_iff G y z.1).mp (mem_boundary.mp zH).1
    exact separate (ex.trans ey.symm)
  have sub : F∪H⊆incoming G D := union_subset (component_incoming G x) (component_incoming G y)
  have lc := card_le_card sub
  rw [card_union_of_disjoint dj] at lc
  have capacity := incoming_card_le G cub D
  omega

#print axioms three_connected_of_small_trivial
end
end KelmansCactus.FourRingCutAux
