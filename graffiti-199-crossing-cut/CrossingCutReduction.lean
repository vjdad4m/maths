import TwoVertexShore

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}

abbrev DeletionGraph (G : SimpleGraph V) (D : Finset V) :=
  G.induce {v : V | v ∉ D}

def componentShore (D : Finset V) (C : (DeletionGraph G D).ConnectedComponent) : Set V :=
  Subtype.val '' C.supp

theorem componentShore_off_cut (D : Finset V) (C : (DeletionGraph G D).ConnectedComponent)
    (v : V) (vD : v ∈ D) : v ∉ componentShore D C := by
  rintro ⟨a,_,rfl⟩
  exact a.property vD

theorem componentShore_boundary (D : Finset V) (C : (DeletionGraph G D).ConnectedComponent) :
    ShoreBoundary G D (componentShore D C) := by
  rintro v ⟨x,hx,rfl⟩ w hw edge
  apply Classical.byContradiction
  intro wOff
  let y : Survives D := ⟨w,wOff⟩
  have step : (DeletionGraph G D).Adj x y := edge
  exact hw ⟨y,(C.mem_supp_congr_adj step).mp hx,rfl⟩

theorem componentShore_connected (D : Finset V) (C : (DeletionGraph G D).ConnectedComponent) :
    (G.induce (componentShore D C)).Connected := by
  let f : C.supp → componentShore D C := fun x => ⟨x.val.val,⟨x.val,x.property,rfl⟩⟩
  have inj : Function.Injective f := fun _ _ e => Subtype.ext (Subtype.ext
    (congrArg (fun t : componentShore D C => t.val) e))
  have onto : Function.Surjective f := by
    rintro ⟨y,⟨x,xC,rfl⟩⟩
    exact ⟨⟨x,xC⟩,rfl⟩
  let e := Equiv.ofBijective f ⟨inj,onto⟩
  let iso : (DeletionGraph G D).induce C.supp ≃g
      G.induce (componentShore D C) := ⟨e,fun {_ _} => Iff.rfl⟩
  exact iso.connected_iff.mp C.connected_induce_supp

theorem componentShore_disjoint {D : Finset V} {C E : (DeletionGraph G D).ConnectedComponent}
    (ne : C ≠ E) : Disjoint (componentShore D C) (componentShore D E) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨x,hx,rfl⟩ ⟨y,hy,eq⟩
  have yx : y = x := Subtype.ext eq
  exact ne (ConnectedComponent.eq_of_common_vertex hx (yx ▸ hy))

structure LargeCrossingFailure (G : SimpleGraph V) where
  cut : Finset V
  size : cut.card = 3
  first : (DeletionGraph G cut).ConnectedComponent
  second : (DeletionGraph G cut).ConnectedComponent
  different : first ≠ second
  first_large : 3 ≤ Nat.card (componentShore cut first)
  second_large : 3 ≤ Nat.card (componentShore cut second)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem large_component_of_edge {D : Finset V}
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (size : D.card = 3)
    (no : ¬ Traceable G)
    (cubic : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    {a b : Survives D} (edge : G.Adj a.val b.val) :
    3 ≤ Nat.card (componentShore D ((DeletionGraph G D).connectedComponentMk a)) := by
  classical
  let C := (DeletionGraph G D).connectedComponentMk a
  let A := componentShore D C
  have ha : a.val ∈ A := ⟨a,rfl,rfl⟩
  have hb : b.val ∈ A :=
    ⟨b,(C.mem_supp_congr_adj (show (DeletionGraph G D).Adj a b from edge)).mp rfl,rfl⟩
  have third : ∃ v ∈ A, v ≠ a.val ∧ v ≠ b.val := by
    apply Classical.byContradiction
    intro fail
    have setEq : A = ({a.val,b.val} : Set V) := by
      ext v
      constructor
      · intro h
        apply Classical.byContradiction
        intro outside
        have va : v ≠ a.val := fun e => outside (Or.inl e)
        have vb : v ≠ b.val := fun e => outside (Or.inr e)
        exact fail ⟨v,h,va,vb⟩
      · rintro (h|h)
        · exact h.symm ▸ ha
        · exact h.symm ▸ hb
    exact no (traceable_of_two_vertex_shore_of_independent_cubics
      smaller conn budget order size a.property b.property edge
      (setEq ▸ componentShore_boundary D C) cubic)
  obtain ⟨c,hc,ca,cb⟩ := third
  let T : Finset V := {a.val,b.val,c}
  have ts : T.card = 3 := by
    change (insert a.val ({b.val,c} : Finset V)).card = 3
    rw [Finset.card_insert_of_not_mem (by simp [edge.ne,ca.symm]),Finset.card_pair cb.symm]
  let f : T → A := fun t => ⟨t.val, by
    have h : t.val ∈ insert a.val ({b.val,c} : Finset V) := t.property
    rcases Finset.mem_insert.mp h with e|rest
    · exact e.symm ▸ ha
    · rcases Finset.mem_insert.mp rest with e|last
      · exact e.symm ▸ hb
      · exact (Finset.mem_singleton.mp last).symm ▸ hc⟩
  have inj : Function.Injective f := fun _ _ e => Subtype.ext (congrArg (fun t : A => t.val) e)
  have big := Fintype.card_le_of_injective f inj
  rw [Fintype.card_coe,ts] at big
  simpa [Nat.card_eq_fintype_card,A,C] using big

/-- Failure of the old crossing hypothesis requires two distinct surviving
components of order at least three in the independent-cubic branch. -/
theorem large_crossing_failure_of_independent_cubics
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (cubic : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    (fail : ¬ CrossingBetweenSurvivingEdges G) :
    Nonempty (LargeCrossingFailure G) := by
  have f : ¬ EdgeReachAfterSmallDeletion G :=
    fun reach => fail (edgeReach_iff_crossing_between_surviving_edges.mp reach)
  unfold EdgeReachAfterSmallDeletion at f
  push_neg at f
  obtain ⟨D,small,a,b,c,d,ab,cd,apart⟩ := f
  have size : D.card = 3 := by
    by_cases eq : D.card = 3
    · exact eq
    · exact (apart ((conn.2 D (by omega)).preconnected a c)).elim
  let H := DeletionGraph G D
  have ne : H.connectedComponentMk a ≠ H.connectedComponentMk c :=
    fun e => apart (ConnectedComponent.exact e)
  exact ⟨⟨D,size,H.connectedComponentMk a,H.connectedComponentMk c,ne,
    large_component_of_edge smaller conn budget order size no cubic ab,
    large_component_of_edge smaller conn budget order size no cubic cd⟩⟩

#print axioms large_crossing_failure_of_independent_cubics

end Graffiti199Depleted.Catalogue
