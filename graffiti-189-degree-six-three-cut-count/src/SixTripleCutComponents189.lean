import SixTripleCutFourShore189
import AdjacentCutFiveActual189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

abbrev Removed (G : SimpleGraph V) (S : Finset V) :=
  G.induce ((↑S : Set V)ᶜ)

noncomputable def shoreSet {S : Finset V} (C : (Removed G S).ConnectedComponent) : Finset V := by
  classical
  exact univ.filter fun x => ∃ h : x∉S, (Removed G S).connectedComponentMk ⟨x,h⟩=C

theorem mem_shoreSet {S : Finset V} {C : (Removed G S).ConnectedComponent} {x : V} :
    x∈shoreSet C ↔ ∃ h : x∉S, (Removed G S).connectedComponentMk ⟨x,h⟩=C := by
  classical
  simp [shoreSet]

theorem shoreSet_shore {S : Finset V} (C : (Removed G S).ConnectedComponent) :
    Shore G S (shoreSet C) := by
  classical
  refine ⟨?_,?_,?_⟩
  · obtain ⟨x,hx⟩ := C.exists_rep
    exact ⟨x.val,mem_shoreSet.mpr ⟨x.property,hx⟩⟩
  · exact disjoint_left.mpr (fun _ h => (mem_shoreSet.mp h).choose)
  · intro x xc y xy
    by_cases ys : y∈S
    · exact Or.inr ys
    obtain ⟨xs,hx⟩ := mem_shoreSet.mp xc
    have e : (Removed G S).Adj ⟨x,xs⟩ ⟨y,ys⟩ := xy
    exact Or.inl (mem_shoreSet.mpr ⟨ys,(ConnectedComponent.sound e.reachable).symm.trans hx⟩)

theorem shoreSet_disjoint {S : Finset V} {C D : (Removed G S).ConnectedComponent} (ne : C≠D) :
    Disjoint (shoreSet C) (shoreSet D) := by
  apply disjoint_left.mpr
  intro x xc xd
  obtain ⟨_,hc⟩ := mem_shoreSet.mp xc
  obtain ⟨_,hd⟩ := mem_shoreSet.mp xd
  exact ne (hc.symm.trans hd)

theorem shoreSet_connected {S : Finset V} (C : (Removed G S).ConnectedComponent) :
    (G.induce (↑(shoreSet C) : Set V)).Connected := by
  apply CrossSaturation.FiveAdjacent.induced_connected_of_joined _ (shoreSet_shore C).nonempty
  intro x xc y yc
  obtain ⟨hx,e⟩ := mem_shoreSet.mp xc
  obtain ⟨hy,f⟩ := mem_shoreSet.mp yc
  obtain ⟨q⟩ := ConnectedComponent.exact (e.trans f.symm)
  let φ : Removed G S →g G := {toFun := Subtype.val,map_rel' := fun e=>e}
  refine ⟨q.map φ,?_⟩
  intro z hz
  rw [support_map,List.mem_map] at hz
  obtain ⟨w,wm,rfl⟩ := hz
  have r := ConnectedComponent.sound (q.takeUntil w wm).reachable
  exact mem_shoreSet.mpr ⟨w.property,r.symm.trans e⟩

/-- Every actual three-cut has at most three components under the
degree-six #189 hypotheses. -/
theorem three_cut_at_most_three_components (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S : Finset V} (ss : S.card=3) :
    Nat.card (Removed G S).ConnectedComponent≤3 := by
  classical
  by_contra! big
  let C := (Removed G S).ConnectedComponent
  letI : Finite C := Finite.of_surjective (Removed G S).connectedComponentMk
    (fun y => y.exists_rep)
  letI : Fintype C := Fintype.ofFinite C
  have c : 4≤Fintype.card C := by
    change 3<Nat.card C at big
    rw [Nat.card_eq_fintype_card] at big
    omega
  let f : Fin 4 ↪ C := (Fin.castLEEmb c).trans (Fintype.equivFin C).symm.toEmbedding
  let A (i : Fin 4) := shoreSet (f i)
  exact no_four_shores hc cap conn degree ss A
    (fun i=>shoreSet_shore (f i))
    (fun _ _ ne=>shoreSet_disjoint (f.injective.ne ne))

#print axioms shoreSet_connected
#print axioms three_cut_at_most_three_components
end Graffiti189LongestPath.ThresholdSix.ThreeCut
