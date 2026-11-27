import P8HeawoodLift133
import HexFlattened133

namespace Graffiti133Eighth
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133P8Heawood Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem connected_min_three_heawood_or_P8 (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (hm : ∀ x, 3 ≤ localIndependence G x) :
    (∃ f : Fin 8 → V, InducedPath G f) ∨ ∃ M : Model G Heawood, Function.Surjective M.f := by
  classical
  by_cases h8 : ∃ f : Fin 8 → V, InducedPath G f
  · exact Or.inl h8
  letI := hc.nonempty
  obtain ⟨k,hk,f,hf⟩ := no_four_five_path_of_min_local G h4 h5 3 (by decide) hm
  obtain ⟨g,hg⟩ := trim_path (by omega : 7 ≤ k) hf
  obtain ⟨A⟩ := anchor_of_path7 hg (hm _) h4 h5 h8
  obtain ⟨M⟩ := A.model.extends_to_heawood hm h4 h5 h8
  apply Or.inr
  refine ⟨M, M.covers_if_closed hc 0 ?_⟩
  intro v h i
  have g := (M.extend v h (M.contacts_true v)).good h4 h5 h8
  have e := heawood_no_contacts (M.contacts v) g i
  exact (M.contacts_false v i).mp e

private theorem local_le_three_of_heawood (M : Model G Heawood)
    (cover : Function.Surjective M.f) (v : V) :
    localIndependence G v ≤ 3 := by
  classical
  let L := Equiv.ofBijective M.f ⟨M.inj,cover⟩
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  have hx := (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1
  have hand (w : V) (hw : w ∈ A) :
      L.symm w ∈ Finset.univ.filter (Heawood (L.symm v)) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(M.adj ..).mpr ?_⟩
    change G.Adj (L (L.symm v)) (L (L.symm w))
    simpa using hx w hw
  have cert : ∀ i : Fin 14, (Finset.univ.filter (Heawood i)).card ≤ 3 := by decide
  rw [← eq]
  exact (Finset.card_le_card_of_injOn L.symm hand L.symm.injective.injOn).trans (cert _)

/-- Restricting to an adjacency-closed vertex set preserves every original
maximum independent neighborhood set at surviving centers. -/
private theorem local_le_of_closed (s : Set V) [Fintype s]
    (closed : ∀ x ∈ s, ∀ y, G.Adj x y → y ∈ s) (x : s) :
    localIndependence G x ≤ localIndependence (G.induce s) x := by
  classical
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let embed : A ↪ s := ⟨fun y => ⟨y.val,closed x x.property y.val (hN _ y.property)⟩,
    fun _ _ e => Subtype.ext (congrArg (fun z : s => z.val) e)⟩
  let B := A.attach.map embed
  have hb : B ∈ localIndependentSets (G.induce s) x := by
    apply Graffiti133Pentagon.PentagonFrame.memLocalSet.mpr
    constructor
    · intro w hw
      obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hw
      exact hN a.val a.property
    · intro w hw z hz
      obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨b,_,rfl⟩ := Finset.mem_map.mp hz
      exact hI a.val a.property b.val b.property
  have c := Finset.le_sup (f:=Finset.card) hb
  have Size : B.card = A.card := by simp [B]
  change B.card ≤ localIndependence (G.induce s) x at c
  exact eq ▸ Size ▸ c

private theorem min_three_or_pointwise_three (G : SimpleGraph V)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (hm : ∀ x, 3≤localIndependence G x)
    (no : ¬∃ f : Fin 8 → V, InducedPath G f) :
    ∀ x, localIndependence G x ≤ 3 := by
  classical
  intro x
  let c := G.connectedComponentMk x
  let s := c.supp
  let x' : s := ⟨x,by rfl⟩
  let H := G.induce s
  have closed (x : V) (hx : x∈s) (y : V) (e : G.Adj x y) : y∈s :=
    (c.mem_supp_congr_adj e).mp hx
  have conn : H.Connected := c.connected_induce_supp
  have four : FourCycleFree H := by
    intro a b w z ne e1 e2 e3 e4
    exact Subtype.ext (h4 a.val b.val w.val z.val (fun h => ne (Subtype.ext h)) e1 e2 e3 e4)
  have five : NoSimpleFive133 H := by
    intro a b c d e nd ab bc cd de ea
    exact h5 a.val b.val c.val d.val e.val
      (by simpa using nd.map Subtype.val_injective) ab bc cd de ea
  have minimum (v : s) : 3 ≤ localIndependence H v :=
    (hm v.val).trans (local_le_of_closed s closed v)
  rcases connected_min_three_heawood_or_P8 H conn four five minimum with ⟨f,hf⟩ | ⟨M,cover⟩
  · exact (no ⟨Subtype.val ∘ f,Subtype.val_injective.comp hf.1,hf.2⟩).elim
  · exact (local_le_of_closed s closed x').trans (local_le_three_of_heawood M cover x')

/-- If ordinary 4- and 5-cycles are forbidden, exact average local
independence ≥4 forces an induced P8. Triangles and six-cycles are allowed. -/
theorem P8_of_local_mean_four_without_five (G : SimpleGraph V) [Nonempty V]
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (hmean : 4 ≤ averageLocal G) : ∃ f : Fin 8 → V, InducedPath G f := by
  classical
  apply lift_local_density_path 8 2 4 (by decide) (by decide) G h4
    (nat_density_of_le_average G 4 hmean)
  intro W _ _ J e adj hJ hm dens
  have five : NoSimpleFive133 J := by
    intro a b c d f nd ea eb ec ed ef
    exact h5 _ _ _ _ _ (by simpa using nd.map e.injective)
      ((adj _ _).mp ea) ((adj _ _).mp eb) ((adj _ _).mp ec) ((adj _ _).mp ed) ((adj _ _).mp ef)
  apply Classical.byContradiction
  intro no
  have b := min_three_or_pointwise_three J hJ five hm no
  have bd : (∑ v, localIndependence J v) ≤ 3*Fintype.card W := by
    calc
      (∑ v, localIndependence J v) ≤ ∑ _ : W, (3 : ℕ) := Finset.sum_le_sum (fun _ _ => b _)
      _ = 3*Fintype.card W := by simp [Nat.mul_comm]
  have pos : 0 < Fintype.card W := Fintype.card_pos
  omega

#print axioms connected_min_three_heawood_or_P8
#print axioms P8_of_local_mean_four_without_five
end Graffiti133Eighth
