import NoFiveHexDensity133

namespace Graffiti133NoFive
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
universe u

variable {V : Type u} [Fintype V]

private theorem simplicial_of_local_le_one (G : SimpleGraph V) (v : V)
    (low : localIndependence G v ≤ 1) {a b : V}
    (ha : G.Adj v a) (hb : G.Adj v b) :
    a = b ∨ G.Adj a b := by
  classical
  by_cases ne : a = b
  · exact Or.inl ne
  by_cases e : G.Adj a b
  · exact Or.inr e
  exfalso
  have hs : ({a,b} : Finset V) ∈ localIndependentSets G v := by
    apply Graffiti133Pentagon.PentagonFrame.memLocalSet.mpr
    refine ⟨?_,?_⟩
    · intro x hx
      rcases (by simpa using hx : x=a ∨ x=b) with rfl | rfl
      · exact ha
      · exact hb
    · intro x hx y hy
      rcases (by simpa using hx : x=a ∨ x=b) with hx' | hx' <;>
        rcases (by simpa using hy : y=a ∨ y=b) with hy' | hy' <;> rw [hx',hy']
      · exact G.loopless _
      · exact e
      · exact fun h => e h.symm
      · exact G.loopless _
  have h := (Finset.le_sup (f:=Finset.card) hs).trans low
  simp [ne] at h

/-- Deleting a vertex of local independence at most one preserves
connectivity, provided the deletion is nonempty. -/
theorem connected_delete_low_local (G : SimpleGraph V) (hc : G.Connected)
    (v : V) (low : localIndependence G v ≤ 1) (non : Nonempty {y : V // y ≠ v}) :
    (G.induce {y | y ≠ v}).Connected := by
  let S : Set V := {y | y ≠ v}
  let H := G.induce S
  have non' : Nonempty S := non
  apply @SimpleGraph.Connected.mk _ H _ non'
  intro x y
  obtain ⟨p⟩ := hc x.val y.val
  have reduce {a b : V} (q : G.Walk a b) (hb : b ≠ v) (u : S)
      (hu : u.val=a ∨ (a=v ∧ G.Adj u.val v)) : H.Reachable u ⟨b,hb⟩ := by
    induction q generalizing u with
    | nil =>
      rcases hu with eq | ⟨eq,_⟩
      · have he : u = ⟨_,hb⟩ := Subtype.ext eq
        exact he.symm ▸ SimpleGraph.Reachable.refl _
      · exact (hb eq).elim
    | @cons a b c e q ih =>
      by_cases bb : b=v
      · have aa : a ≠ v := by
          intro h
          exact e.ne (h.trans bb.symm)
        rcases hu with h | ⟨h,_⟩
        · exact ih hb u (Or.inr ⟨bb,h.symm ▸ (bb ▸ e)⟩)
        · exact (aa h).elim
      · let t : S := ⟨b,bb⟩
        have step : H.Reachable u t := by
          rcases hu with h | ⟨h,hu⟩
          · have ee : H.Adj u t := by
              change G.Adj u.val b
              exact h.symm ▸ e
            exact ee.reachable
          · have eb : G.Adj v b := h ▸ e
            rcases simplicial_of_local_le_one G v low hu.symm eb with near | adj
            · have eq : u = t := Subtype.ext near
              exact eq.symm ▸ SimpleGraph.Reachable.refl _
            · exact (show H.Adj u t from adj).reachable
        exact step.trans (ih hb t (Or.inl rfl))
  exact reduce p y.prop x (Or.inl rfl)

/-- Density pruning at local threshold one preserves both mean at least
three and connectedness. -/
theorem connected_peel_for_P7 (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (hD : 3*Fintype.card V ≤ (∑ v, localIndependence G v))
    (core : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W), J.Connected →
      FourCycleFree J → NoSimpleFive133 J → (∀ v, 2 ≤ localIndependence J v) →
      3*Fintype.card W ≤ (∑ v, localIndependence J v) →
      ∃ f : Fin 7 → W, InducedPath J f) :
    ∃ f : Fin 7 → V, InducedPath G f := by
  classical
  let Claim (n : ℕ) := ∀ (W : Type u) [Fintype W] (J : SimpleGraph W),
    Fintype.card W=n → J.Connected → FourCycleFree J → NoSimpleFive133 J →
    3*Fintype.card W ≤ (∑ v, localIndependence J v) →
    ∃ f : Fin 7 → W, InducedPath J f
  have aux (n : ℕ) : Claim n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ G hn hC h4 h5 dens
      letI := hC.nonempty
      by_cases hmin : ∀ v, 2 ≤ localIndependence G v
      · exact core W G hC h4 h5 hmin dens
      push_neg at hmin
      obtain ⟨v,hv⟩ := hmin
      let S : Set W := {w | w ≠ v}
      let H := G.induce S
      have hpos : 0 < Fintype.card W := Fintype.card_pos
      have hS : Fintype.card S + 1 = Fintype.card W := by
        have hs : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card {x : W // ¬ x = v} = _
          rw [Fintype.card_subtype_compl]
          rw [show Fintype.card {x : W // x = v} = 1 from Fintype.card_unique]
        omega
      have h4' : FourCycleFree H := by
        intro a b x y hab hax hbx hay hby
        apply Subtype.ext
        exact h4 _ _ _ _ (fun h => hab (Subtype.ext h)) hax hbx hay hby
      have h5' : NoSimpleFive133 H := by
        intro a b c d e nd ha hb hC hd he
        have nd' := nd.map (Subtype.val_injective (p:=fun x : W => x ≠ v))
        exact h5 _ _ _ _ _ (by simpa using nd') ha hb hC hd he
      have non : Nonempty S := by
        have pos : 0 < (∑ v, localIndependence G v) := by omega
        obtain ⟨a,b,ab⟩ : ∃ a b, G.Adj a b := by
          apply Classical.byContradiction
          intro no
          have eq : ∀ x, localIndependence G x = 0 := by
            intro x
            obtain ⟨A,hA,hc⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
            rw [← hc,Finset.card_eq_zero]
            apply Finset.not_nonempty_iff_eq_empty.mp
            rintro ⟨a,ha⟩
            exact no ⟨x,a,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 a ha⟩
          simp [eq] at pos
        by_cases ha : a=v
        · exact ⟨⟨b,(ha ▸ ab.ne).symm⟩⟩
        · exact ⟨⟨a,ha⟩⟩
      have hConn : H.Connected := connected_delete_low_local G hC v (by omega) non
      have loss := local_sum_delete_bound G h4 v
      have dH : 3*Fintype.card S ≤ (∑ w, localIndependence H w) := by
        rw [← hS,Nat.mul_add,Nat.mul_one] at dens
        change (∑ w, localIndependence G w) ≤ (∑ w : S, localIndependence H w) +
          2*localIndependence G v at loss
        omega
      obtain ⟨f,hf⟩ := ih _ (by omega : Fintype.card S < n) S H rfl hConn h4' h5' dH
      exact ⟨fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
  exact aux (Fintype.card V) V G rfl hc h4 h5 hD

#print axioms connected_delete_low_local
#print axioms connected_peel_for_P7

end Graffiti133NoFive
