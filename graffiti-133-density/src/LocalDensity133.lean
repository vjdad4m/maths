import Partial133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Finset
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

private theorem memLocal {G : SimpleGraph V} {v : V} {A : Finset V} :
    A ∈ localIndependentSets G v ↔ (∀ x ∈ A, G.Adj v x) ∧
      (∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) := by
  classical
  simp only [localIndependentSets, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_iff, Finset.mem_univ, true_and]

private theorem maxLocal (G : SimpleGraph V) (v : V) :
    ∃ A ∈ localIndependentSets G v, A.card = localIndependence G v := by
  classical
  obtain ⟨A,hA,hM⟩ := Finset.exists_max_image (localIndependentSets G v) Finset.card
    ⟨∅, memLocal.mpr (by simp)⟩
  exact ⟨A,hA,le_antisymm (Finset.le_sup (f := Finset.card) hA)
    (Finset.sup_le_iff.mpr hM)⟩

private theorem liftLocal (G : SimpleGraph V) (v : V) (x : {y : V | y ≠ v})
    (A : Finset V) (hA : A ∈ localIndependentSets G x.val) (hv : v ∉ A) :
    A.card ≤ localIndependence (G.induce {y | y ≠ v}) x := by
  classical
  let K := A.subtype fun y => y ≠ v
  have hCard : K.card = A.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_eq_self.mpr (fun w hw e => hv (e ▸ hw))
  have hl : K ∈ localIndependentSets (G.induce {y | y ≠ v}) x := by
    obtain ⟨hn,hi⟩ := memLocal.mp hA
    apply memLocal.mpr
    exact ⟨fun y hy => hn _ (Finset.mem_subtype.mp hy),
      fun a ha b hb => hi _ (Finset.mem_subtype.mp ha) _ (Finset.mem_subtype.mp hb)⟩
  rw [← hCard]
  exact Finset.le_sup (f:=Finset.card) hl

private noncomputable def lone (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x => G.Adj v x ∧ ¬ ∃ y, G.Adj v y ∧ G.Adj x y

private theorem lone_le_local (G : SimpleGraph V) (v : V) :
    (lone G v).card ≤ localIndependence G v := by
  classical
  have spec {x : V} (hx : x ∈ lone G v) := (Finset.mem_filter.mp hx).2
  exact Finset.le_sup (f:=Finset.card) (memLocal.mpr
    ⟨fun x hx => (spec hx).1,fun x hx y hy e => (spec hx).2 ⟨y,(spec hy).1,e⟩⟩)

private noncomputable def loneCost (G : SimpleGraph V) (v x : V) : ℕ := by
  classical
  exact if x ∈ lone G v then 1 else 0

private theorem one_loss (G : SimpleGraph V) (h4 : FourCycleFree G)
    (v : V) (x : {y : V | y ≠ v}) :
    localIndependence G x.val ≤ localIndependence (G.induce {y | y ≠ v}) x +
      loneCost G v x.val := by
  classical
  obtain ⟨A,hA,hc⟩ := maxLocal G x.val
  by_cases hv : v ∈ A
  · obtain ⟨hn,hi⟩ := memLocal.mp hA
    by_cases ht : x.val ∈ lone G v
    · have ha' : A.erase v ∈ localIndependentSets G x.val := by
        apply memLocal.mpr
        exact ⟨fun y hy => hn _ (Finset.mem_of_mem_erase hy),
          fun a ha b hb => hi _ (Finset.mem_of_mem_erase ha) _ (Finset.mem_of_mem_erase hb)⟩
      have hl := liftLocal G v x (A.erase v) ha' (Finset.not_mem_erase _ _)
      rw [Finset.card_erase_of_mem hv,hc] at hl
      simp only [loneCost,if_pos ht]
      omega
    · have et : ∃ z, G.Adj v z ∧ G.Adj x.val z := by
        apply Classical.byContradiction
        intro no
        exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hn _ hv).symm,no⟩)
      obtain ⟨z,hvz,hxz⟩ := et
      have hz : z ∉ A := fun h => hi v hv z h hvz
      let B := insert z (A.erase v)
      have hB : B ∈ localIndependentSets G x.val := by
        dsimp only [B]
        have nochord (y : V) (hy : y ∈ A.erase v) : ¬G.Adj z y := by
          intro e
          have eq := h4 x.val z y v hxz.ne (hn _ (Finset.mem_of_mem_erase hy))
            e (hn _ hv) hvz.symm
          exact (Finset.ne_of_mem_erase hy) eq
        apply memLocal.mpr
        refine ⟨?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hxz
          · exact hn _ (Finset.mem_of_mem_erase hy)
        · intro a ha b hb
          rcases Finset.mem_insert.mp ha with ea | hax
          · rcases Finset.mem_insert.mp hb with eb | hbx
            · rw [ea,eb]
              exact G.loopless _
            · rw [ea]
              exact nochord _ hbx
          · rcases Finset.mem_insert.mp hb with eb | hbx
            · rw [eb]
              exact fun e => nochord _ hax e.symm
            · exact hi _ (Finset.mem_of_mem_erase hax) _ (Finset.mem_of_mem_erase hbx)
      have hnv : v ∉ B := by simp [B,hvz.ne]
      have hl := liftLocal G v x B hB hnv
      unfold B at hl
      rw [Finset.card_insert_of_not_mem (fun h => hz (Finset.mem_of_mem_erase h)),
        Finset.card_erase_add_one hv,hc] at hl
      simpa only [loneCost,if_neg ht,Nat.add_zero] using hl
  · rw [← hc]
    exact (liftLocal G v x A hA hv).trans (Nat.le_add_right _ _)

/-- In a four-cycle-free graph, deleting vertex v loses at most twice
its local independence number from the total local independence potential.
More precisely, the residual loss is bounded by the count of neighbors
not lying with v in a triangle. -/
theorem local_sum_delete_bound (G : SimpleGraph V) (h4 : FourCycleFree G) (v : V) :
    (∑ y, localIndependence G y) ≤
      (∑ y : {y : V | y ≠ v}, localIndependence (G.induce {y | y ≠ v}) y) +
      2 * localIndependence G v := by
  classical
  let W := {y : V | y ≠ v}
  let H := G.induce W
  have hh (x : W) := one_loss G h4 v x
  have rhs := Finset.sum_le_sum (s := (Finset.univ : Finset W)) (fun x _ => hh x)
  rw [Finset.sum_add_distrib] at rhs
  have original : (∑ x : W, localIndependence G x.val) + localIndependence G v =
      ∑ x, localIndependence G x := by
    have h := (Finset.sum_erase_add (s := (Finset.univ : Finset V))
      (f := fun x => localIndependence G x) (Finset.mem_univ v))
    have hh := Finset.sum_subtype ((Finset.univ : Finset V).erase v) (p := fun x => x ≠ v) (F := inferInstanceAs (Fintype W)) (by simp) (localIndependence G)
    exact (congrArg (fun n => n + localIndependence G v) hh.symm).trans h
  have lonelyCard : (∑ x : W, loneCost G v x.val) = (lone G v).card := by
    have sub : (lone G v).filter (fun x => x ≠ v) = lone G v := by
      apply Finset.filter_eq_self.mpr
      intro x hx e
      subst x
      exact G.loopless v (Finset.mem_filter.mp hx).2.1
    have hh := Finset.sum_subtype ((Finset.univ : Finset V).erase v) (p := fun x => x ≠ v) (F := inferInstanceAs (Fintype W)) (by simp) (loneCost G v)
    refine hh.symm.trans ?_
    have hF : ((Finset.univ : Finset V).erase v).filter (fun x => x ∈ lone G v) = lone G v := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true]
      exact ⟨And.right,fun hx => ⟨fun e => by subst x; exact G.loopless v (Finset.mem_filter.mp hx).2.1,hx⟩⟩
    simp [loneCost,Finset.sum_ite,hF,Finset.erase_eq_of_not_mem (show v ∉ lone G v by
      intro hv
      exact G.loopless v (Finset.mem_filter.mp hv).2.1)]
  change (∑ x : W, localIndependence G x.val) ≤ (∑ x : W, localIndependence H x) +
    (∑ x : W, loneCost G v x.val) at rhs
  rw [lonelyCard] at rhs
  change (∑ y, localIndependence G y) ≤ (∑ y : W, localIndependence H y) + _
  rw [← original]
  have := lone_le_local G v
  omega

#print axioms local_sum_delete_bound

/-- A longest induced-path lower bound can be transferred from minimum
local independence to a local mean assumption, with factor two in the
threshold. The induction preserves any larger integral density threshold. -/
theorem lift_local_density_path (k d t : ℕ) (hd : 1 ≤ d) (ht : 2*d ≤ t)
    (G : SimpleGraph V) [Nonempty V] (h4 : FourCycleFree G)
    (hD : t*Fintype.card V ≤ (∑ x, localIndependence G x))
    (witness : ∀ (W : Type u) [Fintype W] [Nonempty W] (J : SimpleGraph W) (e : W ↪ V),
      (∀ a b, J.Adj a b ↔ G.Adj (e a) (e b)) → FourCycleFree J →
      (∀ x, d+1 ≤ localIndependence J x) →
      t*Fintype.card W ≤ (∑ x, localIndependence J x) →
      ∃ f : Fin k → W, InducedPath J f) :
    ∃ f : Fin k → V, InducedPath G f := by
  classical
  let Claim (n : ℕ) := ∀ (W : Type u) [Fintype W] [DecidableEq W] [Nonempty W],
    Fintype.card W = n → ∀ (J : SimpleGraph W) (e : W ↪ V),
    (∀ a b, J.Adj a b ↔ G.Adj (e a) (e b)) → FourCycleFree J →
    t*Fintype.card W ≤ (∑ x, localIndependence J x) →
    ∃ f : Fin k → W, InducedPath J f
  have aux (n : ℕ) : Claim n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ hn G e hEmbed h4 dens
      by_cases hh : ∀ v, d+1 ≤ localIndependence G v
      · exact witness W G e hEmbed h4 hh dens
      push_neg at hh
      obtain ⟨v,hv⟩ := hh
      let S : Set W := {x | x ≠ v}
      let H := G.induce S
      have hpos : 0 < Fintype.card W := Fintype.card_pos
      have hS : Fintype.card S + 1 = Fintype.card W := by
        have hs : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card {x : W // ¬ x = v} = _
          rw [Fintype.card_subtype_compl]
          rw [show Fintype.card {x : W // x = v} = 1 from Fintype.card_unique]
        omega
      have hFree : FourCycleFree H := by
        intro a b x y hab hax hbx hay hby
        apply Subtype.ext
        exact h4 _ _ _ _ (fun h => hab (Subtype.ext h)) hax hbx hay hby
      have posSum := (Nat.mul_pos (show 0 < t by omega) hpos).trans_le dens
      have edg : ∃ a b, G.Adj a b := by
        apply Classical.byContradiction
        intro no
        have nn : ∀ x, localIndependence G x = 0 := by
          intro x
          obtain ⟨A,hA,hAC⟩ := maxLocal G x
          rw [← hAC,Finset.card_eq_zero]
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          obtain ⟨a,ha⟩ := hne
          exact no ⟨x,a,(memLocal.mp hA).1 a ha⟩
        simp [nn] at posSum
      obtain ⟨a,b,hab⟩ := edg
      haveI : Nonempty S := by
        by_cases eq : a = v
        · exact ⟨⟨b,(eq ▸ hab.ne).symm⟩⟩
        · exact ⟨⟨a,eq⟩⟩
      have hloss := local_sum_delete_bound G h4 v
      have hD' : t*Fintype.card S ≤ (∑ x, localIndependence H x) := by
        rw [← hS,Nat.mul_add,Nat.mul_one] at dens
        change (∑ x, localIndependence G x) ≤ (∑ x : S, localIndependence H x) +
          2*localIndependence G v at hloss
        omega
      have hsN : Fintype.card S < n := by omega
      obtain ⟨f,hf⟩ := ih _ hsN S rfl H ((Function.Embedding.subtype _).trans e)
        (fun a b => hEmbed a.val b.val) hFree hD'
      exact ⟨fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
  exact aux (Fintype.card V) V rfl G (Function.Embedding.refl V) (fun _ _ => Iff.rfl) h4 hD

/-- Restrict an induced path to a prescribed shorter positive order. -/
theorem trim_path {V : Type*} {G : SimpleGraph V} {k m : ℕ} (bound : k ≤ m)
    {f : Fin m → V} (h : InducedPath G f) : ∃ g : Fin k → V, InducedPath G g := by
  refine ⟨f ∘ Fin.castLE bound,h.1.comp (Fin.castLE_injective bound),?_⟩
  intro i j hlt
  exact h.2 (Fin.castLE bound i) (Fin.castLE bound j) hlt

/-- Degree pruning using the average local independence, rather than
ordinary edge density. Triangles and heterogeneous degrees are permitted. -/
theorem no_four_five_path_of_local_density
    (G : SimpleGraph V) [Nonempty V] (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (d : ℕ) (hd : 1 ≤ d)
    (hD : 2*d*Fintype.card V ≤ (∑ x, localIndependence G x)) :
    ∃ f : Fin (2*d+3) → V, InducedPath G f := by
  classical
  apply lift_local_density_path (2*d+3) d (2*d) hd le_rfl G h4 hD
  intro U _ _ J e he h4J hm _
  have h5J : NoSimpleFive133 J := by
    intro a b c d e' hn ea eb ec ed ee
    have hl := hn.map e.injective
    exact h5 _ _ _ _ _ (by simpa using hl) ((he _ _).mp ea)
      ((he _ _).mp eb) ((he _ _).mp ec) ((he _ _).mp ed) ((he _ _).mp ee)
  obtain ⟨k,hk,f,hf⟩ := no_four_five_path_of_min_local J h4J h5J (d+1) (by omega) hm
  exact trim_path (by omega : 2*d+3 ≤ k) hf

#print axioms no_four_five_path_of_local_density

end Graffiti133Revisit
