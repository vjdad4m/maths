import StarCone

namespace TwinForcing
open SimpleGraph Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A set is a k-fort when every outside vertex that touches it has more
than k neighbors in it. A forcing process cannot enter an uncolored fort. -/
def Fort (k : ℕ) (F : Finset V) : Prop :=
  ∀ z ∉ F, (∃ w ∈ F, G.Adj z w) → k < (F.filter (G.Adj z)).card

/-- A block of vertices with identical open neighborhoods. -/
def TwinBlock (F : Finset V) : Prop :=
  ∀ ⦃w u z : V⦄, w ∈ F → u ∈ F → G.Adj z w → G.Adj z u

theorem fort_disjoint_step {k : ℕ} {F S : Finset V} (hF : Fort G k F)
    (hS : Disjoint F S) : Disjoint F (StarCone.step G k S) := by
  rw [Finset.disjoint_left] at hS ⊢
  intro w hw hit
  rw [StarCone.step,mem_union] at hit
  rcases hit with old | new
  · exact hS hw old
  rcases (mem_filter.mp new).2 with ⟨_,z,hz,ez,num⟩
  have sub : F.filter (G.Adj z) ⊆ G.neighborFinset z \ S := by
    intro u hu
    have m := mem_filter.mp hu
    exact mem_sdiff.mpr ⟨(G.mem_neighborFinset z u).mpr m.2,hS m.1⟩
  exact (not_le_of_gt (hF z (fun hz' => hS hz' hz) ⟨w,hw,ez⟩))
    ((card_le_card sub).trans num)

theorem fort_disjoint_iterate {k : ℕ} {F S : Finset V} (hF : Fort G k F)
    (hS : Disjoint F S) (j : ℕ) : Disjoint F ((StarCone.step G k)^[j] S) := by
  induction j with
  | zero => exact hS
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact fort_disjoint_step G hF ih

omit [Fintype V] [DecidableEq V] in
theorem twin_subset_is_fort {k : ℕ} {B F : Finset V} (twin : TwinBlock G B)
    (sub : F ⊆ B) (large : k < F.card) : Fort G k F := by
  rintro z _ ⟨w,hw,adj⟩
  have equal : F.filter (G.Adj z) = F := by
    apply filter_eq_self.mpr
    intro u hu
    exact twin (sub hw) (sub hu) adj
  rwa [equal]

theorem twin_seed_quota {k : ℕ} {B S : Finset V} (twin : TwinBlock G B)
    (full : StarCone.full G k S) : B.card - k ≤ (B ∩ S).card := by
  by_contra! small
  let F := B \ S
  have sum := card_sdiff_add_card_inter B S
  have big : k < F.card := by dsimp [F]; omega
  have miss : Disjoint F S := by
    rw [Finset.disjoint_left]
    exact fun _ hw => (mem_sdiff.mp hw).2
  have dis := fort_disjoint_iterate G (twin_subset_is_fort G twin sdiff_subset big)
    miss (Fintype.card V)
  change (StarCone.step G k)^[Fintype.card V] S = univ at full
  rw [full,Finset.disjoint_left] at dis
  obtain ⟨w,hw⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
  exact dis hw (mem_univ _)

/-- Quotas for pairwise disjoint twin blocks sum to a lower bound. -/
theorem sum_twin_quota {ι : Type*} {k : ℕ} (is : Finset ι) (B : ι → Finset V)
    (twins : ∀ i ∈ is, TwinBlock G (B i)) (disj : is.toSet.PairwiseDisjoint B) :
    ∑ i ∈ is, ((B i).card - k) ≤ StarCone.forcing G k := by
  let sizes := {r : ℕ | ∃ S : Finset V, S.card = r ∧ StarCone.full G k S ∧ True}
  have fixed : StarCone.step G k univ = univ := by simp [StarCone.step]
  have all : StarCone.full G k univ := by
    unfold StarCone.full
    exact (Function.iterate_fixed fixed (Fintype.card V))
  change _ ≤ sInf sizes
  obtain ⟨S,hs,full,_⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨_,univ,rfl,all,trivial⟩)
  have disj' : is.toSet.PairwiseDisjoint (fun i => B i ∩ S) := by
    intro i hi j hj ne
    exact (disj hi hj ne).mono inter_subset_left inter_subset_left
  calc
    (∑ i ∈ is, ((B i).card - k)) ≤ ∑ i ∈ is, (B i ∩ S).card :=
      sum_le_sum (fun i hi => twin_seed_quota G (twins i hi) full)
    _ = (is.biUnion (fun i => B i ∩ S)).card := (card_biUnion disj').symm
    _ ≤ sInf sizes := by
      rw [← hs]
      exact card_le_card (fun _ hx => (mem_inter.mp ((mem_biUnion.mp hx).choose_spec.2)).2)

/-- In a chain built from n disjoint equal-size page blocks, the quotas
depend only on the page count, not on the edges linking the hubs. -/
theorem uniform_twin_quota {n m k : ℕ} (B : Fin n → Finset V)
    (twins : ∀ i, TwinBlock G (B i)) (sizes : ∀ i, (B i).card = m)
    (disj : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    n * (m-k) ≤ StarCone.forcing G k := by
  have pair : (univ : Finset (Fin n)).toSet.PairwiseDisjoint B := by
    intro i _ j _ ne
    exact disj i j ne
  have h := sum_twin_quota (k := k) G univ B (fun i _ => twins i) pair
  simpa [sizes] using h

#print axioms fort_disjoint_iterate
#print axioms twin_seed_quota
#print axioms sum_twin_quota
#print axioms uniform_twin_quota
end TwinForcing
