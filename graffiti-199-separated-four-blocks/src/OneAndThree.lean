import OrderFifteen

open private join_four_regions from OwnershipSplice

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [DecidableEq V]
variable (F : FourBlockPacking G)

private theorem opposite_type (i : Fin 4) : ∃ j : Fin 4, singletonHigh j = true ∧
    singletonLoose j ≠ singletonLoose i := by
  revert i
  decide

/-- The uneven split has a splice even when the admissible entries of
the two pairs belong to only one singleton. -/
theorem FourBlockPacking.traceable_of_three_and_one_losses
    (H : FourBlockSeparation F) (noSix : NoIndependentSix G)
    (three : (F.lost F.depleted).card = 3) (one : (F.lost F.terminal).card = 1) :
    Catalogue.Traceable G := by
  classical
  let A := pairGoodEntries (F.lost F.depleted)
  have aCount : A.card = 2 := pairGoodEntries_card_of_three _ (fun _ h => (F.mem_lost.mp h).1) three
  obtain ⟨a,b,ab,abA⟩ := Finset.card_eq_two.mp aCount
  have aGood : a ∈ A := by simp [abA]
  have bGood : b ∈ A := by simp [abA]
  obtain ⟨z,zLost,zBad⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (show A.card < (F.lost F.depleted).card by omega)
  obtain ⟨w,wLost⟩ := Finset.card_pos.mp (show 0 < (F.lost F.terminal).card by omega)
  have wGood : w ∈ pairGoodEntries (F.lost F.terminal) :=
    (pairGoodEntries_of_single_loss _ (fun _ h => (F.mem_lost.mp h).1) one).symm ▸ wLost
  by_cases mixed : ∃ i ∈ A,
      (F.depleted.f i ∈ singletonPorts F.first ∧ F.terminal.f w ∈ singletonPorts F.second) ∨
      (F.depleted.f i ∈ singletonPorts F.second ∧ F.terminal.f w ∈ singletonPorts F.first)
  · obtain ⟨i,good,owners⟩ := mixed
    exact F.traceable_of_distinct_entry_owners H noSix good wGood owners
  have owned (i : O) (hi : i ∈ A) : F.depleted.f i ∈
      singletonPorts F.first ∪ singletonPorts F.second :=
    (F.mem_lost.mp (pairGoodEntries_subset _ hi)).2
  have aHigh : F.depleted.f a ∈ pairPorts F.depleted :=
    ⟨a,(F.mem_lost.mp (pairGoodEntries_subset _ aGood)).1,rfl⟩
  have bHigh : F.depleted.f b ∈ pairPorts F.depleted :=
    ⟨b,(F.mem_lost.mp (pairGoodEntries_subset _ bGood)).1,rfl⟩
  have zHigh : F.depleted.f z ∈ pairPorts F.depleted :=
    ⟨z,(F.mem_lost.mp zLost).1,rfl⟩
  have wHigh : F.terminal.f w ∈ pairPorts F.terminal :=
    ⟨w,(F.mem_lost.mp wLost).1,rfl⟩
  have away {v : V} (hi : v ∈ pairPorts F.depleted) : v ≠ F.terminal.f w :=
    fun eq => Set.disjoint_left.mp H.pairs (eq ▸ hi) wHigh
  have solve (S T : PrivateSingleton G)
      (sameOwner : ∀ i ∈ A, F.depleted.f i ∈ singletonPorts S)
      (wS : F.terminal.f w ∈ singletonPorts S)
      (zOwners : F.depleted.f z ∈ singletonPorts S ∨ F.depleted.f z ∈ singletonPorts T)
      (ts : Disjoint (labelRegion T.f) (labelRegion S.f))
      (sP : Disjoint (labelRegion S.f) (F.retained F.depleted))
      (sQ : Disjoint (labelRegion S.f) (F.retained F.terminal))
      (tP : Disjoint (labelRegion T.f) (F.retained F.depleted))
      (tQ : Disjoint (labelRegion T.f) (F.retained F.terminal))
      (cover : ∀ v, v ∈ labelRegion T.f ∨ v ∈ F.retained F.depleted ∨
        v ∈ labelRegion S.f ∨ v ∈ F.retained F.terminal) : Catalogue.Traceable G := by
    let ports := ((Finset.univ : Finset (Fin 4)).filter fun i => singletonHigh i = true).map S.f
    let E : Finset V := {F.depleted.f a,F.depleted.f b,F.terminal.f w}
    have matchPorts (v : V) : v ∈ ports ↔ v ∈ singletonPorts S := by simp [ports,singletonPorts]
    have count : ports.card = 3 := (Finset.card_map _).trans (by decide)
    have eCount : E.card = 3 := by
      have notMem : F.depleted.f a ∉ ({F.depleted.f b,F.terminal.f w} : Finset V) := by
        simp [F.depleted.f.injective.ne ab,away aHigh]
      change (insert (F.depleted.f a) ({F.depleted.f b,F.terminal.f w} : Finset V)).card = 3
      rw [Finset.card_insert_of_not_mem notMem,Finset.card_pair (away bHigh)]
    have exactPorts : E = ports := by
      apply Finset.eq_of_subset_of_card_le ?_ (by omega)
      intro v hv
      rcases (show v = F.depleted.f a ∨ v = F.depleted.f b ∨ v = F.terminal.f w by
        simpa [E] using hv) with rfl|rfl|rfl
      · exact (matchPorts _).mpr (sameOwner a aGood)
      · exact (matchPorts _).mpr (sameOwner b bGood)
      · exact (matchPorts _).mpr wS
    have zT : F.depleted.f z ∈ singletonPorts T := by
      apply zOwners.resolve_left
      intro h
      have m := exactPorts.symm ▸ (matchPorts _).mpr h
      rcases (show F.depleted.f z = F.depleted.f a ∨ F.depleted.f z = F.depleted.f b ∨
          F.depleted.f z = F.terminal.f w by simpa [E] using m) with eq|eq|eq
      · exact zBad (F.depleted.f.injective eq ▸ aGood)
      · exact zBad (F.depleted.f.injective eq ▸ bGood)
      · exact away zHigh eq
    obtain ⟨iw,hw,iwEq⟩ := wS
    obtain ⟨ix,hx,diff⟩ := opposite_type iw
    have xE : S.f ix ∈ E := exactPorts.symm ▸ (matchPorts _).mpr ⟨ix,hx,rfl⟩
    have xW : S.f ix ≠ F.terminal.f w :=
      fun e => diff (congrArg singletonLoose (S.f.injective (e.trans iwEq.symm)))
    obtain ⟨i,ig,iEq⟩ : ∃ i ∈ A, S.f ix = F.depleted.f i := by
      rcases ((show S.f ix = F.depleted.f a ∨ S.f ix = F.depleted.f b ∨
        S.f ix = F.terminal.f w by simpa [E] using xE)) with ea|eb|e
      · exact ⟨a,aGood,ea⟩
      · exact ⟨b,bGood,eb⟩
      · exact (xW e).elim
    obtain ⟨iz,hz,izEq⟩ := zT
    obtain ⟨t,tFirst⟩ := singleton_start_at_high T.f T.edges hz
    obtain ⟨p,pEntry,j,hj,kj,pLast⟩ := F.path_at_good_entry F.depleted ig
    obtain ⟨s,sFirst,sLast⟩ := singleton_between_types S.f S.edges hx hw diff
    obtain ⟨q,qEntry,_⟩ := F.path_at_good_entry F.terminal wGood
    have zj := nonentry_sees_retained _ (F.mem_lost.mp zLost).1 zLost zBad hj kj
    have zEdge : G.Adj (F.depleted.f z) (F.depleted.f j) := by
      simp only [terminalHas,Bool.or_eq_true,List.contains_iff_mem] at zj
      exact zj.elim (F.depleted.edges _ _) (fun h => (F.depleted.edges _ _ h).symm)
    have e₁ : G.Adj t.rev.last p.rev.first := by simpa [tFirst,izEq,pLast] using zEdge
    have e₂ : G.Adj p.rev.last s.first := by simpa [sFirst,iEq] using pEntry.symm
    have e₃ : G.Adj s.last q.first := by simpa [sLast,iwEq] using qEntry
    exact Catalogue.traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp
      (join_four_regions t.rev p.rev s q tP ts tQ sP.symm H.retained_pairs sQ cover e₁ e₂ e₃))
  rcases (F.mem_lost.mp wLost).2 with fs|ft
  · apply solve F.first F.second
      (fun i h => (owned i h).resolve_right (fun other => mixed ⟨i,h,Or.inr ⟨other,fs⟩⟩))
      fs (F.mem_lost.mp zLost).2 (FourBlockSeparation.singleton_regions F H).symm
      H.first_depleted (FourBlockSeparation.first_terminal F)
      H.second_depleted (FourBlockSeparation.second_terminal F)
    intro v
    rcases F.retained_cover v with a|b|c|d
    · exact Or.inr (Or.inr (Or.inl a))
    · exact Or.inl b
    · exact Or.inr (Or.inl c)
    · exact Or.inr (Or.inr (Or.inr d))
  · apply solve F.second F.first
      (fun i h => (owned i h).resolve_left (fun other => mixed ⟨i,h,Or.inl ⟨other,ft⟩⟩))
      ft (Or.symm (F.mem_lost.mp zLost).2) H.singleton_regions
      H.second_depleted (FourBlockSeparation.second_terminal F)
      H.first_depleted (FourBlockSeparation.first_terminal F)
    intro v
    rcases F.retained_cover v with a|b|c|d
    · exact Or.inl a
    · exact Or.inr (Or.inr (Or.inl b))
    · exact Or.inr (Or.inl c)
    · exact Or.inr (Or.inr (Or.inr d))

namespace Catalogue

/-- Both exact orders of the separated two-pair layout now follow
from the counting and the catalogue tree budget. -/
theorem traceable_at_fifteen_or_sixteen_of_separated_four_blocks
    (H : FourBlockSeparation F) (noSix : NoIndependentSix G)
    (conn : vertexConnectivity G = 3) (budget : treeNumber G ≤ 5)
    (order : Fintype.card V = 15 ∨ Fintype.card V = 16) : Traceable G := by
  rcases order with fifteen|sixteen
  · exact traceable_at_fifteen_of_separated_four_blocks F H noSix conn budget fifteen
  have balance := F.order_add_pair_losses H
  by_cases a4 : (F.lost F.depleted).card = 4
  · exact traceable_of_depleted_pair_of_tree_budget F conn budget (F.highs_owned_of_four_losses _ a4) (by omega)
  by_cases b4 : (F.lost F.terminal).card = 4
  · exact traceable_of_depleted_pair_of_tree_budget (F.swapPairs H) conn budget
      (F.highs_owned_of_four_losses _ b4) (by omega)
  have cases' :
      ((F.lost F.depleted).card = 1 ∧ (F.lost F.terminal).card = 3) ∨
      ((F.lost F.depleted).card = 3 ∧ (F.lost F.terminal).card = 1) ∨
      ((F.lost F.depleted).card = 2 ∧ (F.lost F.terminal).card = 2) := by omega
  rcases cases' with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
  · exact (F.swapPairs H).traceable_of_three_and_one_losses (F.swapPairs_separation H) noSix b a
  · exact F.traceable_of_three_and_one_losses H noSix a b
  · exact F.traceable_of_two_or_three_losses_each H noSix (by omega) (by omega) (by omega) (by omega)

#print axioms FourBlockPacking.traceable_of_three_and_one_losses
#print axioms traceable_at_fifteen_or_sixteen_of_separated_four_blocks

end Catalogue
end Graffiti199Depleted
