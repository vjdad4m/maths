import PairedEntries

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
variable (F : FourBlockPacking G)

/-- Two sets of at least two admissible lost entries cannot all be
owned by the same singleton. Its high set has only three vertices. -/
theorem FourBlockPacking.good_entries_distinct_owners (H : FourBlockSeparation F)
    (twoA : 2 ≤ (pairGoodEntries (F.lost F.depleted)).card)
    (twoB : 2 ≤ (pairGoodEntries (F.lost F.terminal)).card) :
    ∃ i ∈ pairGoodEntries (F.lost F.depleted), ∃ j ∈ pairGoodEntries (F.lost F.terminal),
      (F.depleted.f i ∈ singletonPorts F.first ∧ F.terminal.f j ∈ singletonPorts F.second) ∨
      (F.depleted.f i ∈ singletonPorts F.second ∧ F.terminal.f j ∈ singletonPorts F.first) := by
  classical
  by_contra no
  let A := (pairGoodEntries (F.lost F.depleted)).map F.depleted.f
  let B := (pairGoodEntries (F.lost F.terminal)).map F.terminal.f
  have a2 : 2 ≤ A.card := by simpa [A] using twoA
  have b2 : 2 ≤ B.card := by simpa [B] using twoB
  have which (P : FullPair G) {v : V}
      (h : v ∈ (pairGoodEntries (F.lost P)).map P.f) :
      v ∈ pairPorts P ∧ v ∈ singletonPorts F.first ∪ singletonPorts F.second := by
    obtain ⟨i,entry,rfl⟩ := Finset.mem_map.mp h
    obtain ⟨hi,ports⟩ := F.mem_lost.mp (pairGoodEntries_subset _ entry)
    exact ⟨⟨i,hi,rfl⟩,ports⟩
  have conflict {a b : V} (ha : a ∈ A) (hb : b ∈ B)
      (mixed : (a ∈ singletonPorts F.first ∧ b ∈ singletonPorts F.second) ∨
        (a ∈ singletonPorts F.second ∧ b ∈ singletonPorts F.first)) : False := by
    obtain ⟨i,ia,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j,jb,rfl⟩ := Finset.mem_map.mp hb
    exact no ⟨i,ia,j,jb,mixed⟩
  have separate : Disjoint A B := Finset.disjoint_left.mpr fun v ha hb =>
    Set.disjoint_left.mp H.pairs (which _ ha).1 (which _ hb).1
  have impossible (S : PrivateSingleton G)
      (as' : ∀ v ∈ A, v ∈ singletonPorts S) (bs' : ∀ v ∈ B, v ∈ singletonPorts S) : False := by
    let ports := ((Finset.univ : Finset (Fin 4)).filter fun i => singletonHigh i = true).map S.f
    have cap : ports.card = 3 := (Finset.card_map _).trans (by decide)
    have sub : A ∪ B ⊆ ports := by
      intro v hv
      have hv' := (Finset.mem_union.mp hv).elim (as' v) (bs' v)
      obtain ⟨i,hi,eq⟩ := hv'
      exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,eq⟩
    have count := Finset.card_le_card sub
    rw [Finset.card_union_of_disjoint separate,cap] at count
    omega
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  rcases (which _ ha).2 with as'|at'
  · have bs' (v : V) (hv : v ∈ B) : v ∈ singletonPorts F.first :=
      (which _ hv).2.resolve_right (fun t => conflict ha hv (Or.inl ⟨as',t⟩))
    exact impossible F.first (fun v hv => (which _ hv).2.resolve_right
      (fun t => conflict hv hb (Or.inr ⟨t,bs' b hb⟩))) bs'
  · have bt' (v : V) (hv : v ∈ B) : v ∈ singletonPorts F.second :=
      (which _ hv).2.resolve_left (fun s => conflict ha hv (Or.inr ⟨at',s⟩))
    exact impossible F.second (fun v hv => (which _ hv).2.resolve_left
      (fun s => conflict hv hb (Or.inl ⟨s,bt' b hb⟩))) bt'

omit [Fintype V] [DecidableRel G.Adj] in
private theorem join_four_regions {A B C D : Set V} (a : PathOn G A) (b : PathOn G B)
    (c : PathOn G C) (d : PathOn G D)
    (ab : Disjoint A B) (ac : Disjoint A C) (ad : Disjoint A D)
    (bc : Disjoint B C) (bd : Disjoint B D) (cd : Disjoint C D)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ C ∨ v ∈ D)
    (abEdge : G.Adj a.last b.first) (bcEdge : G.Adj b.last c.first)
    (cdEdge : G.Adj c.last d.first) : Nonempty (PathOn G Set.univ) := by
  let abPath := a.join b ab abEdge
  let abcPath := abPath.join c (Set.disjoint_union_left.mpr ⟨ac,bc⟩)
    (by simpa only [abPath,PathOn.join_last] using bcEdge)
  have all : A ∪ B ∪ C ∪ D = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    rcases cover v with ha|hb|hc|hd
    · exact Or.inl (Or.inl (Or.inl ha))
    · exact Or.inl (Or.inl (Or.inr hb))
    · exact Or.inl (Or.inr hc)
    · exact Or.inr hd
  exact ⟨all ▸ abcPath.join d (Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr ⟨ad,bd⟩,cd⟩)
    (by simpa only [abcPath,PathOn.join_last] using cdEdge)⟩

/-- Whenever good lost entries can be owned by opposite singleton
blocks, the four retained paths concatenate. -/
theorem FourBlockPacking.traceable_of_distinct_entry_owners [DecidableEq V]
    (H : FourBlockSeparation F) (noSix : NoIndependentSix G) {i j : O}
    (goodA : i ∈ pairGoodEntries (F.lost F.depleted))
    (goodB : j ∈ pairGoodEntries (F.lost F.terminal))
    (owners : (F.depleted.f i ∈ singletonPorts F.first ∧ F.terminal.f j ∈ singletonPorts F.second) ∨
      (F.depleted.f i ∈ singletonPorts F.second ∧ F.terminal.f j ∈ singletonPorts F.first)) :
    Catalogue.Traceable G := by
  obtain ⟨p,entryP,a,ha,ka,endP⟩ := F.path_at_good_entry F.depleted goodA
  obtain ⟨q,entryQ,b,hb,kb,endQ⟩ := F.path_at_good_entry F.terminal goodB
  have middle : G.Adj p.last q.rev.first := by
    rw [endP,PathOn.rev_first,endQ]
    exact F.retained_highs_adjacent H noSix ha hb ka kb
  have splice (S T : PrivateSingleton G)
      (st : Disjoint (labelRegion S.f) (labelRegion T.f))
      (sP : Disjoint (labelRegion S.f) (F.retained F.depleted))
      (sQ : Disjoint (labelRegion S.f) (F.retained F.terminal))
      (tP : Disjoint (labelRegion T.f) (F.retained F.depleted))
      (tQ : Disjoint (labelRegion T.f) (F.retained F.terminal))
      (cover : ∀ v, v ∈ labelRegion S.f ∨ v ∈ F.retained F.depleted ∨
        v ∈ F.retained F.terminal ∨ v ∈ labelRegion T.f)
      (s : F.depleted.f i ∈ singletonPorts S) (t : F.terminal.f j ∈ singletonPorts T) :
      Catalogue.Traceable G := by
    obtain ⟨is,hs,eqS⟩ := s
    obtain ⟨it,ht,eqT⟩ := t
    obtain ⟨ps,startS⟩ := singleton_start_at_high S.f S.edges hs
    obtain ⟨pt,startT⟩ := singleton_start_at_high T.f T.edges ht
    have left : G.Adj ps.rev.last p.first := by simpa [startS,eqS] using entryP
    have right : G.Adj q.rev.last pt.first := by simpa [startT,eqT] using entryQ.symm
    apply Catalogue.traceable_iff_hamiltonian_walk.mpr
    apply pathOn_univ_iff_hamiltonian_walk.mp
    exact join_four_regions ps.rev p q.rev pt sP sQ st H.retained_pairs tP.symm tQ.symm cover
      left middle right
  rcases owners with ⟨s,t⟩|⟨t,s⟩
  · apply splice F.first F.second H.singleton_regions H.first_depleted
      (FourBlockSeparation.first_terminal F) H.second_depleted (FourBlockSeparation.second_terminal F) _ s t
    intro v
    rcases F.retained_cover v with hs|ht|ha|hb
    · exact Or.inl hs
    · exact Or.inr (Or.inr (Or.inr ht))
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl hb))
  · apply splice F.second F.first (FourBlockSeparation.singleton_regions F H).symm H.second_depleted
      (FourBlockSeparation.second_terminal F) H.first_depleted (FourBlockSeparation.first_terminal F) _ t s
    intro v
    rcases F.retained_cover v with hs|ht|ha|hb
    · exact Or.inr (Or.inr (Or.inr hs))
    · exact Or.inl ht
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl hb))

theorem FourBlockPacking.traceable_of_two_or_three_losses_each [DecidableEq V]
    (H : FourBlockSeparation F) (noSix : NoIndependentSix G)
    (twoA : 2 ≤ (F.lost F.depleted).card) (threeA : (F.lost F.depleted).card ≤ 3)
    (twoB : 2 ≤ (F.lost F.terminal).card) (threeB : (F.lost F.terminal).card ≤ 3) :
    Catalogue.Traceable G := by
  obtain ⟨i,ia,j,jb,owners⟩ := F.good_entries_distinct_owners H
    (pairGoodEntries_two _ (fun _ h => (F.mem_lost.mp h).1) twoA threeA)
    (pairGoodEntries_two _ (fun _ h => (F.mem_lost.mp h).1) twoB threeB)
  exact F.traceable_of_distinct_entry_owners H noSix ia jb owners

private theorem loss_bound (P : FullPair G) : (F.lost P).card ≤ 4 := by
  let high := (Finset.univ : Finset O).filter fun i : O => 2 ≤ i.val
  have count : high.card = 4 := by decide
  have sub : F.lost P ⊆ high := fun _ h =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(F.mem_lost.mp h).1⟩
  exact (Finset.card_le_card sub).trans_eq count

theorem FourBlockPacking.highs_owned_of_four_losses (P : FullPair G) (lost : (F.lost P).card = 4) :
    pairPorts P ⊆ singletonPorts F.first ∪ singletonPorts F.second := by
  let high := (Finset.univ : Finset O).filter fun i : O => 2 ≤ i.val
  have count : high.card = 4 := by decide
  have sub : F.lost P ⊆ high := fun _ h =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(F.mem_lost.mp h).1⟩
  have eq : F.lost P = high := Finset.eq_of_subset_of_card_le sub (by omega)
  rintro _ ⟨i,hi,rfl⟩
  exact (F.mem_lost.mp (eq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)).2

/-- Recover the four-loss ownership conclusion at order fifteen in a
nontraceable two-pair packing with disjoint highs. -/
theorem FourBlockPacking.four_losses_at_fifteen [DecidableEq V]
    (H : FourBlockSeparation F) (noSix : NoIndependentSix G)
    (order : Fintype.card V = 15) (nontraceable : ¬ Catalogue.Traceable G) :
    ((F.lost F.depleted).card = 4 ∧ (F.lost F.terminal).card = 1) ∨
    ((F.lost F.depleted).card = 1 ∧ (F.lost F.terminal).card = 4) := by
  have balance := F.order_add_pair_losses H
  have a4 := loss_bound F F.depleted
  have b4 := loss_bound F F.terminal
  have other : ¬ ((F.lost F.depleted).card ≤ 3 ∧ (F.lost F.terminal).card ≤ 3) := by
    rintro ⟨a,b⟩
    exact nontraceable (F.traceable_of_two_or_three_losses_each H noSix (by omega) a (by omega) b)
  omega

#print axioms FourBlockPacking.good_entries_distinct_owners
#print axioms FourBlockPacking.traceable_of_distinct_entry_owners
#print axioms FourBlockPacking.traceable_of_two_or_three_losses_each
#print axioms FourBlockPacking.highs_owned_of_four_losses
#print axioms FourBlockPacking.four_losses_at_fifteen

end Graffiti199Depleted
