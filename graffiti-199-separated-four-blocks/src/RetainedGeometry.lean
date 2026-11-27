import CatalogueInterface

open private pair_low_cases singleton_region_cases FourBlockPacking.singleton_regions_disjoint
  from FourBlockIntegration
open private three_names_exhaust_neighbors from DepletedFootprint
open private InternallyIndependent independent_pair independent_union from SplitTipsSplice

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- The disjoint-high branch of the recovered two-pair reduction. -/
structure FourBlockSeparation (F : FourBlockPacking G) : Prop where
  singletons : Disjoint (singletonPorts F.first) (singletonPorts F.second)
  pairs : Disjoint (pairPorts F.depleted) (pairPorts F.terminal)
  depletedDegree : ∀ v ∈ pairPorts F.depleted, G.degree v ≠ 3

variable (F : FourBlockPacking G)

def FourBlockPacking.retained (P : FullPair G) : Set V :=
  {v | ∃ i : O, i ∉ F.lost P ∧ P.f i = v}

private theorem FullPair.degree_of_low (P : FullPair G) (i : O) (low : i.val < 2) :
    G.degree (P.f i) = 3 := by
  rcases pair_low_cases i low with rfl|rfl
  · exact P.degree 0 (by decide)
  · exact P.degree 1 (by decide)

private theorem FullPair.neighbors_zero (P : FullPair G) {v : V} (e : G.Adj (P.f 0) v) :
    ∃ j ∈ ([1,2,3] : List O), P.f j = v :=
  three_names_exhaust_neighbors P.f (by decide) (by decide) (by decide)
    (P.degree 0 (by decide)) (P.edges 0 1 (by decide)) (P.edges 0 2 (by decide))
    (P.edges 0 3 (by decide)) v e

private theorem FullPair.neighbors_one (P : FullPair G) {v : V} (e : G.Adj (P.f 1) v) :
    ∃ j ∈ ([0,4,5] : List O), P.f j = v :=
  three_names_exhaust_neighbors P.f (by decide) (by decide) (by decide)
    (P.degree 1 (by decide)) (P.edges 0 1 (by decide)).symm (P.edges 1 4 (by decide))
    (P.edges 1 5 (by decide)) v e

private theorem FullPair.opp_low (P : FullPair G) {i : O} (high : 2 ≤ i.val) :
    ∃ u : V, u ∈ labelRegion P.f ∧ G.degree u = 3 ∧ u ≠ P.f i ∧
      ¬ G.Adj u (P.f i) ∧ ∀ v, G.Adj u v → v ∈ labelRegion P.f := by
  by_cases left : i.val < 4
  · refine ⟨P.f 1,⟨1,rfl⟩,P.degree 1 (by decide),P.f.injective.ne (by intro e; subst i; omega),?_,?_⟩
    · intro h
      obtain ⟨j,jm,e⟩ := P.neighbors_one h
      have off : i ∉ ([0,4,5] : List O) := by fin_cases i <;> simp_all
      exact off (P.f.injective e ▸ jm)
    · intro v h
      obtain ⟨j,_,e⟩ := P.neighbors_one h
      exact ⟨j,e⟩
  · refine ⟨P.f 0,⟨0,rfl⟩,P.degree 0 (by decide),P.f.injective.ne (by intro e; subst i; omega),?_,?_⟩
    · intro h
      obtain ⟨j,jm,e⟩ := P.neighbors_zero h
      have off : i ∉ ([1,2,3] : List O) := by fin_cases i <;> simp_all
      exact off (P.f.injective e ▸ jm)
    · intro v h
      obtain ⟨j,_,e⟩ := P.neighbors_zero h
      exact ⟨j,e⟩

theorem FourBlockSeparation.full_pairs (H : FourBlockSeparation F) :
    Disjoint (labelRegion F.depleted.f) (labelRegion F.terminal.f) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨i,rfl⟩ ⟨j,eq⟩
  by_cases hi : 2 ≤ i.val
  · by_cases hj : 2 ≤ j.val
    · exact Set.disjoint_left.mp H.pairs ⟨i,hi,rfl⟩ ⟨j,hj,eq⟩
    · exact H.depletedDegree _ ⟨i,hi,rfl⟩ (eq ▸ F.terminal.degree_of_low j (by omega))
  · by_cases hj : 2 ≤ j.val
    · exact F.highDegree _ (Or.inr ⟨j,hj,eq⟩) (F.depleted.degree_of_low i (by omega))
    · rcases pair_low_cases i (by omega) with rfl|rfl <;>
        rcases pair_low_cases j (by omega) with rfl|rfl
      · exact F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 2) eq
      · exact F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 2) eq
      · exact F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 3) eq
      · exact F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 3) eq

theorem FourBlockPacking.retained_subset (P : FullPair G) :
    F.retained P ⊆ labelRegion P.f := by
  rintro _ ⟨i,_,eq⟩
  exact ⟨i,eq⟩

private theorem retained_away (S : PrivateSingleton G) (P : FullPair G)
    (lo0 : P.f 0 ≠ S.f 0) (lo1 : P.f 1 ≠ S.f 0)
    (sHigh : ∀ v ∈ singletonPorts S, G.degree v ≠ 3)
    (sOwner : singletonPorts S ⊆ singletonPorts F.first ∪ singletonPorts F.second)
    (pHigh : ∀ v ∈ pairPorts P, G.degree v ≠ 3) :
    Disjoint (labelRegion S.f) (F.retained P) := by
  apply Set.disjoint_left.mpr
  rintro _ hs ⟨i,keep,rfl⟩
  rcases singleton_region_cases S hs with eq|hp
  · by_cases low : i.val < 2
    · exact (pair_low_cases i low).elim (fun e => lo0 (e ▸ eq)) (fun e => lo1 (e ▸ eq))
    · exact pHigh _ ⟨i,by omega,rfl⟩ (eq.symm ▸ S.degree)
  · by_cases low : i.val < 2
    · exact sHigh _ hp (P.degree_of_low i low)
    · exact keep (F.mem_lost.mpr ⟨by omega,sOwner hp⟩)

theorem FourBlockSeparation.first_depleted (H : FourBlockSeparation F) :
    Disjoint (labelRegion F.first.f) (F.retained F.depleted) :=
  retained_away F F.first F.depleted (F.lowDistinct.ne (by decide : (2 : Fin 6) ≠ 0))
    (F.lowDistinct.ne (by decide : (3 : Fin 6) ≠ 0))
    (fun v h => F.highDegree v (Or.inl (Or.inl h))) (fun _ h => Or.inl h) H.depletedDegree

theorem FourBlockSeparation.first_terminal :
    Disjoint (labelRegion F.first.f) (F.retained F.terminal) :=
  retained_away F F.first F.terminal (F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 0))
    (F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 0))
    (fun v h => F.highDegree v (Or.inl (Or.inl h))) (fun _ h => Or.inl h)
    (fun v h => F.highDegree v (Or.inr h))

theorem FourBlockSeparation.second_depleted (H : FourBlockSeparation F) :
    Disjoint (labelRegion F.second.f) (F.retained F.depleted) :=
  retained_away F F.second F.depleted (F.lowDistinct.ne (by decide : (2 : Fin 6) ≠ 1))
    (F.lowDistinct.ne (by decide : (3 : Fin 6) ≠ 1))
    (fun v h => F.highDegree v (Or.inl (Or.inr h))) (fun _ h => Or.inr h) H.depletedDegree

theorem FourBlockSeparation.second_terminal :
    Disjoint (labelRegion F.second.f) (F.retained F.terminal) :=
  retained_away F F.second F.terminal (F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 1))
    (F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 1))
    (fun v h => F.highDegree v (Or.inl (Or.inr h))) (fun _ h => Or.inr h)
    (fun v h => F.highDegree v (Or.inr h))

theorem FourBlockSeparation.singleton_regions (H : FourBlockSeparation F) :
    Disjoint (labelRegion F.first.f) (labelRegion F.second.f) :=
  FourBlockPacking.singleton_regions_disjoint F H.singletons

theorem FourBlockSeparation.retained_pairs (H : FourBlockSeparation F) :
    Disjoint (F.retained F.depleted) (F.retained F.terminal) :=
  (H.full_pairs).mono (F.retained_subset _) (F.retained_subset _)

theorem FourBlockPacking.retained_cover (v : V) :
    v ∈ labelRegion F.first.f ∨ v ∈ labelRegion F.second.f ∨
      v ∈ F.retained F.depleted ∨ v ∈ F.retained F.terminal := by
  have split (P : FullPair G) (h : v ∈ labelRegion P.f) :
      v ∈ labelRegion F.first.f ∨ v ∈ labelRegion F.second.f ∨ v ∈ F.retained P := by
    obtain ⟨i,rfl⟩ := h
    by_cases lost : i ∈ F.lost P
    · rcases (F.mem_lost.mp lost).2 with ⟨j,_,e⟩|⟨j,_,e⟩
      · exact Or.inl ⟨j,e⟩
      · exact Or.inr (Or.inl ⟨j,e⟩)
    · exact Or.inr (Or.inr ⟨i,lost,rfl⟩)
  rcases F.cover v with a|b|c|d
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · exact (split _ c).imp id (Or.imp id Or.inl)
  · exact (split _ d).imp id (Or.imp id Or.inr)

omit [Fintype V] in
private theorem finite_disjoint {s t : Finset V} {U W : Set V} (h : Disjoint U W)
    (su : ∀ x ∈ s, x ∈ U) (tw : ∀ x ∈ t, x ∈ W) : Disjoint s t :=
  Finset.disjoint_left.mpr fun v a b => Set.disjoint_left.mp h (su v a) (tw v b)

/-- The two retained portions and two full singleton regions form a
partition, so the paired loss counts exactly account for the order deficit. -/
theorem FourBlockPacking.order_add_pair_losses (H : FourBlockSeparation F) :
    Fintype.card V + (F.lost F.depleted).card + (F.lost F.terminal).card = 20 := by
  classical
  let A := Finset.univ.map F.first.f
  let B := Finset.univ.map F.second.f
  let C := (Finset.univ \ F.lost F.depleted).map F.depleted.f
  let D := (Finset.univ \ F.lost F.terminal).map F.terminal.f
  have ma (v : V) : v ∈ A ↔ v ∈ labelRegion F.first.f := by simp [A,labelRegion]
  have mb (v : V) : v ∈ B ↔ v ∈ labelRegion F.second.f := by simp [B,labelRegion]
  have mc (v : V) : v ∈ C ↔ v ∈ F.retained F.depleted := by simp [C,FourBlockPacking.retained]
  have md (v : V) : v ∈ D ↔ v ∈ F.retained F.terminal := by simp [D,FourBlockPacking.retained]
  have ab := finite_disjoint H.singleton_regions (fun v => (ma v).mp) (fun v => (mb v).mp)
  have ac := finite_disjoint H.first_depleted (fun v => (ma v).mp) (fun v => (mc v).mp)
  have ad := finite_disjoint (FourBlockSeparation.first_terminal F)
    (fun v => (ma v).mp) (fun v => (md v).mp)
  have bc := finite_disjoint H.second_depleted (fun v => (mb v).mp) (fun v => (mc v).mp)
  have bd := finite_disjoint (FourBlockSeparation.second_terminal F)
    (fun v => (mb v).mp) (fun v => (md v).mp)
  have cd := finite_disjoint H.retained_pairs (fun v => (mc v).mp) (fun v => (md v).mp)
  have un : A ∪ B ∪ (C ∪ D) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    rcases F.retained_cover v with a|b|c|d
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ((ma v).mpr a))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ((mb v).mpr b))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl ((mc v).mpr c))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr ((md v).mpr d))))
  have total := Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_right.mpr ⟨ac,ad⟩, Finset.disjoint_union_right.mpr ⟨bc,bd⟩⟩)
  rw [un,Finset.card_univ,Finset.card_union_of_disjoint ab,Finset.card_union_of_disjoint cd] at total
  have ca : A.card = 4 := by simp [A]
  have cb : B.card = 4 := by simp [B]
  have cc : C.card + (F.lost F.depleted).card = 6 := by
    simpa [C] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (F.lost F.depleted))
  have cd' : D.card + (F.lost F.terminal).card = 6 := by
    simpa [D] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (F.lost F.terminal))
  omega

variable [DecidableEq V]

/-- In the no-independent-six branch, every retained pair tip sees
every retained tip of the other pair. -/
theorem FourBlockPacking.retained_highs_adjacent (H : FourBlockSeparation F)
    (noSix : NoIndependentSix G) {i j : O}
    (hi : 2 ≤ i.val) (hj : 2 ≤ j.val)
    (ki : i ∉ F.lost F.depleted) (kj : j ∉ F.lost F.terminal) :
    G.Adj (F.depleted.f i) (F.terminal.f j) := by
  classical
  by_contra no
  obtain ⟨a,aIn,aDegree,ane,an,astays⟩ := F.depleted.opp_low hi
  obtain ⟨b,bIn,bDegree,bne,bn,bstays⟩ := F.terminal.opp_low hj
  let A : Finset V := {F.first.f 0,F.second.f 0}
  let B : Finset V := {a,F.depleted.f i}
  let C : Finset V := {b,F.terminal.f j}
  have low_off (R : PrivateSingleton G) {v : V} (out : v ∉ labelRegion R.f) :
      ¬ G.Adj (R.f 0) v := fun e => Bool.false_ne_true (R.outgoing_high out e)
  have aRegion (x : V) (hx : x ∈ A) : x ∈ labelRegion F.first.f ∪ labelRegion F.second.f := by
    rcases (show x = F.first.f 0 ∨ x = F.second.f 0 by simpa [A] using hx) with rfl|rfl
    · exact Or.inl ⟨0,rfl⟩
    · exact Or.inr ⟨0,rfl⟩
  have bRegion (x : V) (hx : x ∈ B) : x ∈ labelRegion F.depleted.f := by
    rcases (show x = a ∨ x = F.depleted.f i by simpa [B] using hx) with rfl|rfl
    · exact aIn
    · exact ⟨i,rfl⟩
  have cRegion (x : V) (hx : x ∈ C) : x ∈ labelRegion F.terminal.f := by
    rcases (show x = b ∨ x = F.terminal.f j by simpa [C] using hx) with rfl|rfl
    · exact bIn
    · exact ⟨j,rfl⟩
  have aKeep : a ∈ F.retained F.depleted := by
    obtain ⟨k,e⟩ := aIn
    exact ⟨k,fun lost => H.depletedDegree a ⟨k,(F.mem_lost.mp lost).1,e⟩ aDegree,e⟩
  have bKeep : b ∈ F.retained F.terminal := by
    obtain ⟨k,e⟩ := bIn
    exact ⟨k,fun lost => F.highDegree b (Or.inr ⟨k,(F.mem_lost.mp lost).1,e⟩) bDegree,e⟩
  have br (x : V) (hx : x ∈ B) : x ∈ F.retained F.depleted := by
    rcases (show x = a ∨ x = F.depleted.f i by simpa [B] using hx) with rfl|rfl
    · exact aKeep
    · exact ⟨i,ki,rfl⟩
  have cr (x : V) (hx : x ∈ C) : x ∈ F.retained F.terminal := by
    rcases (show x = b ∨ x = F.terminal.f j by simpa [C] using hx) with rfl|rfl
    · exact bKeep
    · exact ⟨j,kj,rfl⟩
  have abDis := Set.disjoint_union_left.mpr ⟨H.first_depleted,H.second_depleted⟩
  have acDis := Set.disjoint_union_left.mpr
    ⟨FourBlockSeparation.first_terminal F,FourBlockSeparation.second_terminal F⟩
  have size : (A ∪ B ∪ C).card = 6 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨finite_disjoint acDis aRegion cr,finite_disjoint H.retained_pairs br cr⟩),
      Finset.card_union_of_disjoint (finite_disjoint abDis aRegion br)]
    simp [A,B,C,Finset.card_pair ane,Finset.card_pair bne,
      F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 1)]
    exact Finset.card_pair (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 1))
  have fromA {U : Set V} (sep : Disjoint (labelRegion F.first.f ∪ labelRegion F.second.f) U)
      {x y : V} (hx : x ∈ A) (hy : y ∈ U) : ¬ G.Adj x y := by
    rcases (show x = F.first.f 0 ∨ x = F.second.f 0 by simpa [A] using hx) with rfl|rfl
    · exact low_off F.first (fun m => Set.disjoint_left.mp sep (Or.inl m) hy)
    · exact low_off F.second (fun m => Set.disjoint_left.mp sep (Or.inr m) hy)
  have ab : InternallyIndependent G (A ∪ B) := independent_union
    (independent_pair _ _ (low_off F.first (fun h => Set.disjoint_left.mp H.singleton_regions h ⟨0,rfl⟩)))
    (independent_pair _ _ an) (fun x hx y hy => fromA abDis hx (br y hy))
  have bc (x : V) (hx : x ∈ B) (y : V) (hy : y ∈ C) : ¬ G.Adj x y := by
    intro e
    by_cases xa : x = a
    · exact Set.disjoint_left.mp H.full_pairs (astays y (xa ▸ e)) (cRegion y hy)
    · by_cases yb : y = b
      · exact Set.disjoint_left.mp H.full_pairs (bRegion x hx) (bstays x (yb ▸ e.symm))
      · have ex := (show x = a ∨ x = F.depleted.f i by simpa [B] using hx).resolve_left xa
        have ey := (show y = b ∨ y = F.terminal.f j by simpa [C] using hy).resolve_left yb
        exact no (ex ▸ ey ▸ e)
  have all : InternallyIndependent G (A ∪ B ∪ C) := independent_union ab
    (independent_pair _ _ bn) (fun x hx y hy =>
      (Finset.mem_union.mp hx).elim (fun ha => fromA acDis ha (cr y hy)) (fun hb => bc x hb y hy))
  obtain ⟨x,hx,y,hy,e⟩ := noSix _ size
  exact all x hx y hy e

#print axioms FourBlockPacking.order_add_pair_losses
#print axioms FourBlockPacking.retained_highs_adjacent

end Graffiti199Depleted
