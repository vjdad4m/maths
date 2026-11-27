import SharedPortCapacity

open private pair_low_cases singleton_region_cases from FourBlockIntegration
open private FullPair.low FullPair.low_stays FullPair.degree_three_off from SharedHighSeparation

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

private theorem singleton_ports_card (R : PrivateSingleton G) :
    (verticesIn (singletonPorts R)).card = 3 := by
  classical
  have eq : verticesIn (singletonPorts R) =
      ((Finset.univ : Finset (Fin 4)).filter fun i => singletonHigh i = true).map R.f := by
    ext v
    simp [singletonPorts]
  rw [eq,Finset.card_map]
  decide

private theorem pair_ports_card (P : FullPair G) : (verticesIn (pairPorts P)).card = 4 := by
  classical
  have eq : verticesIn (pairPorts P) =
      ((Finset.univ : Finset O).filter fun i : O => 2 ≤ i.val).map P.f := by
    ext v
    simp [pairPorts]
  rw [eq,Finset.card_map]
  decide

variable (F : FourBlockPacking G)

/-- Accounting for the repeated pair highs and the singleton-owned pair
highs before requiring that the pairs have disjoint high sets. -/
theorem FourBlockPacking.order_add_shared_and_owned
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (sDis : Disjoint (singletonPorts F.first) (singletonPorts F.second))
    [DecidableEq V] :
    let P := verticesIn (pairPorts F.depleted)
    let Q := verticesIn (pairPorts F.terminal)
    let U := verticesIn (singletonPorts F.first) ∪ verticesIn (singletonPorts F.second)
    Fintype.card V + (P ∩ Q).card + ((P ∪ Q) ∩ U).card = 20 := by
  classical
  let P := verticesIn (pairPorts F.depleted)
  let Q := verticesIn (pairPorts F.terminal)
  let A := verticesIn (singletonPorts F.first)
  let B := verticesIn (singletonPorts F.second)
  let low : Fin 6 ↪ V := ⟨![F.first.f 0,F.second.f 0,F.depleted.f 0,F.depleted.f 1,
    F.terminal.f 0,F.terminal.f 1],F.lowDistinct⟩
  let L := Finset.univ.map low
  let H := (P ∪ Q) ∪ (A ∪ B)
  have lc : L.card = 6 := by simp [L]
  have pc : P.card = 4 := pair_ports_card _
  have qc : Q.card = 4 := pair_ports_card _
  have ab : Disjoint A B := Finset.disjoint_left.mpr fun v a b =>
    Set.disjoint_left.mp sDis (mem_verticesIn.mp a) (mem_verticesIn.mp b)
  have abc : (A ∪ B).card = 6 := by
    rw [Finset.card_union_of_disjoint ab]
    exact congrArg₂ (· + ·) (singleton_ports_card F.first) (singleton_ports_card F.second)
  have lowDeg (i : Fin 6) : G.degree (low i) = 3 := by
    fin_cases i
    · exact F.first.degree
    · exact F.second.degree
    · exact F.depleted.degree 0 (by decide)
    · exact F.depleted.degree 1 (by decide)
    · exact F.terminal.degree 0 (by decide)
    · exact F.terminal.degree 1 (by decide)
  have isolated : Disjoint L H := by
    apply Finset.disjoint_left.mpr
    rintro _ hm hn
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hm
    have degree := lowDeg i
    rcases Finset.mem_union.mp hn with pairs|singletons
    · rcases Finset.mem_union.mp pairs with hp|hq
      · exact pHigh _ (mem_verticesIn.mp hp) degree
      · exact F.highDegree _ (Or.inr (mem_verticesIn.mp hq)) degree
    · rcases Finset.mem_union.mp singletons with ha|hb
      · exact F.highDegree _ (Or.inl (Or.inl (mem_verticesIn.mp ha))) degree
      · exact F.highDegree _ (Or.inl (Or.inr (mem_verticesIn.mp hb))) degree
  have all : L ∪ H = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    rcases F.cover v with a|b|p|q
    · rcases singleton_region_cases F.first a with rfl|hi
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨0,Finset.mem_univ _,rfl⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inl (mem_verticesIn.mpr hi))))))
    · rcases singleton_region_cases F.second b with rfl|hi
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨1,Finset.mem_univ _,rfl⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inr (mem_verticesIn.mpr hi))))))
    · obtain ⟨i,rfl⟩ := p
      by_cases hi : 2 ≤ i.val
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inl (mem_verticesIn.mpr ⟨i,hi,rfl⟩))))))
      · rcases pair_low_cases i (by omega) with rfl|rfl
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨2,Finset.mem_univ _,rfl⟩))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨3,Finset.mem_univ _,rfl⟩))
    · obtain ⟨i,rfl⟩ := q
      by_cases hi : 2 ≤ i.val
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr (mem_verticesIn.mpr ⟨i,hi,rfl⟩))))))
      · rcases pair_low_cases i (by omega) with rfl|rfl
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨4,Finset.mem_univ _,rfl⟩))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨5,Finset.mem_univ _,rfl⟩))
  have n := Finset.card_union_of_disjoint isolated
  rw [all,Finset.card_univ,lc] at n
  have pairSum := Finset.card_union_add_card_inter P Q
  rw [pc,qc] at pairSum
  have highSum := Finset.card_union_add_card_inter (P ∪ Q) (A ∪ B)
  rw [abc] at highSum
  change Fintype.card V + (P ∩ Q).card + ((P ∪ Q) ∩ (A ∪ B)).card = 20
  change Fintype.card V = 6 + ((P ∪ Q) ∪ (A ∪ B)).card at n
  omega

private def swap_without_separation
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3) : FourBlockPacking G where
  first := F.first
  second := F.second
  depleted := F.terminal
  terminal := F.depleted
  looseFirst := F.looseFirst
  looseSecond := F.looseSecond
  lowDistinct := by
    let perm : Fin 6 → Fin 6 := ![0,1,4,5,2,3]
    have pinj : Function.Injective perm := by
      unfold Function.Injective
      decide
    let low : Fin 6 → V := ![F.first.f 0,F.second.f 0,F.depleted.f 0,F.depleted.f 1,
      F.terminal.f 0,F.terminal.f 1]
    have eq : (![F.first.f 0,F.second.f 0,F.terminal.f 0,F.terminal.f 1,
      F.depleted.f 0,F.depleted.f 1] : Fin 6 → V) = low ∘ perm := by
      funext i
      fin_cases i <;> rfl
    rw [eq]
    exact F.lowDistinct.comp pinj
  highDegree := fun v hv => hv.elim (fun h => F.highDegree v (Or.inl h)) (pHigh v)
  cover := fun v => (F.cover v).imp id (Or.imp id Or.symm)

private theorem paired_highs_not_equal
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (bound : Catalogue.treeNumber G ≤ 5) (connected : G.Connected)
    (same : pairPorts F.depleted = pairPorts F.terminal) : False := by
  let U := labelRegion F.depleted.f ∪ labelRegion F.terminal.f
  have far : F.first.f 0 ∉ U := by
    rintro (a|b)
    · exact FullPair.degree_three_off F.depleted F.first.degree
        (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 2))
        (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 3)) pHigh a
    · exact FullPair.degree_three_off F.terminal F.first.degree
        (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 4))
        (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 5))
        (fun v h => F.highDegree v (Or.inr h)) b
  obtain ⟨w⟩ := connected.preconnected (F.depleted.f 0) (F.first.f 0)
  obtain ⟨x,hx,y,hy,xy⟩ := crossingOnWalk (U := U) w (Or.inl ⟨0,rfl⟩) far
  rcases hx with ⟨i,rfl⟩|⟨i,rfl⟩
  · by_cases hi : 2 ≤ i.val
    · have port : F.depleted.f i ∈ pairPorts F.depleted := ⟨i,hi,rfl⟩
      exact F.shared_paired_high_no_outside_neighbor pHigh bound port (same ▸ port)
        (fun h => hy (Or.inl h)) (fun h => hy (Or.inr h)) xy
    · rcases pair_low_cases i (by omega) with rfl|rfl
      · exact hy (Or.inl (FullPair.low_stays F.depleted false xy))
      · exact hy (Or.inl (FullPair.low_stays F.depleted true xy))
  · by_cases hi : 2 ≤ i.val
    · have port : F.terminal.f i ∈ pairPorts F.terminal := ⟨i,hi,rfl⟩
      exact F.shared_paired_high_no_outside_neighbor pHigh bound (same.symm ▸ port) port
        (fun h => hy (Or.inl h)) (fun h => hy (Or.inr h)) xy
    · rcases pair_low_cases i (by omega) with rfl|rfl
      · exact hy (Or.inr (FullPair.low_stays F.terminal false xy))
      · exact hy (Or.inr (FullPair.low_stays F.terminal true xy))

/-- In the covered layout at orders fifteen and sixteen, the two paired
high sets are disjoint once the singleton high sets are disjoint. -/
theorem FourBlockPacking.pair_highs_disjoint_at_fifteen_or_sixteen
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (sDis : Disjoint (singletonPorts F.first) (singletonPorts F.second))
    (budget : Catalogue.treeNumber G ≤ 5) (connected : G.Connected)
    (order : Fintype.card V = 15 ∨ Fintype.card V = 16) :
    Disjoint (pairPorts F.depleted) (pairPorts F.terminal) := by
  classical
  let P := verticesIn (pairPorts F.depleted)
  let Q := verticesIn (pairPorts F.terminal)
  let U := verticesIn (singletonPorts F.first) ∪ verticesIn (singletonPorts F.second)
  let R := P ∩ Q
  let A := P ∩ U
  let B := Q ∩ U
  have hmU (v : V) : v ∈ U ↔ v ∈ singletonPorts F.first ∪ singletonPorts F.second := by simp [U]
  have hr (v : V) : v ∈ R ↔ v ∈ pairPorts F.depleted ∩ pairPorts F.terminal := by simp [R,P,Q]
  have hA (v : V) : v ∈ A ↔ v ∈ pairPorts F.depleted ∩
      (singletonPorts F.first ∪ singletonPorts F.second) := by simp [A,P,hmU]
  have hB (v : V) : v ∈ B ↔ v ∈ pairPorts F.terminal ∩
      (singletonPorts F.first ∪ singletonPorts F.second) := by simp [B,Q,hmU]
  apply Set.disjoint_left.mpr
  intro v vp vq
  have someR : R.Nonempty := ⟨v,(hr v).mpr ⟨vp,vq⟩⟩
  have pos : 0 < R.card := Finset.card_pos.mpr someR
  have balance := F.order_add_shared_and_owned pHigh sDis
  have total : Fintype.card V + R.card + (A ∪ B).card = 20 := by
    have eq : A ∪ B = (P ∪ Q) ∩ U := by
      ext v
      simp only [A,B,Finset.mem_union,Finset.mem_inter]
      tauto
    rw [eq]
    exact balance
  have capA (some : A.Nonempty) : R.card + A.card ≤ 2 :=
    F.shared_owned_highs_capacity pHigh budget R A hr hA someR some
  have capB (some : B.Nonempty) : R.card + B.card ≤ 2 := by
    let S := swap_without_separation F pHigh
    exact S.shared_owned_highs_capacity (fun v h => F.highDegree v (Or.inr h))
      budget R B (fun v => (hr v).trans (by simp [S,Set.inter_comm,swap_without_separation]))
      hB someR some
  have aOne : A.card ≤ 1 := by
    by_cases hp : A.Nonempty
    · have h := capA hp
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hp]
  have bOne : B.card ≤ 1 := by
    by_cases hp : B.Nonempty
    · have h := capB hp
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hp]
  have abTwo : (A ∪ B).card ≤ 2 := (Finset.card_union_le A B).trans (by omega)
  have many : 2 ≤ R.card := by omega
  have a0 : A = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro h
    have one := Finset.card_pos.mpr h
    have two := capA h
    omega
  have b0 : B = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro h
    have one := Finset.card_pos.mpr h
    have two := capB h
    omega
  rw [a0,b0,Finset.empty_union,Finset.card_empty] at total
  have pc : P.card = 4 := pair_ports_card _
  have qc : Q.card = 4 := pair_ports_card _
  have rp : R ⊆ P := Finset.inter_subset_left
  have rq : R ⊆ Q := Finset.inter_subset_right
  have up := Finset.card_le_card rp
  have four : R.card = 4 := by omega
  have eq : P = Q := (Finset.eq_of_subset_of_card_le rp (by omega)).symm.trans
    (Finset.eq_of_subset_of_card_le rq (by omega))
  have same : pairPorts F.depleted = pairPorts F.terminal := by
    ext x
    exact (mem_verticesIn (U := pairPorts F.depleted)).symm.trans
      ((show x ∈ P ↔ x ∈ Q by rw [eq]).trans mem_verticesIn)
  exact paired_highs_not_equal F pHigh budget connected same

#print axioms FourBlockPacking.order_add_shared_and_owned
#print axioms FourBlockPacking.pair_highs_disjoint_at_fifteen_or_sixteen

end Graffiti199Depleted
