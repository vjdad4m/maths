import TerminalLossAdapter
import RemainingCut

namespace Graffiti199Depleted

open SimpleGraph Graffiti199K2.NearPacking.Depleted

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- A full paired neighborhood before shared vertices are assigned to singletons. -/
structure FullPair (G : SimpleGraph V) [DecidableRel G.Adj] where
  f : O ↪ V
  edges : ∀ a b, (a,b) ∈ terminalEdges → G.Adj (f a) (f b)
  degree : ∀ i ∈ ([0,1] : List O), G.degree (f i) = 3

def singletonPorts (R : PrivateSingleton G) : Set V :=
  {v | ∃ i : Fin 4, singletonHigh i = true ∧ R.f i = v}

def pairPorts (P : FullPair G) : Set V :=
  {v | ∃ i : O, 2 ≤ i.val ∧ P.f i = v}

/-- The four full neighborhoods can overlap at their high vertices.
Only the six low vertices have separate names at this stage. -/
structure FourBlockPacking (G : SimpleGraph V) [DecidableRel G.Adj] where
  first : PrivateSingleton G
  second : PrivateSingleton G
  depleted : FullPair G
  terminal : FullPair G
  looseFirst : ¬ G.Adj (first.f 2) (first.f 3)
  looseSecond : ¬ G.Adj (second.f 2) (second.f 3)
  lowDistinct : Function.Injective
    (![first.f 0,second.f 0,depleted.f 0,depleted.f 1,terminal.f 0,terminal.f 1] : Fin 6 → V)
  highDegree : ∀ v, v ∈ singletonPorts first ∪ singletonPorts second ∪ pairPorts terminal →
    G.degree v ≠ 3
  cover : ∀ v, v ∈ labelRegion first.f ∨ v ∈ labelRegion second.f ∨
    v ∈ labelRegion depleted.f ∨ v ∈ labelRegion terminal.f

variable (F : FourBlockPacking G)

noncomputable def FourBlockPacking.lost (R : FullPair G) : Finset O := by
  classical
  exact Finset.univ.filter fun i : O =>
    2 ≤ i.val ∧ R.f i ∈ (singletonPorts F.first ∪ singletonPorts F.second)

theorem FourBlockPacking.mem_lost {R : FullPair G} {i : O} :
    i ∈ F.lost R ↔ 2 ≤ i.val ∧ R.f i ∈ (singletonPorts F.first ∪ singletonPorts F.second) := by
  classical
  simp [FourBlockPacking.lost]

/-- Convert the original vertex-set allocation predicate to the local labels.
An allocated high is lost exactly when it belongs to a singleton's high set. -/
theorem FourBlockPacking.lost_map_eq_forbidden (R : FullPair G) (forbidden : Finset V)
    (highOnly : ∀ v ∈ forbidden, v ∈ pairPorts R)
    (membership : ∀ v ∈ pairPorts R,
      v ∈ forbidden ↔ v ∈ singletonPorts F.first ∪ singletonPorts F.second) :
    (F.lost R).map R.f = forbidden := by
  apply Finset.ext
  intro v
  constructor
  · intro h
    obtain ⟨i,loss,rfl⟩ := Finset.mem_map.mp h
    have ⟨hi,inSingleton⟩ := F.mem_lost.mp loss
    exact (membership _ ⟨i,hi,rfl⟩).mpr inSingleton
  · intro h
    have overlap := (membership v (highOnly v h)).mp h
    obtain ⟨i,hi,rfl⟩ := highOnly v h
    exact Finset.mem_map.mpr ⟨i,F.mem_lost.mpr ⟨hi,overlap⟩,rfl⟩

private theorem pair_low_cases (i : O) (lo : i.val < 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp_all

private theorem singleton_region_cases (S : PrivateSingleton G) {v : V}
    (h : v ∈ labelRegion S.f) : v = S.f 0 ∨ v ∈ singletonPorts S := by
  obtain ⟨i,rfl⟩ := h
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr ⟨1,rfl,rfl⟩
  · exact Or.inr ⟨2,rfl,rfl⟩
  · exact Or.inr ⟨3,rfl,rfl⟩

private theorem FourBlockPacking.degree_second_high {v : V} (h : v ∈ singletonPorts F.second) :
    G.degree v ≠ 3 := F.highDegree v (Or.inl (Or.inr h))

private theorem FourBlockPacking.degree_first_high {v : V} (h : v ∈ singletonPorts F.first) :
    G.degree v ≠ 3 := F.highDegree v (Or.inl (Or.inl h))

private theorem FourBlockPacking.degree_terminal_high {i : O} (h : 2 ≤ i.val) :
    G.degree (F.terminal.f i) ≠ 3 := F.highDegree _ (Or.inr ⟨i,h,rfl⟩)

private theorem FourBlockPacking.singleton_regions_disjoint
    (portsDisjoint : Disjoint (singletonPorts F.first) (singletonPorts F.second)) :
    Disjoint (labelRegion F.first.f) (labelRegion F.second.f) := by
  apply Set.disjoint_left.mpr
  intro v first second
  rcases singleton_region_cases F.first first with rfl|hi
  · rcases singleton_region_cases F.second second with eq|hi
    · exact F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 1) eq
    · exact F.degree_second_high hi F.first.degree
  · rcases singleton_region_cases F.second second with rfl|hj
    · exact F.degree_first_high hi F.second.degree
    · exact Set.disjoint_left.mp portsDisjoint hi hj

private def FourBlockPacking.depletedLows : Fin 2 ↪ V :=
  ⟨fun i => F.depleted.f (i.castAdd 4),fun _ _ e =>
    Fin.ext (congrArg (fun k : O => k.val) (F.depleted.f.injective e))⟩

private def FourBlockPacking.depletedHighs : Fin 4 ↪ V :=
  ⟨fun i => F.depleted.f (i.natAdd 2),fun i j e => by
    apply Fin.ext
    have h : 2 + i.val = 2 + j.val := congrArg Fin.val (F.depleted.f.injective e)
    omega⟩

private theorem FourBlockPacking.depleted_low_degree (i : Fin 2) :
    G.degree (F.depletedLows i) = 3 := by
  fin_cases i
  · exact F.depleted.degree 0 (by decide)
  · exact F.depleted.degree 1 (by decide)

private theorem FourBlockPacking.low_off_singletons :
    Disjoint (labelRegion F.first.f ∪ labelRegion F.second.f) (labelRegion F.depletedLows) := by
  apply Set.disjoint_left.mpr
  rintro v hv ⟨i,rfl⟩
  rcases hv with first|second
  · rcases singleton_region_cases F.first first with eq|hi
    · fin_cases i
      · exact F.lowDistinct.ne (by decide : (2 : Fin 6) ≠ 0) eq
      · exact F.lowDistinct.ne (by decide : (3 : Fin 6) ≠ 0) eq
    · exact F.degree_first_high hi (F.depleted_low_degree i)
  · rcases singleton_region_cases F.second second with eq|hi
    · fin_cases i
      · exact F.lowDistinct.ne (by decide : (2 : Fin 6) ≠ 1) eq
      · exact F.lowDistinct.ne (by decide : (3 : Fin 6) ≠ 1) eq
    · exact F.degree_second_high hi (F.depleted_low_degree i)

private def FourBlockPacking.innerSet : Set V :=
  (labelRegion F.first.f ∪ labelRegion F.second.f) ∪ labelRegion F.depletedLows

private def FourBlockPacking.keptSet : Set V :=
  {v | ∃ i : O, i ∉ F.lost F.terminal ∧ F.terminal.f i = v}

private theorem FourBlockPacking.terminal_low_off_inner {i : O} (hi : i.val < 2) :
    F.terminal.f i ∉ F.innerSet := by
  have deg : G.degree (F.terminal.f i) = 3 := by
    rcases pair_low_cases i hi with rfl|rfl
    · exact F.terminal.degree 0 (by decide)
    · exact F.terminal.degree 1 (by decide)
  rintro ((s|t)|⟨k,eq⟩)
  · rcases singleton_region_cases F.first s with eq|off
    · rcases pair_low_cases i hi with rfl|rfl
      · exact F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 0) eq
      · exact F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 0) eq
    · exact F.degree_first_high off deg
  · rcases singleton_region_cases F.second t with eq|off
    · rcases pair_low_cases i hi with rfl|rfl
      · exact F.lowDistinct.ne (by decide : (4 : Fin 6) ≠ 1) eq
      · exact F.lowDistinct.ne (by decide : (5 : Fin 6) ≠ 1) eq
    · exact F.degree_second_high off deg
  · rcases pair_low_cases i hi with rfl|rfl <;> fin_cases k
    · exact F.lowDistinct.ne (by decide : (2 : Fin 6) ≠ 4) eq
    · exact F.lowDistinct.ne (by decide : (3 : Fin 6) ≠ 4) eq
    · exact F.lowDistinct.ne (by decide : (2 : Fin 6) ≠ 5) eq
    · exact F.lowDistinct.ne (by decide : (3 : Fin 6) ≠ 5) eq

private theorem FourBlockPacking.separate_kept : Disjoint F.innerSet F.keptSet := by
  apply Set.disjoint_left.mpr
  rintro v inner ⟨i,kept,rfl⟩
  by_cases low : i.val < 2
  · exact F.terminal_low_off_inner low inner
  · have high : 2 ≤ i.val := by omega
    have degree := F.degree_terminal_high high
    rcases inner with (s|t)|⟨k,eq⟩
    · rcases singleton_region_cases F.first s with eq|port
      · exact degree (eq.symm ▸ F.first.degree)
      · exact kept (F.mem_lost.mpr ⟨high,Or.inl port⟩)
    · rcases singleton_region_cases F.second t with eq|port
      · exact degree (eq.symm ▸ F.second.degree)
      · exact kept (F.mem_lost.mpr ⟨high,Or.inr port⟩)
    · exact degree (eq ▸ F.depleted_low_degree k)

private theorem FourBlockPacking.four_lost_is_all (losses : (F.lost F.depleted).card = 4)
    {i : O} (hi : 2 ≤ i.val) : i ∈ F.lost F.depleted := by
  let high : Finset O := Finset.univ.filter fun i : O => 2 ≤ i.val
  have count : high.card = 4 := by decide
  have eq : F.lost F.depleted = high := Finset.eq_of_subset_of_card_le
    (fun _ li => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(F.mem_lost.mp li).1⟩)
    (by omega)
  exact eq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩

private theorem FourBlockPacking.ports_in_inner {v : V}
    (h : v ∈ singletonPorts F.first ∪ singletonPorts F.second) : v ∈ F.innerSet := by
  rcases h with ⟨i,_,eq⟩|⟨i,_,eq⟩
  · exact Or.inl (Or.inl ⟨i,eq⟩)
  · exact Or.inl (Or.inr ⟨i,eq⟩)

private theorem FourBlockPacking.covers_allocated (losses : (F.lost F.depleted).card = 4) :
    ∀ v, v ∈ F.innerSet ∨ v ∈ F.keptSet := by
  intro v
  rcases F.cover v with s|t|⟨i,rfl⟩|⟨i,rfl⟩
  · exact Or.inl (Or.inl (Or.inl s))
  · exact Or.inl (Or.inl (Or.inr t))
  · by_cases low : i.val < 2
    · exact Or.inl (Or.inr ⟨⟨i.val,low⟩,rfl⟩)
    · exact Or.inl (F.ports_in_inner (F.mem_lost.mp (F.four_lost_is_all losses (by omega))).2)
  · by_cases lost : i ∈ F.lost F.terminal
    · exact Or.inl (F.ports_in_inner (F.mem_lost.mp lost).2)
    · exact Or.inr ⟨i,lost,rfl⟩

/-- The singleton overlap is counted before any shared high is assigned. -/
noncomputable def FourBlockPacking.singletonOverlap : Finset V := by
  classical
  exact (Finset.univ.map F.first.f) ∩ (Finset.univ.map F.second.f)

private theorem FourBlockPacking.mem_singletonOverlap {v : V} :
    v ∈ F.singletonOverlap ↔ v ∈ labelRegion F.first.f ∧ v ∈ labelRegion F.second.f := by
  classical
  simp [FourBlockPacking.singletonOverlap,labelRegion]

/-- The full neighborhoods force their order plus the singleton overlap plus
the number of terminal losses to be exactly sixteen. No disjointness of the
singleton highs is assumed. -/
theorem FourBlockPacking.order_add_overlaps (losses : (F.lost F.depleted).card = 4) :
    Fintype.card V + F.singletonOverlap.card + (F.lost F.terminal).card = 16 := by
  classical
  let s := (Finset.univ : Finset (Fin 4)).map F.first.f
  let t := (Finset.univ : Finset (Fin 4)).map F.second.f
  let d := (Finset.univ : Finset (Fin 2)).map F.depletedLows
  let inner := s ∪ t ∪ d
  let retained := ((Finset.univ : Finset O) \ F.lost F.terminal).map F.terminal.f
  have memS (v : V) : v ∈ s ↔ v ∈ labelRegion F.first.f := by simp [s,labelRegion]
  have memT (v : V) : v ∈ t ↔ v ∈ labelRegion F.second.f := by simp [t,labelRegion]
  have memD (v : V) : v ∈ d ↔ v ∈ labelRegion F.depletedLows := by simp [d,labelRegion]
  have memI (v : V) : v ∈ inner ↔ v ∈ F.innerSet := by
    simp only [inner,Finset.mem_union,memS,memT,memD,FourBlockPacking.innerSet,Set.mem_union]
  have memR (v : V) : v ∈ retained ↔ v ∈ F.keptSet := by simp [retained,FourBlockPacking.keptSet]
  have dsep : Disjoint (s ∪ t) d := Finset.disjoint_left.mpr fun v h k =>
    Set.disjoint_left.mp F.low_off_singletons
      ((Finset.mem_union.mp h).imp (memS v).mp (memT v).mp) ((memD v).mp k)
  have distinct : Disjoint inner retained := Finset.disjoint_left.mpr fun v mi mr =>
    Set.disjoint_left.mp F.separate_kept ((memI v).mp mi) ((memR v).mp mr)
  have union : inner ∪ retained = Finset.univ := Finset.eq_univ_of_forall fun v =>
    Finset.mem_union.mpr ((F.covers_allocated losses v).imp (memI v).mpr (memR v).mpr)
  have total := Finset.card_union_of_disjoint distinct
  rw [union,Finset.card_univ] at total
  have sc : s.card = 4 := by simp [s]
  have tc : t.card = 4 := by simp [t]
  have dc : d.card = 2 := by simp [d]
  have both := Finset.card_union_add_card_inter s t
  have overlap : (s ∩ t).card = F.singletonOverlap.card := rfl
  rw [sc,tc,overlap] at both
  have ic : inner.card = (s ∪ t).card + d.card := Finset.card_union_of_disjoint dsep
  have rc : retained.card = 6 - (F.lost F.terminal).card := by
    rw [Finset.card_map,Finset.card_sdiff (Finset.subset_univ _),Finset.card_univ]
    rfl
  have bound := Finset.card_le_univ (F.lost F.terminal)
  have upper : (F.lost F.terminal).card ≤ 6 := by simpa using bound
  omega

private theorem FourBlockPacking.overlap_zero_of_disjoint
    (portsDisjoint : Disjoint (singletonPorts F.first) (singletonPorts F.second)) :
    F.singletonOverlap.card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro v mem
  have ⟨s,t⟩ := F.mem_singletonOverlap.mp mem
  exact Set.disjoint_left.mp (F.singleton_regions_disjoint portsDisjoint) s t

/-- Starting with the overlapping full neighborhoods, recover all
allocation data for the depleted-pair adapter. Only the four losses from
the first pair are supplied. The second pair loses at most one high by the order. -/
theorem FourBlockPacking.depleted_footprint_of_order
    (portsDisjoint : Disjoint (singletonPorts F.first) (singletonPorts F.second))
    (losses : (F.lost F.depleted).card = 4)
    (order : 15 ≤ Fintype.card V) :
    ∃ (loss : Bool) (A : DepletedFootprint G loss),
      A.inner 3 = F.first.f 3 ∧ (loss = true ↔ (F.lost F.terminal).card = 1) := by
  have balance := F.order_add_overlaps losses
  have empty := F.overlap_zero_of_disjoint portsDisjoint
  obtain ⟨loss,Q,flag,region,edges,degree⟩ := terminal_pair_of_at_most_one_loss F.terminal.f
    (F.lost F.terminal) (by omega) (fun _ h => (F.mem_lost.mp h).1)
    F.terminal.edges F.terminal.degree
  have assignment (j : Fin 4) :
      F.depletedHighs j ∈ singletonPorts F.first ∪ singletonPorts F.second := by
    have high : 2 ≤ (j.natAdd 2).val := by simp
    exact (F.mem_lost.mp (F.four_lost_is_all losses high)).2
  have sep : Disjoint F.innerSet (terminalRegion Q loss) := region.symm ▸ F.separate_kept
  have full (v : V) : v ∈ F.innerSet ∨ v ∈ terminalRegion Q loss :=
    (F.covers_allocated losses v).imp id (fun h => region.symm ▸ h)
  obtain ⟨A,loose,_⟩ := depleted_footprint_of_blocks F.first F.second F.depletedLows
    (F.singleton_regions_disjoint portsDisjoint) F.low_off_singletons F.looseFirst F.looseSecond
    (F.depleted.edges 0 1 (by decide)) F.depleted_low_degree F.depletedHighs assignment
    ⟨F.depleted.edges 0 2 (by decide),F.depleted.edges 0 3 (by decide),F.depleted.edges 2 3 (by decide)⟩
    ⟨F.depleted.edges 1 4 (by decide),F.depleted.edges 1 5 (by decide),F.depleted.edges 4 5 (by decide)⟩
    Q edges degree sep full
  exact ⟨loss,A,loose,flag⟩

/-- Eliminate the four-loss two-singleton branch at the original crossing
interface. The hypothesis of order at least fifteen suffices. -/
theorem FourBlockPacking.hamiltonian_of_four_losses [DecidableEq V]
    (portsDisjoint : Disjoint (singletonPorts F.first) (singletonPorts F.second))
    (losses : (F.lost F.depleted).card = 4) (order : 15 ≤ Fintype.card V)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (cross : CrossingBetweenSurvivingEdges G) :
    (Fintype.card V = 15 ∨ Fintype.card V = 16) ∧
      ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian := by
  obtain ⟨loss,A,loose,_⟩ := F.depleted_footprint_of_order portsDisjoint losses order
  have high : G.degree (A.inner 3) ≠ 3 :=
    loose.symm ▸ F.degree_first_high (show F.first.f 3 ∈ singletonPorts F.first from ⟨3,rfl,rfl⟩)
  obtain ⟨n,p⟩ := depleted_footprint_order_and_path A
    (edgeReach_iff_crossing_between_surviving_edges.mpr cross)
    (degree_of_small_deletion_preconnected (by omega) below _) high
  exact ⟨by cases loss <;> simp_all,pathOn_univ_iff_hamiltonian_walk.mp p⟩

/-- At order sixteen the disjointness required by the splice is forced
by the covered graph and the four losses from the first pair. -/
theorem FourBlockPacking.hamiltonian_of_four_losses_at_sixteen [DecidableEq V]
    (losses : (F.lost F.depleted).card = 4) (order : Fintype.card V = 16)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (cross : CrossingBetweenSurvivingEdges G) :
    ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian := by
  have balance := F.order_add_overlaps losses
  have zero : F.singletonOverlap.card = 0 := by omega
  have empty := Finset.card_eq_zero.mp zero
  have dis : Disjoint (singletonPorts F.first) (singletonPorts F.second) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨i,_,rfl⟩ ⟨j,_,eq⟩
    have mem := F.mem_singletonOverlap.mpr ⟨⟨i,rfl⟩,⟨j,eq⟩⟩
    simp [empty] at mem
  exact (F.hamiltonian_of_four_losses dis losses (by omega) below cross).2

#print axioms FourBlockPacking.lost_map_eq_forbidden
#print axioms FourBlockPacking.order_add_overlaps
#print axioms FourBlockPacking.depleted_footprint_of_order
#print axioms FourBlockPacking.hamiltonian_of_four_losses
#print axioms FourBlockPacking.hamiltonian_of_four_losses_at_sixteen

end Graffiti199Depleted
