import FourBlockIntegration
import OneSharedCertificate

open private appendDisjoint appendDisjoint_region from NeighborhoodAdapter
open private three_names_exhaust_neighbors from DepletedFootprint
open private FourBlockPacking.innerSet FourBlockPacking.keptSet FourBlockPacking.mem_singletonOverlap
  FourBlockPacking.low_off_singletons FourBlockPacking.depletedLows FourBlockPacking.depletedHighs
  FourBlockPacking.four_lost_is_all FourBlockPacking.degree_first_high FourBlockPacking.degree_second_high
  FourBlockPacking.ports_in_inner FourBlockPacking.separate_kept FourBlockPacking.covers_allocated
  singleton_region_cases pair_low_cases from FourBlockIntegration

namespace Graffiti199Depleted

open SimpleGraph Graffiti199K2.NearPacking.Depleted OneShared

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
variable (F : FourBlockPacking G)

private theorem overlap_is_high {v : V} (s : v ∈ labelRegion F.first.f)
    (t : v ∈ labelRegion F.second.f) : v ∈ singletonPorts F.first ∧ v ∈ singletonPorts F.second := by
  rcases singleton_region_cases F.first s with rfl|hs
  · rcases singleton_region_cases F.second t with eq|ht
    · exact (F.lowDistinct.ne (by decide : (0 : Fin 6) ≠ 1) eq).elim
    · exact (FourBlockPacking.degree_second_high F ht F.first.degree).elim
  · rcases singleton_region_cases F.second t with rfl|ht
    · exact (FourBlockPacking.degree_first_high F hs F.second.degree).elim
    · exact ⟨hs,ht⟩

private theorem core_labelling {i j : Fin 4} (hi : singletonHigh i = true) (hj : singletonHigh j = true)
    (eq : F.first.f i = F.second.f j) (unique : F.singletonOverlap = {F.first.f i}) :
    ∃ f : J ↪ V, labelRegion f = FourBlockPacking.innerSet F ∧
      (∀ k, f (leftLabel k) = F.first.f k) ∧ (∀ k, f (rightLabel i j k) = F.second.f k) ∧
      f 7 = F.depleted.f 0 ∧ f 8 = F.depleted.f 1 := by
  obtain ⟨freshInj,coversFresh,same,shift⟩ := right_labels i j hi hj
  let t := (⟨freshRight j,freshInj⟩ : Fin 3 ↪ Fin 4).trans F.second.f
  have away : Disjoint (labelRegion F.first.f) (labelRegion t) := by
    apply Set.disjoint_left.mpr
    rintro v s ⟨k,rfl⟩
    have both := (FourBlockPacking.mem_singletonOverlap F).mpr ⟨s,⟨freshRight j k,rfl⟩⟩
    have h := Finset.mem_singleton.mp (unique ▸ both)
    exact ((coversFresh _).mp ⟨k,rfl⟩) (F.second.f.injective (h.trans eq))
  let st := appendDisjoint F.first.f t away
  have stRegion : labelRegion st = labelRegion F.first.f ∪ labelRegion F.second.f := by
    rw [appendDisjoint_region]
    ext v
    constructor
    · rintro (s|⟨k,rfl⟩)
      · exact Or.inl s
      · exact Or.inr ⟨freshRight j k,rfl⟩
    · rintro (s|⟨k,rfl⟩)
      · exact Or.inl s
      · by_cases e : k = j
        · exact Or.inl ⟨i,eq.trans (congrArg F.second.f e).symm⟩
        · obtain ⟨a,h⟩ := (coversFresh k).mpr e
          exact Or.inr ⟨a,congrArg F.second.f h⟩
  let f : J ↪ V := appendDisjoint st (FourBlockPacking.depletedLows F)
    (stRegion.symm ▸ FourBlockPacking.low_off_singletons F)
  have regions : labelRegion f = FourBlockPacking.innerSet F := by
    rw [appendDisjoint_region,stRegion]
    rfl
  have left (k : Fin 4) : f (leftLabel k) = F.first.f k := by
    change f ((k.castAdd 3).castAdd 2) = F.first.f k
    exact (Fin.append_left st (FourBlockPacking.depletedLows F) _).trans
      (Fin.append_left F.first.f t k)
  have right (k : Fin 4) : f (rightLabel i j k) = F.second.f k := by
    by_cases e : k = j
    · subst k
      rw [same,left,eq]
    · obtain ⟨a,rfl⟩ := (coversFresh k).mpr e
      rw [shift]
      exact (Fin.append_left st (FourBlockPacking.depletedLows F) _).trans
        (Fin.append_right F.first.f t a)
  exact ⟨f,regions,left,right,rfl,rfl⟩

omit [Fintype V] [DecidableRel G.Adj] in
private theorem reorder_core_pair (f : J ↪ V) {a b c d : I} (k : J)
    (move : Graffiti199K2.NearPacking.Depleted.same a b c d) (a7 : a ≠ 7) (b7 : b ≠ 7)
    (ka : G.Adj (f k) (f (a.castAdd 1))) (kb : G.Adj (f k) (f (b.castAdd 1)))
    (ab : G.Adj (f (a.castAdd 1)) (f (b.castAdd 1))) :
    c ≠ 7 ∧ d ≠ 7 ∧ G.Adj (f k) (f (c.castAdd 1)) ∧ G.Adj (f k) (f (d.castAdd 1)) ∧
      G.Adj (f (c.castAdd 1)) (f (d.castAdd 1)) := by
  rcases move with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨a7,b7,ka,kb,ab⟩
  · exact ⟨b7,a7,kb,ka,ab.symm⟩

/-- A shared singleton high leaves a nine-vertex core. Any singleton
high can end a path spanning this core. -/
theorem FourBlockPacking.path_to_high_with_one_overlap (losses : (F.lost F.depleted).card = 4)
    (shared : F.singletonOverlap.card = 1) {v : V}
    (hv : v ∈ singletonPorts F.first ∪ singletonPorts F.second) :
    ∃ p : PathOn G (FourBlockPacking.innerSet F), p.last = v := by
  obtain ⟨u,unique⟩ := Finset.card_eq_one.mp shared
  have there := (FourBlockPacking.mem_singletonOverlap F).mp (show u ∈ F.singletonOverlap by
    rw [unique]; simp)
  obtain ⟨⟨i,hi,iu⟩,⟨j,hj,ju⟩⟩ := overlap_is_high F there.1 there.2
  obtain ⟨f,region,l,r,p0,p1⟩ := core_labelling F hi hj (iu.trans ju.symm) (iu.symm ▸ unique)
  have atHigh {w : V} (hw : w ∈ singletonPorts F.first ∪ singletonPorts F.second) :
      ∃ k : J, coreHigh k = true ∧ f k = w := by
    rcases hw with ⟨k,kh,e⟩|⟨k,kh,e⟩
    · exact ⟨leftLabel k,left_high k kh,(l k).trans e⟩
    · exact ⟨rightLabel i j k,right_high i j k hi hj kh,(r k).trans e⟩
  let d := FourBlockPacking.depletedHighs F
  have names (q : Fin 4) : ∃ w : I, high w = true ∧ w ≠ 7 ∧ f (w.castAdd 1) = d q := by
    have whigh : 2 ≤ (q.natAdd 2).val := by simp
    obtain ⟨k,kh,key⟩ := atHigh ((F.mem_lost.mp (FourBlockPacking.four_lost_is_all F losses whigh)).2)
    obtain ⟨w,wh,w7,e⟩ := high_preimage k kh
    exact ⟨w,wh,w7,(congrArg f e).trans key⟩
  obtain ⟨a,ah,a7,ae⟩ := names 0
  obtain ⟨b,bh,b7,be⟩ := names 1
  obtain ⟨c,ch,c7,ce⟩ := names 2
  obtain ⟨d',dh,d7,de⟩ := names 3
  have different {q t : Fin 4} {x y : I} (ne : q ≠ t) (hx : f (x.castAdd 1) = d q)
      (hy : f (y.castAdd 1) = d t) : x ≠ y := fun e =>
    d.injective.ne ne (hx.symm.trans (e ▸ hy))
  obtain ⟨row,ma,mb⟩ := covered a b c d' ah bh ch dh
    (different (by decide) ae be) (different (by decide) ae ce) (different (by decide) ae de)
    (different (by decide) be ce) (different (by decide) be de) (different (by decide) ce de)
  obtain ⟨ar,br,ea,eb,eab⟩ := reorder_core_pair (G := G) f 7 ma a7 b7
    (by rw [p0,ae]; exact F.depleted.edges 0 2 (by decide))
    (by rw [p0,be]; exact F.depleted.edges 0 3 (by decide))
    (by rw [ae,be]; exact F.depleted.edges 2 3 (by decide))
  obtain ⟨cr,dr,ec,ed,ecd⟩ := reorder_core_pair (G := G) f 8 mb c7 d7
    (by rw [p1,ce]; exact F.depleted.edges 1 4 (by decide))
    (by rw [p1,de]; exact F.depleted.edges 1 5 (by decide))
    (by rw [ce,de]; exact F.depleted.edges 4 5 (by decide))
  have required (x y : J) (h : (x,y) ∈ coreEdges i j row) : G.Adj (f x) (f y) := by
    simp only [coreEdges,List.mem_append] at h
    rcases h with (h|h)|h
    · obtain ⟨⟨u,w⟩,mem,e⟩ := List.mem_map.mp h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
      simpa only [edgeMap,l] using F.first.edges u w mem
    · obtain ⟨⟨u,w⟩,mem,e⟩ := List.mem_map.mp h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
      simpa only [edgeMap,r] using F.second.edges u w mem
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with e|e|e|e|e|e|e <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
      · rw [p0,p1]
        exact F.depleted.edges 0 1 (by decide)
      · exact ea
      · exact eb
      · exact eab
      · exact ec
      · exact ed
      · exact ecd
  have banned (x y : J) (h : (x,y) ∈ coreBans i j) : ¬ G.Adj (f x) (f y) := by
    rcases List.mem_append.mp h with h|h
    · obtain ⟨⟨u,w⟩,mem,e⟩ := List.mem_map.mp h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
      simp only [looseBans,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with mem|mem <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj mem
      · simpa only [edgeMap,l] using F.first.looseNonedge
      · simpa only [edgeMap,l] using F.looseFirst
    · obtain ⟨⟨u,w⟩,mem,e⟩ := List.mem_map.mp h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
      simp only [looseBans,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with mem|mem <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj mem
      · simpa only [edgeMap,r] using F.second.looseNonedge
      · simpa only [edgeMap,r] using F.looseSecond
  obtain ⟨k,kh,kv⟩ := atHigh hv
  obtain ⟨p,last⟩ := core_path_ending_at_high f hi hj ⟨ar,br,cr,dr⟩ required banned kh
  rw [← region]
  exact ⟨p,last.trans kv⟩

private theorem pair_low_stays (P : FullPair G) {i : O} (lo : i.val < 2) {v : V}
    (edge : G.Adj (P.f i) v) : v ∈ labelRegion P.f := by
  rcases pair_low_cases i lo with rfl|rfl
  · obtain ⟨j,_,eq⟩ := three_names_exhaust_neighbors P.f (by decide) (by decide) (by decide)
      (P.degree 0 (by decide)) (P.edges 0 1 (by decide)) (P.edges 0 2 (by decide))
      (P.edges 0 3 (by decide)) v edge
    exact ⟨j,eq⟩
  · obtain ⟨j,_,eq⟩ := three_names_exhaust_neighbors P.f (by decide) (by decide) (by decide)
      (P.degree 1 (by decide)) (P.edges 0 1 (by decide)).symm (P.edges 1 4 (by decide))
      (P.edges 1 5 (by decide)) v edge
    exact ⟨j,eq⟩

/-- The shared singleton residue at order fifteen also gives a
Hamiltonian path. The terminal pair is intact by the overlap identity. -/
theorem FourBlockPacking.hamiltonian_with_one_overlap [DecidableEq V]
    (losses : (F.lost F.depleted).card = 4) (order : Fintype.card V = 15)
    (shared : F.singletonOverlap.card = 1) (cross : CrossingBetweenSurvivingEdges G) :
    ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian := by
  have balance := F.order_add_overlaps losses
  have empty : F.lost F.terminal = ∅ := Finset.card_eq_zero.mp (by omega)
  have kept : terminalRegion F.terminal.f false = FourBlockPacking.keptSet F := by
    ext v
    simp [terminalKept,FourBlockPacking.keptSet,empty]
  have pInner (i : O) : F.depleted.f i ∈ FourBlockPacking.innerSet F := by
    by_cases lo : i.val < 2
    · exact Or.inr ⟨⟨i.val,lo⟩,rfl⟩
    · exact FourBlockPacking.ports_in_inner F
        (F.mem_lost.mp (FourBlockPacking.four_lost_is_all F losses (by omega))).2
  have qKept (i : O) : F.terminal.f i ∈ FourBlockPacking.keptSet F := ⟨i,by simp [empty],rfl⟩
  have qOut (i : O) : F.terminal.f i ∉ FourBlockPacking.innerSet F := fun h =>
    Set.disjoint_left.mp (FourBlockPacking.separate_kept F) h (qKept i)
  obtain ⟨x,xIn,y,yOut,_,_,xy⟩ := cross ∅ (by simp) (FourBlockPacking.innerSet F)
    ⟨_,pInner 0,_,pInner 1,by simp,by simp,F.depleted.edges 0 1 (by decide)⟩
    ⟨_,qOut 0,_,qOut 1,by simp,by simp,F.terminal.edges 0 1 (by decide)⟩
  have highX : x ∈ singletonPorts F.first ∪ singletonPorts F.second := by
    rcases xIn with (⟨i,rfl⟩|⟨i,rfl⟩)|⟨i,rfl⟩
    · exact Or.inl ⟨i,F.first.outgoing_high (fun h => yOut (Or.inl (Or.inl h))) xy,rfl⟩
    · exact Or.inr ⟨i,F.second.outgoing_high (fun h => yOut (Or.inl (Or.inr h))) xy,rfl⟩
    · obtain ⟨j,eq⟩ := pair_low_stays F.depleted (i := i.castAdd 4) i.isLt xy
      exact (yOut (eq ▸ pInner j)).elim
  obtain ⟨i,_,rfl⟩ := (FourBlockPacking.covers_allocated F losses y).resolve_left yOut
  have highY : terminalHigh i = true := by
    have noLow : ¬ i.val < 2 := by
      intro lo
      obtain ⟨j,eq⟩ := pair_low_stays F.terminal lo xy.symm
      exact Set.disjoint_left.mp (FourBlockPacking.separate_kept F) xIn (eq ▸ qKept j)
    fin_cases i <;> first | rfl | exact (noLow (by decide)).elim
  obtain ⟨p,last⟩ := F.path_to_high_with_one_overlap losses shared highX
  obtain ⟨q,first⟩ := terminal_path_from_high F.terminal.f false F.terminal.edges rfl highY
  have sep : Disjoint (FourBlockPacking.innerSet F) (terminalRegion F.terminal.f false) :=
    kept.symm ▸ FourBlockPacking.separate_kept F
  have full : FourBlockPacking.innerSet F ∪ terminalRegion F.terminal.f false = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    exact (FourBlockPacking.covers_allocated F losses v).imp id (fun h => kept.symm ▸ h)
  exact pathOn_univ_iff_hamiltonian_walk.mp ⟨full ▸ p.join q sep (last.symm ▸ first.symm ▸ xy)⟩

/-- Full integration of the four-loss layout at order at least fifteen.
At order fifteen, the unique singleton overlap is handled by its own path table. -/
theorem FourBlockPacking.hamiltonian_of_four_losses_of_order [DecidableEq V]
    (losses : (F.lost F.depleted).card = 4) (order : 15 ≤ Fintype.card V)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (cross : CrossingBetweenSurvivingEdges G) :
    (Fintype.card V = 15 ∨ Fintype.card V = 16) ∧
      ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian := by
  have balance := F.order_add_overlaps losses
  by_cases empty : F.singletonOverlap.card = 0
  · have dis : Disjoint (singletonPorts F.first) (singletonPorts F.second) := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨i,_,rfl⟩ ⟨j,_,eq⟩
      have mem := (FourBlockPacking.mem_singletonOverlap F).mpr ⟨⟨i,rfl⟩,⟨j,eq⟩⟩
      simp [Finset.card_eq_zero.mp empty] at mem
    exact F.hamiltonian_of_four_losses dis losses order below cross
  · have size : Fintype.card V = 15 := by omega
    exact ⟨Or.inl size,F.hamiltonian_with_one_overlap losses size (by omega) cross⟩

/-- In the original reduction the allocation is expressed as a set of
vertices. Its four-loss branch contradicts the nontraceability certificate. -/
theorem FourBlockPacking.excludes_four_forbidden_highs [DecidableEq V]
    (forbidden : Finset V) (count : forbidden.card = 4)
    (highOnly : ∀ v ∈ forbidden, v ∈ pairPorts F.depleted)
    (membership : ∀ v ∈ pairPorts F.depleted,
      v ∈ forbidden ↔ v ∈ singletonPorts F.first ∪ singletonPorts F.second)
    (order : 15 ≤ Fintype.card V)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (cross : CrossingBetweenSurvivingEdges G)
    (nontraceable : ¬ ∃ a b : V, ∃ w : G.Walk a b, w.IsHamiltonian) : False := by
  have loss : (F.lost F.depleted).card = 4 := by
    rw [← Finset.card_map F.depleted.f, F.lost_map_eq_forbidden F.depleted forbidden highOnly membership]
    exact count
  exact nontraceable (F.hamiltonian_of_four_losses_of_order loss order below cross).2

#print axioms FourBlockPacking.path_to_high_with_one_overlap
#print axioms FourBlockPacking.hamiltonian_with_one_overlap
#print axioms FourBlockPacking.hamiltonian_of_four_losses_of_order
#print axioms FourBlockPacking.excludes_four_forbidden_highs

end Graffiti199Depleted
