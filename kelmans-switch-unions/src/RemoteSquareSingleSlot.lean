import RemoteSquareRankFactor

namespace KelmansCactus.AtomicBridge.RemoteSquareSingleSlot
open SimpleGraph
open scoped Sym2
open Finset
open RemoteSquareConvergence RemoteSquareEvenScaffold
open RemoteSquareRankFactor (closed_tail_membership TwoRegular)
open RemoteGapRunPacking (joined_at_factor)
open SquareCap (HasFactor)
variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- Every component of a finite degree-two graph has a spanning run ending at its
prescribed anchor. This is the exact data needed for an omitted-slot graft. -/
theorem anchored_run (G : SimpleGraph V) [DecidableRel G.Adj]
    (regular : ∀ x,G.degree x=2) (a : V) :
    ∃ L : List V,L.Nodup ∧ L.Chain' G.Adj ∧ L.getLast?=some a ∧
      ∀ x,x∈L ↔ G.Reachable a x := by
  have pos : 0<G.degree a := by rw [regular]; decide
  obtain ⟨b,bm⟩ := Finset.card_pos.mp pos
  have adj : G.Adj a b := (SimpleGraph.mem_neighborFinset _ _ _).mp bm
  have alt := even_degree_alternate G (fun x=>by rw [regular]; decide) adj
  obtain ⟨u,p,pc,ep⟩ := SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp ⟨adj,alt⟩
  have am : a∈p.support := p.fst_mem_support_of_mem_edges ep
  let c := p.rotate am
  have cc : c.IsCycle := pc.rotate am
  have closed {x y : V} (xmem : x∈c.support) (xy : G.Adj x y) : y∈c.support := by
    let q := c.rotate xmem
    have qc : q.IsCycle := cc.rotate xmem
    have supmap {z : V} (hz : z∈q.support) : z∈c.support :=
      (closed_tail_membership cc.not_nil).mpr
        ((c.support_rotate xmem).mem_iff.mp ((closed_tail_membership qc.not_nil).mp hz))
    have aa : G.Adj x q.snd := q.adj_snd qc.not_nil
    have bb : G.Adj x q.penultimate := (q.adj_penultimate qc.not_nil).symm
    have ne : q.snd≠q.penultimate := qc.snd_ne_penultimate
    have allN : G.neighborFinset x = {q.snd,q.penultimate} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro z zm
        simp only [Finset.mem_insert,Finset.mem_singleton] at zm
        rcases zm with rfl|rfl
        · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr aa
        · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr bb
      · rw [SimpleGraph.card_neighborFinset_eq_degree,regular]
        simp [ne]
    have m : y ∈ G.neighborFinset x := (SimpleGraph.mem_neighborFinset _ _ _).mpr xy
    rw [allN] at m
    simp only [Finset.mem_insert,Finset.mem_singleton] at m
    rcases m with rfl|rfl
    · exact supmap (q.getVert_mem_support 1)
    · exact supmap (q.getVert_mem_support (q.length-1))
  have non : c.support.tail ≠ [] := by
    intro h
    have m := c.end_mem_tail_support cc.not_nil
    rw [h] at m
    exact List.not_mem_nil m
  refine ⟨c.support.tail,cc.support_nodup,c.chain'_adj_support.tail,?_,?_⟩
  · rw [List.getLast?_eq_getLast_of_ne_nil non, List.getLast_tail, c.getLast_support]
  · intro x
    rw [←closed_tail_membership cc.not_nil]
    constructor
    · intro h
      exact (c.takeUntil x h).reachable
    · intro reach
      rw [SimpleGraph.reachable_iff_reflTransGen] at reach
      induction reach with
      | refl => exact c.start_mem_support
      | tail _ e ih => exact closed ih e

abbrev old (G : SimpleGraph (Option V)) : SimpleGraph V := G.comap Option.some

omit [Fintype V] [DecidableEq V] in
theorem old_pair_cover (G : SimpleGraph (Option V)) (a b : V)
    (slots : ∀ v, G.Adj none (some v) ↔ v=a ∨ v=b)
    (con : G.Preconnected) (v : V) :
    (old G).Reachable a v ∨ (old G).Reachable b v := by
  let P : Option V → Prop := fun
    | none => True
    | some z => (old G).Reachable a z ∨ (old G).Reachable b z
  have step (x y : Option V) (hx : P x) (e : G.Adj x y) : P y := by
    rcases y with (_|y)
    · exact True.intro
    rcases x with (_|x)
    · rcases (slots y).mp e with rfl|rfl
      · exact Or.inl (SimpleGraph.Reachable.refl _)
      · exact Or.inr (SimpleGraph.Reachable.refl _)
    · rcases hx with h|h
      · exact Or.inl (h.trans (SimpleGraph.Adj.reachable (G:=old G) e))
      · exact Or.inr (h.trans (SimpleGraph.Adj.reachable (G:=old G) e))
  have path := con none (some v)
  rw [SimpleGraph.reachable_iff_reflTransGen] at path
  have go : ∀ y, Relation.ReflTransGen G.Adj none y → P y := by
    intro y p
    induction p with
    | refl => exact True.intro
    | tail _ e ih => exact step _ _ ih e
  exact go _ path

/-- Two disjoint old runs (one may be empty), ending at slot neighbors, can be
reversed and joined to an actual spanning factor. -/
theorem factor_of_slot_runs (G : SimpleGraph (Option V)) (L R : List V)
    (ln : L.Nodup) (rn : R.Nodup) (lc : L.Chain' (old G).Adj) (rc : R.Chain' (old G).Adj)
    (lastL : ∀ z∈L.getLast?, G.Adj (some z) none)
    (lastR : ∀ z∈R.getLast?, G.Adj none (some z))
    (apart : ∀ x∈L,x∉R) (cover : ∀ x,x∈L ∨ x∈R)
    (size : 3∣Fintype.card (Option V)) : HasFactor G := by
  let LL := L.map some
  let RR := R.reverse.map some
  have lnod : LL.Nodup := List.Nodup.map (Option.some_injective V) ln
  have rnod : RR.Nodup := List.Nodup.map (Option.some_injective V) (List.nodup_reverse.mpr rn)
  have ll : LL.Chain' G.Adj := (List.chain'_map _).mpr lc
  have rr : RR.Chain' G.Adj := (List.chain'_map _).mpr
    (List.chain'_reverse.mpr (rc.imp fun _ _ h=>h.symm))
  have lend : ∀ x∈LL.getLast?, G.Adj x none := by
    intro x h
    rw [List.getLast?_map] at h
    cases eq : L.getLast? with
    | none => simp [eq] at h
    | some z =>
      rw [eq] at h
      have e : some z=x := Option.some.inj h
      subst x
      exact lastL z (by simp [eq])
  have rstart : ∀ x∈RR.head?, G.Adj none x := by
    intro x h
    rw [List.head?_map,List.head?_reverse] at h
    cases eq : R.getLast? with
    | none => simp [eq] at h
    | some z =>
      rw [eq] at h
      have e : some z=x := Option.some.inj h
      subst x
      exact lastR z (by simp [eq])
  have la : none∉LL.toFinset := by simp [LL]
  have ra : none∉RR.toFinset := by simp [RR]
  have disj : Disjoint LL.toFinset RR.toFinset := by
    rw [Finset.disjoint_left]
    rintro (_|x) hm hr
    · exact la hm
    · have a : x∈L := by simpa [LL] using hm
      have b : x∈R := by simpa [RR] using hr
      exact apart x a b
  have all : (LL.toFinset∪RR.toFinset)∪{none}=Finset.univ := by
    ext x
    cases x with
    | none => simp
    | some x => simpa [LL,RR] using cover x
  have count : LL.length+RR.length+1=Fintype.card (Option V) := by
    rw [←Finset.card_univ,←all,
      Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr (by
        intro h
        exact (Finset.mem_union.mp h).elim la ra)),
      Finset.card_union_of_disjoint disj, Finset.card_singleton,
      List.toFinset_card_of_nodup lnod,List.toFinset_card_of_nodup rnod]
  rw [←count] at size
  have factor := joined_at_factor LL RR none lnod rnod ll rr lend rstart disj la ra size
  rwa [all] at factor

/-- The entire connected rank is factorable when the only extra slot is one
vertex adjacent to two chosen contacts of an old degree-two graph. -/
theorem factor_connected_one_slot (G : SimpleGraph (Option V)) (a b : V)
    (slots : ∀ v,G.Adj none (some v) ↔ v=a ∨ v=b)
    (regular : TwoRegular (old G)) (con : G.Preconnected)
    (size : 3∣Fintype.card (Option V)) : HasFactor G := by
  obtain ⟨inst,degree⟩ := regular
  letI := inst
  obtain ⟨L,ln,lc,lend,memL⟩ := anchored_run (old G) degree a
  have l2 : ∀ z∈L.getLast?,G.Adj (some z) none := by
    intro z h
    rw [lend] at h
    have : a=z := Option.some.inj h
    subst z
    exact ((slots a).mpr (Or.inl rfl)).symm
  by_cases ok : (old G).Reachable a b
  · have all : ∀ z,z∈L ∨ z∈([] : List V) := by
      intro z
      refine Or.inl ((memL z).mpr ?_)
      rcases old_pair_cover G a b slots con z with h|h
      · exact h
      · exact ok.trans h
    exact factor_of_slot_runs G L [] ln (by simp) lc (by simp) l2
      (by simp) (by simp) all size
  · obtain ⟨R,rn,rc,rend,memR⟩ := anchored_run (old G) degree b
    have r2 : ∀ z∈R.getLast?,G.Adj none (some z) := by
      intro z h
      rw [rend] at h
      have : b=z := Option.some.inj h
      subst z
      exact (slots b).mpr (Or.inr rfl)
    have apart (x : V) (xl : x∈L) (xr : x∈R) : False :=
      ok (((memL x).mp xl).trans ((memR x).mp xr).symm)
    have all (x : V) : x∈L ∨ x∈R := 
      (old_pair_cover G a b slots con x).elim (fun h=>Or.inl ((memL x).mpr h))
        (fun h=>Or.inr ((memR x).mpr h))
    exact factor_of_slot_runs G L R ln rn lc rc l2 r2 apart all size


omit [Fintype V] [DecidableEq V] in
theorem old_alternate_lifts (G : SimpleGraph (Option V)) {a b : V}
    (r : ((old G).deleteEdges {s(a,b)}).Reachable a b) :
    (G.deleteEdges {s(some a,some b)}).Reachable (some a) (some b) := by
  let f : (old G).deleteEdges {s(a,b)} →g G.deleteEdges {s(some a,some b)} :=
    ⟨some, by
      intro x y h
      obtain ⟨e,ne⟩ := SimpleGraph.deleteEdges_adj.mp h
      refine SimpleGraph.deleteEdges_adj.mpr ⟨e,?_⟩
      intro bad
      apply ne
      simpa only [Set.mem_singleton_iff,Sym2.eq_iff,Option.some.injEq] using bad⟩
  exact r.map f

/-- A genuine one-omitted-slot version of the square convergence factor
criterion. Gate edges lie on old vertices. The slot keeps its two contacts
throughout, but need not be used as a center in the final factor. -/
theorem square_rank_one_slot [DecidableEq I]
    (G B : SimpleGraph (Option V)) (gates : I→Quad (Option V)) (a b : V)
    (sub : unionNetwork B gates ≤ G)
    (reg : ∀ s, TwoRegular (old (network B gates s)))
    (slot : ∀ s v, (network B gates s).Adj none (some v) ↔ v=a ∨ v=b)
    (oldGates : ∀ i s x y, (gates i).adj s x y → ∃ u v : V,x=some u ∧ y=some v)
    (con : (unionNetwork B gates).Preconnected)
    (size : 3∣Fintype.card (Option V)) (start : I→Bool) :
    ∃ final, HasFactor (network B gates final) ∧ HasFactor G := by
  have ok : CanBypass B gates := by
    apply bypass_of_alternate
    intro s i
    let X := network B gates s
    let q := (gates i).orient (s i)
    obtain ⟨inst,deg⟩ := reg s
    letI := inst
    have alt (x y : Option V) (h : (gates i).adj (s i) x y) :
        (X.deleteEdges {s(x,y)}).Reachable x y := by
      obtain ⟨u,v,rfl,rfl⟩ := oldGates i (s i) x y h
      have e : (old X).Adj u v := Or.inr ⟨i,h⟩
      exact old_alternate_lifts X (even_degree_alternate _ (fun z=>by rw [deg]; decide) e)
    exact ⟨alt q.a q.b (((gates i).adj_orient_old (s i) _ _).mpr (Or.inl (Or.inl ⟨rfl,rfl⟩))),
      alt q.c q.d (((gates i).adj_orient_old (s i) _ _).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩)))⟩
  obtain ⟨f,_,all⟩ := square_convergence B gates ok start
  have hf : HasFactor (network B gates f) :=
    factor_connected_one_slot _ a b (slot f) (reg f) (fun x y=>(all x y).mpr (con x y)) size
  obtain ⟨pack,legal,apart,covers⟩ := hf
  exact ⟨f,⟨pack,legal,apart,covers⟩,pack,fun R m=>by
    obtain ⟨ct,c,cm,adjs⟩ := legal R m
    exact ⟨ct,c,cm,fun x xm ne=>sub ((network_le_union B gates f) (adjs x xm ne))⟩,apart,covers⟩

#print axioms square_rank_one_slot
#print axioms anchored_run
#print axioms factor_connected_one_slot
end KelmansCactus.AtomicBridge.RemoteSquareSingleSlot
