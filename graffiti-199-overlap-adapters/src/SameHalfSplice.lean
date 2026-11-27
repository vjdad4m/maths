import SameHalfAccess

open private three_names_exhaust_neighbors from DepletedFootprint
open private InternallyIndependent independent_pair independent_union match_endpoint_types
  from SplitTipsSplice

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The paired block and the singleton that shares two tips with one of its halves. -/
structure MergedSameHalf (G : SimpleGraph V) [DecidableRel G.Adj] where
  f : Fin 8 ↪ V
  edges : ∀ i j, (i,j) ∈ sameHalfEdges → G.Adj (f i) (f j)
  degree : ∀ i ∈ ([0,4,5] : List (Fin 8)), G.degree (f i) = 3

private theorem MergedSameHalf.root_neighbors (M : MergedSameHalf G)
    (v : V) (adj : G.Adj (M.f 0) v) : ∃ j ∈ ([1,2,3] : List (Fin 8)), M.f j = v :=
  three_names_exhaust_neighbors M.f (by decide) (by decide) (by decide)
    (M.degree 0 (by decide)) (M.edges 0 1 (by decide)) (M.edges 0 2 (by decide))
    (M.edges 0 3 (by decide)) v adj

private theorem MergedSameHalf.low_stays (M : MergedSameHalf G) {i : Fin 8}
    (low : i = 0 ∨ i = 4 ∨ i = 5) {v : V} (adj : G.Adj (M.f i) v) :
    v ∈ labelRegion M.f := by
  rcases low with rfl|rfl|rfl
  · obtain ⟨j,_,eq⟩ := M.root_neighbors v adj
    exact ⟨j,eq⟩
  · obtain ⟨j,_,eq⟩ :=
      three_names_exhaust_neighbors M.f (by decide) (by decide) (by decide)
        (M.degree 4 (by decide)) (M.edges 4 5 (by decide)) (M.edges 4 1 (by decide))
        (M.edges 4 2 (by decide)) v adj
    exact ⟨j,eq⟩
  · obtain ⟨j,_,eq⟩ :=
      three_names_exhaust_neighbors M.f (by decide) (by decide) (by decide)
        (M.degree 5 (by decide)) (M.edges 4 5 (by decide)).symm (M.edges 5 6 (by decide))
        (M.edges 5 7 (by decide)) v adj
    exact ⟨j,eq⟩

private theorem MergedSameHalf.sealed_pair (M : MergedSameHalf G) : ¬ G.Adj (M.f 0) (M.f 4) := by
  intro h
  obtain ⟨i,hi,eq⟩ := M.root_neighbors (M.f 4) h
  have ne : (4 : Fin 8) ∉ ([1,2,3] : List (Fin 8)) := by decide
  exact ne (M.f.injective eq ▸ hi)

variable [DecidableEq V]

private def MergedSameHalf.blocked (M : MergedSameHalf G) : Finset V := {M.f 1, M.f 2}

private theorem MergedSameHalf.blocked_subset (M : MergedSameHalf G) {v : V}
    (hv : v ∈ M.blocked) : v ∈ labelRegion M.f := by
  rcases (show v = M.f 1 ∨ v = M.f 2 by simpa [MergedSameHalf.blocked] using hv) with rfl|rfl
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

private theorem MergedSameHalf.survives (M : MergedSameHalf G) {i : Fin 8}
    (i1 : i ≠ 1) (i2 : i ≠ 2) : M.f i ∉ M.blocked := by
  simp [MergedSameHalf.blocked, M.f.injective.eq_iff, i1, i2]

private theorem MergedSameHalf.outgoing_available (M : MergedSameHalf G)
    {i : Fin 8} (keep : M.f i ∉ M.blocked) {v : V} (out : v ∉ labelRegion M.f)
    (adj : G.Adj (M.f i) v) : i = 3 ∨ i = 6 ∨ i = 7 := by
  have notLow : ¬ (i = 0 ∨ i = 4 ∨ i = 5) := fun h => out (M.low_stays h adj)
  have i1 : i ≠ 1 := fun h => keep (by simp [h, MergedSameHalf.blocked])
  have i2 : i ≠ 2 := fun h => keep (by simp [h, MergedSameHalf.blocked])
  fin_cases i <;> first | decide | exact (notLow (by decide)).elim | exact (i1 rfl).elim |
    exact (i2 rfl).elim

private theorem same_half_between_singletons (M : MergedSameHalf G) (R T : PrivateSingleton G)
    (noSix : NoIndependentSix G) (mr : Disjoint (labelRegion M.f) (labelRegion R.f))
    (mt : Disjoint (labelRegion M.f) (labelRegion T.f))
    (rt : Disjoint (labelRegion R.f) (labelRegion T.f)) :
    ∃ x ∈ labelRegion R.f, ∃ y ∈ labelRegion T.f, G.Adj x y := by
  classical
  by_contra no
  let A : Finset V := {M.f 0,M.f 4}
  let B : Finset V := {R.f 1,R.f 3}
  let C : Finset V := {T.f 1,T.f 3}
  have m (v : V) (h : v ∈ A) : v ∈ labelRegion M.f := by
    rcases (show v = M.f 0 ∨ v = M.f 4 by simpa [A] using h) with rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨4,rfl⟩
  have r (v : V) (h : v ∈ B) : v ∈ labelRegion R.f := by
    rcases (show v = R.f 1 ∨ v = R.f 3 by simpa [B] using h) with rfl|rfl
    · exact ⟨1,rfl⟩
    · exact ⟨3,rfl⟩
  have t (v : V) (h : v ∈ C) : v ∈ labelRegion T.f := by
    rcases (show v = T.f 1 ∨ v = T.f 3 by simpa [C] using h) with rfl|rfl
    · exact ⟨1,rfl⟩
    · exact ⟨3,rfl⟩
  have separate {s u : Finset V} {X Y : Set V} (dis : Disjoint X Y)
      (hs : ∀ v ∈ s, v ∈ X) (hu : ∀ v ∈ u, v ∈ Y) : Disjoint s u :=
    Finset.disjoint_left.mpr (fun v x y => Set.disjoint_left.mp dis (hs v x) (hu v y))
  have ac : A.card = 2 := Finset.card_pair (M.f.injective.ne (by decide))
  have bc : B.card = 2 := Finset.card_pair (R.f.injective.ne (by decide))
  have cc : C.card = 2 := Finset.card_pair (T.f.injective.ne (by decide))
  have size : ((A ∪ B) ∪ C).card = 6 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨separate mt m t,separate rt r t⟩),Finset.card_union_of_disjoint (separate mr m r)]
    omega
  have onlyA (x : V) (h : x ∈ A) (y : V) (adj : G.Adj x y) : y ∈ labelRegion M.f := by
    rcases (show x = M.f 0 ∨ x = M.f 4 by simpa [A] using h) with rfl|rfl
    · exact M.low_stays (i := 0) (by decide) adj
    · exact M.low_stays (i := 4) (by decide) adj
  have ab : InternallyIndependent G (A ∪ B) := independent_union
    (independent_pair _ _ M.sealed_pair) (independent_pair _ _ R.looseNonedge)
    (fun x xa y yb e => Set.disjoint_left.mp mr (onlyA x xa y e) (r y yb))
  have all : InternallyIndependent G (A ∪ B ∪ C) := independent_union ab
    (independent_pair _ _ T.looseNonedge) (fun x hx y yc e =>
      (Finset.mem_union.mp hx).elim
        (fun xa => Set.disjoint_left.mp mt (onlyA x xa y e) (t y yc))
        (fun xb => no ⟨x,r x xb,y,t y yc,e⟩))
  obtain ⟨x,hx,y,hy,adj⟩ := noSix _ size
  exact all x hx y hy adj

set_option maxHeartbeats 1200000 in
private theorem same_half_splice_in_order (M : MergedSameHalf G) (R T : PrivateSingleton G)
    (reach : EdgeReachAfterSmallDeletion G)
    (mr : Disjoint (labelRegion M.f) (labelRegion R.f))
    (mt : Disjoint (labelRegion M.f) (labelRegion T.f))
    (rt : Disjoint (labelRegion R.f) (labelRegion T.f))
    (cover : ∀ v, v ∈ labelRegion M.f ∨ v ∈ labelRegion R.f ∨ v ∈ labelRegion T.f)
    (looseOff : ¬ G.Adj (R.f 2) (R.f 3)) (looseDegree : 4 ≤ G.degree (R.f 3))
    (crossMR : ∃ x ∈ labelRegion M.f, x ∉ M.blocked ∧
      ∃ y ∈ labelRegion R.f, G.Adj x y)
    (crossRT : ∃ x ∈ labelRegion R.f, ∃ y ∈ labelRegion T.f, G.Adj x y) :
    Nonempty (PathOn G Set.univ) := by
  let W : Set V := {v | v ∈ labelRegion M.f ∧ v ∉ M.blocked}
  let Contact (flag : Bool) (U : Set V) : Prop := ∃ i : Fin 4,
    singletonHigh i = true ∧ singletonLoose i = flag ∧ ∃ v ∈ U, G.Adj (R.f i) v
  have off (a : Fin 8) : M.f a ∉ labelRegion R.f :=
    fun h => Set.disjoint_left.mp mr ⟨a,rfl⟩ h
  have outside (v : V) (h : v ∈ M.blocked) : v ∉ labelRegion R.f :=
    fun r => Set.disjoint_left.mp mr (M.blocked_subset h) r
  have small : M.blocked.card ≤ 2 := by
    have size : M.blocked.card = 2 := Finset.card_pair (M.f.injective.ne (by decide))
    omega
  have options (i : Fin 4) (hi : singletonHigh i = true) {v : V}
      (vo : v ∉ labelRegion R.f) (keep : v ∉ M.blocked) (adj : G.Adj (R.f i) v) :
      Contact (singletonLoose i) W ∨ Contact (singletonLoose i) (labelRegion T.f) := by
    rcases cover v with mv|rv|tv
    · exact Or.inl ⟨i,hi,rfl,v,⟨mv,keep⟩,adj⟩
    · exact (vo rv).elim
    · exact Or.inr ⟨i,hi,rfl,v,tv,adj⟩
  have loose : Contact true W ∨ Contact true (labelRegion T.f) := by
    obtain ⟨v,vo,keep,adj⟩ := R.loose_has_unblocked_contact small looseOff looseDegree
    exact options 3 rfl vo keep adj
  have tip : Contact false W ∨ Contact false (labelRegion T.f) := by
    obtain ⟨i,hi,v,vo,keep,adj⟩ := R.triangle_has_unblocked_contact reach small outside
      (off 0) (off 3) (M.survives (by decide) (by decide)) (M.survives (by decide) (by decide))
      (M.edges 0 3 (by decide))
    rcases hi with rfl|rfl
    · exact options 1 rfl vo keep adj
    · exact options 2 rfl vo keep adj
  have toM : Contact true W ∨ Contact false W := by
    obtain ⟨x,xM,keep,y,⟨i,rfl⟩,adj⟩ := crossMR
    have ih := R.outgoing_high (fun h => Set.disjoint_left.mp mr xM h) adj.symm
    cases h : singletonLoose i
    · exact Or.inr ⟨i,ih,h,x,⟨xM,keep⟩,adj.symm⟩
    · exact Or.inl ⟨i,ih,h,x,⟨xM,keep⟩,adj.symm⟩
  have toT : Contact true (labelRegion T.f) ∨ Contact false (labelRegion T.f) := by
    obtain ⟨_,⟨i,rfl⟩,v,vt,adj⟩ := crossRT
    have ih := R.outgoing_high (fun h => Set.disjoint_left.mp rt h vt) adj
    cases h : singletonLoose i
    · exact Or.inr ⟨i,ih,h,v,vt,adj⟩
    · exact Or.inl ⟨i,ih,h,v,vt,adj⟩
  have matching : ∃ flag : Bool, Contact flag W ∧ Contact (!flag) (labelRegion T.f) := by
    have h : (Contact true W ∧ Contact false (labelRegion T.f)) ∨
        (Contact false W ∧ Contact true (labelRegion T.f)) :=
      match_endpoint_types _ _ _ _ loose tip toM toT
    exact h.elim (fun h => ⟨true,h⟩) (fun h => ⟨false,h⟩)
  obtain ⟨flag,⟨i,ih,li,_,⟨⟨u,rfl⟩,keep⟩,start⟩,⟨j,jh,lj,_,⟨v,rfl⟩,finish⟩⟩ := matching
  have distinctTypes : singletonLoose i ≠ singletonLoose j := by
    rw [li,lj]
    cases flag <;> decide
  have uh := M.outgoing_available keep (fun h => Set.disjoint_left.mp mr h ⟨i,rfl⟩) start.symm
  have vh := T.outgoing_high (fun h => Set.disjoint_left.mp rt ⟨j,rfl⟩ h) finish.symm
  obtain ⟨p,pend⟩ := same_half_available_ends M.f M.edges uh
  obtain ⟨q,qfirst,qend⟩ := singleton_between_types R.f R.edges ih jh distinctTypes
  obtain ⟨z,zfirst⟩ := singleton_start_at_high T.f T.edges vh
  have pq : G.Adj p.last q.first := pend.symm ▸ qfirst.symm ▸ start.symm
  have qz : G.Adj q.last z.first := qend.symm ▸ zfirst.symm ▸ finish
  let head := p.join q mr pq
  have endpoint : head.last = q.last := List.getLast_append_of_ne_nil head.nonempty q.nonempty
  have dis : Disjoint (labelRegion M.f ∪ labelRegion R.f) (labelRegion T.f) :=
    Set.disjoint_union_left.mpr ⟨mt,rt⟩
  have all : (labelRegion M.f ∪ labelRegion R.f) ∪ labelRegion T.f = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    rcases cover v with hm|hr|ht
    · exact Or.inl (Or.inl hm)
    · exact Or.inl (Or.inr hr)
    · exact Or.inr ht
  exact ⟨all ▸ head.join z dis (endpoint.symm ▸ qz)⟩

/-- The same-half three-singleton layout has a Hamiltonian path. Each private singleton
has two triangle ports and a loose port of degree at least four seeing neither triangle port. -/
theorem traceable_three_singletons_same_half_tips (M : MergedSameHalf G) (R T : PrivateSingleton G)
    (reach : EdgeReachAfterSmallDeletion G) (noSix : NoIndependentSix G)
    (mr : Disjoint (labelRegion M.f) (labelRegion R.f))
    (mt : Disjoint (labelRegion M.f) (labelRegion T.f))
    (rt : Disjoint (labelRegion R.f) (labelRegion T.f))
    (cover : ∀ v, v ∈ labelRegion M.f ∨ v ∈ labelRegion R.f ∨ v ∈ labelRegion T.f)
    (rOff : ¬ G.Adj (R.f 2) (R.f 3)) (tOff : ¬ G.Adj (T.f 2) (T.f 3))
    (rDegree : 4 ≤ G.degree (R.f 3)) (tDegree : 4 ≤ G.degree (T.f 3)) :
    Nonempty (PathOn G Set.univ) := by
  have rtContact := same_half_between_singletons M R T noSix mr mt rt
  have off (i : Fin 4) : R.f i ∉ labelRegion M.f :=
    fun h => Set.disjoint_left.mp mr h ⟨i,rfl⟩
  have size : M.blocked.card = 2 := Finset.card_pair (M.f.injective.ne (by decide))
  obtain ⟨x,xm,y,yo,keep,_,xy⟩ := crossingAfterSmallDeletion reach (D := M.blocked) (by omega)
    (U := labelRegion M.f) (a := M.f 0) (b := M.f 3) (c := R.f 0) (d := R.f 1) ⟨0,rfl⟩
    (off 0) (M.survives (by decide) (by decide)) (M.survives (by decide) (by decide))
    (fun h => off 0 (M.blocked_subset h)) (fun h => off 1 (M.blocked_subset h))
    (M.edges 0 3 (by decide)) (R.edges 0 1 (by decide))
  rcases (cover y).resolve_left yo with yr|yt
  · exact same_half_splice_in_order M R T reach mr mt rt cover rOff rDegree
      ⟨x,xm,keep,y,yr,xy⟩ rtContact
  · obtain ⟨a,ar,b,bt,ab⟩ := rtContact
    exact same_half_splice_in_order M T R reach mt mr rt.symm
      (fun v => (cover v).imp id Or.symm) tOff tDegree ⟨x,xm,keep,y,yt,xy⟩ ⟨b,bt,a,ar,ab.symm⟩

#print axioms traceable_three_singletons_same_half_tips

end Graffiti199Depleted
