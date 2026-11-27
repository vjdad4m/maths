import SplitTipsLocal
import DepletedFootprint

open private three_names_exhaust_neighbors from DepletedFootprint

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A singleton block whose root has degree three. -/
structure PrivateSingleton (G : SimpleGraph V) [DecidableRel G.Adj] where
  f : Fin 4 ↪ V
  edges : ∀ i j, (i,j) ∈ singletonEdges → G.Adj (f i) (f j)
  looseNonedge : ¬ G.Adj (f 1) (f 3)
  degree : G.degree (f 0) = 3

/-- The merged block with its two shared triangle tips in opposite paired halves. -/
structure MergedSplitTips (G : SimpleGraph V) [DecidableRel G.Adj] where
  f : Fin 8 ↪ V
  edges : ∀ i j, (i,j) ∈ splitTipsEdges → G.Adj (f i) (f j)
  degree : ∀ i ∈ ([0,4,5] : List (Fin 8)), G.degree (f i) = 3

private theorem PrivateSingleton.root_neighbors (R : PrivateSingleton G)
    (v : V) (adj : G.Adj (R.f 0) v) : ∃ j ∈ ([1,2,3] : List (Fin 4)), R.f j = v :=
  three_names_exhaust_neighbors R.f (by decide) (by decide) (by decide)
    R.degree (R.edges 0 1 (by decide)) (R.edges 0 2 (by decide)) (R.edges 0 3 (by decide)) v adj

theorem PrivateSingleton.outgoing_high (R : PrivateSingleton G)
    {i : Fin 4} {v : V} (out : v ∉ labelRegion R.f) (adj : G.Adj (R.f i) v) :
    singletonHigh i = true := by
  fin_cases i
  · obtain ⟨j,_,eq⟩ := R.root_neighbors v adj
    exact (out ⟨j,eq⟩).elim
  · rfl
  · rfl
  · rfl

private theorem MergedSplitTips.root_neighbors (M : MergedSplitTips G)
    (v : V) (adj : G.Adj (M.f 0) v) : ∃ j ∈ ([1,2,3] : List (Fin 8)), M.f j = v :=
  three_names_exhaust_neighbors M.f (by decide) (by decide) (by decide)
    (M.degree 0 (by decide)) (M.edges 0 1 (by decide)) (M.edges 0 2 (by decide))
    (M.edges 0 3 (by decide)) v adj

private theorem MergedSplitTips.low_stays (M : MergedSplitTips G) {i : Fin 8}
    (low : splitTipsHigh i = false) {v : V} (adj : G.Adj (M.f i) v) :
    v ∈ labelRegion M.f := by
  fin_cases i
  · obtain ⟨j,_,eq⟩ := M.root_neighbors v adj
    exact ⟨j,eq⟩
  · cases low
  · cases low
  · cases low
  · obtain ⟨j,_,eq⟩ :=
      three_names_exhaust_neighbors M.f (by decide) (by decide) (by decide)
        (M.degree 4 (by decide)) (M.edges 4 5 (by decide)) (M.edges 4 1 (by decide))
        (M.edges 4 6 (by decide)) v adj
    exact ⟨j,eq⟩
  · obtain ⟨j,_,eq⟩ :=
      three_names_exhaust_neighbors M.f (by decide) (by decide) (by decide)
        (M.degree 5 (by decide)) (M.edges 4 5 (by decide)).symm (M.edges 5 2 (by decide))
        (M.edges 5 7 (by decide)) v adj
    exact ⟨j,eq⟩
  · cases low
  · cases low

private theorem MergedSplitTips.outgoing_high (M : MergedSplitTips G)
    {i : Fin 8} {v : V} (out : v ∉ labelRegion M.f) (adj : G.Adj (M.f i) v) :
    splitTipsHigh i = true := by
  cases eq : splitTipsHigh i
  · exact (out (M.low_stays eq adj)).elim
  · rfl

private theorem MergedSplitTips.loose_roots (M : MergedSplitTips G) : ¬ G.Adj (M.f 0) (M.f 4) := by
  intro h
  obtain ⟨i,hi,eq⟩ := M.root_neighbors (M.f 4) h
  have ne : (4 : Fin 8) ∉ ([1,2,3] : List (Fin 8)) := by decide
  exact ne (M.f.injective eq ▸ hi)

/-- This is the finite-set formulation of the absence of an independent
set of size six. Repetition of endpoints cannot witness adjacency. -/
def NoIndependentSix (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card = 6 → ∃ x ∈ S, ∃ y ∈ S, G.Adj x y

variable [DecidableEq V]

private def InternallyIndependent (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ¬ G.Adj x y

omit [Fintype V] [DecidableRel G.Adj] in
private theorem independent_pair (x y : V) (ne : ¬ G.Adj x y) :
    InternallyIndependent G ({x,y} : Finset V) := by
  classical
  intro u hu v hv h
  have eu : u = x ∨ u = y := by simpa using hu
  have ev : v = x ∨ v = y := by simpa using hv
  rcases eu with eu|eu <;> rcases ev with ev|ev <;> rw [eu,ev] at h
  · exact G.loopless _ h
  · exact ne h
  · exact ne h.symm
  · exact G.loopless _ h

omit [Fintype V] [DecidableRel G.Adj] in
private theorem independent_union {a b : Finset V} (ha : InternallyIndependent G a)
    (hb : InternallyIndependent G b) (cross : ∀ x ∈ a, ∀ y ∈ b, ¬ G.Adj x y) :
    InternallyIndependent G (a ∪ b) := by
  classical
  intro x hx y hy h
  rcases Finset.mem_union.mp hx with ax|bx <;> rcases Finset.mem_union.mp hy with ay|by'
  · exact ha x ax y ay h
  · exact cross x ax y by' h
  · exact cross y ay x bx h.symm
  · exact hb x bx y by' h

private theorem between_private_singletons (M : MergedSplitTips G) (R T : PrivateSingleton G)
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
    · exact M.low_stays (i := 0) rfl adj
    · exact M.low_stays (i := 4) rfl adj
  have ab : InternallyIndependent G (A ∪ B) := independent_union
    (independent_pair _ _ M.loose_roots) (independent_pair _ _ R.looseNonedge)
    (fun x xa y yb e => Set.disjoint_left.mp mr (onlyA x xa y e) (r y yb))
  have all : InternallyIndependent G (A ∪ B ∪ C) := independent_union ab
    (independent_pair _ _ T.looseNonedge) (fun x hx y yc e =>
      (Finset.mem_union.mp hx).elim
        (fun xa => Set.disjoint_left.mp mt (onlyA x xa y e) (t y yc))
        (fun xb => no ⟨x,r x xb,y,t y yc,e⟩))
  obtain ⟨x,hx,y,hy,adj⟩ := noSix _ size
  exact all x hx y hy adj

omit [DecidableEq V] in
/-- Deleting the other high vertices preserves the root-to-port edge.
The edge-to-edge cut condition forces the specified port to see outside. -/
private theorem PrivateSingleton.port_sees_outside (R : PrivateSingleton G)
    (reach : EdgeReachAfterSmallDeletion G) {a b : V}
    (ao : a ∉ labelRegion R.f) (bo : b ∉ labelRegion R.f) (ab : G.Adj a b)
    {i : Fin 4} (hi : singletonHigh i = true) :
    ∃ v ∉ labelRegion R.f, G.Adj (R.f i) v := by
  classical
  let D := ((Finset.univ : Finset (Fin 4)).filter fun j => j ≠ 0 ∧ j ≠ i).map R.f
  have small : D.card ≤ 3 := by
    have cap : ((Finset.univ : Finset (Fin 4)).erase 0).card = 3 := by decide
    rw [Finset.card_map]
    have subset : (Finset.univ.filter fun j : Fin 4 => j ≠ 0 ∧ j ≠ i) ⊆ Finset.univ.erase 0 :=
      fun k hk => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hk).2.1,Finset.mem_univ _⟩
    exact (Finset.card_le_card subset).trans_eq cap
  have survive (k : Fin 4) (h : k = 0 ∨ k = i) : R.f k ∉ D := by
    intro e
    obtain ⟨j,jh,eq⟩ := Finset.mem_map.mp e
    obtain rfl := R.f.injective eq
    exact h.elim (Finset.mem_filter.mp jh).2.1 (Finset.mem_filter.mp jh).2.2
  have aside (v : V) (off : v ∉ labelRegion R.f) : v ∉ D := fun d => by
    obtain ⟨k,_,eq⟩ := Finset.mem_map.mp d
    exact off ⟨k,eq⟩
  have root_adj : G.Adj (R.f 0) (R.f i) := by
    fin_cases i
    · cases hi
    · exact R.edges 0 1 (by decide)
    · exact R.edges 0 2 (by decide)
    · exact R.edges 0 3 (by decide)
  obtain ⟨x,xR,y,yo,xD,_,xy⟩ := crossingAfterSmallDeletion reach small
    (U := labelRegion R.f) ⟨0,rfl⟩ ao (survive 0 (Or.inl rfl)) (survive i (Or.inr rfl))
    (aside a ao) (aside b bo) root_adj ab
  obtain ⟨j,rfl⟩ := xR
  have j0 : j ≠ 0 := fun e => by
    subst j
    have impossible := R.outgoing_high yo xy
    cases impossible
  have ji : j = i := Classical.byContradiction (fun e =>
    xD (Finset.mem_map.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,j0,e⟩,rfl⟩))
  exact ⟨y,yo,ji ▸ xy⟩

private theorem match_endpoint_types (A B C D : Prop)
    (r₁ : A ∨ B) (r₂ : C ∨ D) (c₁ : A ∨ C) (c₂ : B ∨ D) :
    (A ∧ D) ∨ (C ∧ B) := by tauto

omit [DecidableEq V] in
set_option maxHeartbeats 1200000 in
private theorem splice_in_order (M : MergedSplitTips G) (R T : PrivateSingleton G)
    (reach : EdgeReachAfterSmallDeletion G)
    (mr : Disjoint (labelRegion M.f) (labelRegion R.f))
    (mt : Disjoint (labelRegion M.f) (labelRegion T.f))
    (rt : Disjoint (labelRegion R.f) (labelRegion T.f))
    (cover : ∀ v, v ∈ labelRegion M.f ∨ v ∈ labelRegion R.f ∨ v ∈ labelRegion T.f)
    (crossMR : ∃ x ∈ labelRegion M.f, ∃ y ∈ labelRegion R.f, G.Adj x y)
    (crossRT : ∃ x ∈ labelRegion R.f, ∃ y ∈ labelRegion T.f, G.Adj x y) :
    Nonempty (PathOn G Set.univ) := by
  let Contact (flag : Bool) (W : Set V) : Prop := ∃ i : Fin 4,
    singletonHigh i = true ∧ singletonLoose i = flag ∧ ∃ v ∈ W, G.Adj (R.f i) v
  have options (i : Fin 4) (hi : singletonHigh i = true) :
      Contact (singletonLoose i) (labelRegion M.f) ∨ Contact (singletonLoose i) (labelRegion T.f) := by
    have off (a : Fin 8) : M.f a ∉ labelRegion R.f :=
      fun h => Set.disjoint_left.mp mr ⟨a,rfl⟩ h
    obtain ⟨v,vo,adj⟩ := R.port_sees_outside reach (off 0) (off 1) (M.edges 0 1 (by decide)) hi
    rcases cover v with mv|rv|tv
    · exact Or.inl ⟨i,hi,rfl,v,mv,adj⟩
    · exact (vo rv).elim
    · exact Or.inr ⟨i,hi,rfl,v,tv,adj⟩
  have loose : Contact true (labelRegion M.f) ∨ Contact true (labelRegion T.f) := options 3 rfl
  have tip : Contact false (labelRegion M.f) ∨ Contact false (labelRegion T.f) := options 1 rfl
  have toM : Contact true (labelRegion M.f) ∨ Contact false (labelRegion M.f) := by
    obtain ⟨x,xM,y,⟨i,rfl⟩,adj⟩ := crossMR
    have ih := R.outgoing_high (fun h => Set.disjoint_left.mp mr xM h) adj.symm
    cases h : singletonLoose i
    · exact Or.inr ⟨i,ih,h,x,xM,adj.symm⟩
    · exact Or.inl ⟨i,ih,h,x,xM,adj.symm⟩
  have toT : Contact true (labelRegion T.f) ∨ Contact false (labelRegion T.f) := by
    obtain ⟨_,⟨i,rfl⟩,v,vt,adj⟩ := crossRT
    have ih := R.outgoing_high (fun h => Set.disjoint_left.mp rt h vt) adj
    cases h : singletonLoose i
    · exact Or.inr ⟨i,ih,h,v,vt,adj⟩
    · exact Or.inl ⟨i,ih,h,v,vt,adj⟩
  have matching : ∃ flag : Bool, Contact flag (labelRegion M.f) ∧ Contact (!flag) (labelRegion T.f) := by
    have h : (Contact true (labelRegion M.f) ∧ Contact false (labelRegion T.f)) ∨
        (Contact false (labelRegion M.f) ∧ Contact true (labelRegion T.f)) :=
      match_endpoint_types _ _ _ _ loose tip toM toT
    exact h.elim (fun h => ⟨true,h⟩) (fun h => ⟨false,h⟩)
  obtain ⟨flag,⟨i,ih,li,_,⟨u,rfl⟩,start⟩,⟨j,jh,lj,_,⟨v,rfl⟩,finish⟩⟩ := matching
  have distinctTypes : singletonLoose i ≠ singletonLoose j := by
    rw [li,lj]
    cases flag <;> decide
  have uh := M.outgoing_high (fun h => Set.disjoint_left.mp mr h ⟨i,rfl⟩) start.symm
  have vh := T.outgoing_high (fun h => Set.disjoint_left.mp rt ⟨j,rfl⟩ h) finish.symm
  obtain ⟨p,pend⟩ := split_tips_path_ending_at_high M.f M.edges uh
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

/-- The three-singleton layout is traceable when one singleton shares its
two triangle tips with opposite halves of the single paired block.
The other two singleton blocks are disjoint and have degree-three roots. -/
theorem traceable_three_singletons_split_tips (M : MergedSplitTips G) (R T : PrivateSingleton G)
    (reach : EdgeReachAfterSmallDeletion G) (noSix : NoIndependentSix G)
    (mr : Disjoint (labelRegion M.f) (labelRegion R.f))
    (mt : Disjoint (labelRegion M.f) (labelRegion T.f))
    (rt : Disjoint (labelRegion R.f) (labelRegion T.f))
    (cover : ∀ v, v ∈ labelRegion M.f ∨ v ∈ labelRegion R.f ∨ v ∈ labelRegion T.f) :
    Nonempty (PathOn G Set.univ) := by
  have rtContact := between_private_singletons M R T noSix mr mt rt
  obtain ⟨x,xm,y,yo,_,_,xy⟩ := crossingAfterSmallDeletion reach (D := ∅) (by simp)
    (U := labelRegion M.f) (a := M.f 0) (b := M.f 1) (c := R.f 0) (d := R.f 1) ⟨0,rfl⟩
    (fun h => Set.disjoint_left.mp mr h ⟨0,rfl⟩) (by simp) (by simp) (by simp) (by simp)
    (M.edges 0 1 (by decide)) (R.edges 0 1 (by decide))
  rcases (cover y).resolve_left yo with yr|yt
  · exact splice_in_order M R T reach mr mt rt cover ⟨x,xm,y,yr,xy⟩ rtContact
  · obtain ⟨a,ar,b,bt,ab⟩ := rtContact
    exact splice_in_order M T R reach mt mr rt.symm
      (fun v => (cover v).imp id Or.symm) ⟨x,xm,y,yt,xy⟩ ⟨b,bt,a,ar,ab.symm⟩

#print axioms traceable_three_singletons_split_tips

end Graffiti199Depleted
