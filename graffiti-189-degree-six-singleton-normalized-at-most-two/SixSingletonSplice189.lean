import SixSingletonDarkOre189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Singleton16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
abbrev V := Fin 16
abbrev a : V := 0
abbrev b : V := 1
abbrev s : V := 2
abbrev x : V := 3
abbrev y : V := 4
def K : Finset V := {5,6,7,8}
def D : Finset V := {9,10,11,12,13,14,15}
def P : Finset V := insert x (insert y K)
private theorem d7 : D.card=7 := by decide
private theorem k4 : K.card=4 := by decide
private theorem p6 : P.card=6 := by decide

variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- The exact normalized singleton profile for routing. The two strict
classes partition the nonbalanced dark vertices. The assumptions place
no constraints on unlisted internal edges. -/
structure Frame (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V) : Prop where
  left_sub : L⊆D
  right_sub : R⊆D
  lr_dis : Disjoint L R
  l2 : 2≤L.card
  r2 : 2≤R.card
  strict5 : 5≤(L∪R).card
  sa : G.Adj s a
  sb : G.Adj s b
  ax : G.Adj a x
  by' : G.Adj b y
  ac : ∀ z∈K,G.Adj a z
  bc : ∀ z∈K,G.Adj b z
  xL : ∀ z∈L,G.Adj x z
  yR : ∀ z∈R,G.Adj y z
  dark5 : ∀ z∈L∪R,5≤(inside G D z).card
  darkHigh : ∀ z∈D,6≤G.degree z
  commonHigh : ∀ z∈K,6≤G.degree z
  commonBounds : ∀ z∈K,∀ w,G.Adj z w → w∈insert a (insert b (P∪(D\(L∪R))))
  darkBounds : ∀ z∈D,∀ w,G.Adj z w → w∈P∪D

private theorem row_all (A : Finset V) {u v : V} (p : RouteOn G A u v)
    (all : ∀ z,z∈A) : ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  obtain ⟨q,pp,ww⟩ := p
  exact ⟨u,v,q,pp,fun z=>(ww z).mpr (all z)⟩

private theorem finish_standard {l r c t : V} (rp : RouteOn G D l r) (cp : RouteOn G K c t)
    (sa : G.Adj s a) (ax : G.Adj a x) (xl : G.Adj x l)
    (ry : G.Adj r y) (yc : G.Adj y c) (tb : G.Adj t b) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  have q := rp.prefix xl (by decide)
  have q' := q.prefix ax (by decide)
  have q'' := q'.prefix sa (by decide)
  have p := cp.prefix yc (by decide)
  have p' := p.suffix tb (by decide)
  have w := q''.join p' (by decide) ry
  exact row_all _ w (by decide)

private theorem finish_standard_swap {l r c t : V} (rp : RouteOn G D l r) (cp : RouteOn G K c t)
    (sb : G.Adj s b) (by' : G.Adj b y) (yr : G.Adj y r)
    (lx : G.Adj l x) (xc : G.Adj x c) (ta : G.Adj t a) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  have q := rp.reverse.prefix yr (by decide)
  have q' := q.prefix by' (by decide)
  have q'' := q'.prefix sb (by decide)
  have p := cp.prefix xc (by decide)
  have p' := p.suffix ta (by decide)
  have w := q''.join p' (by decide) lx
  exact row_all _ w (by decide)

private theorem finish_balance_end {l w c t : V} (rp : RouteOn G D l w) (cp : RouteOn G K c t)
    (sa : G.Adj s a) (ax : G.Adj a x) (xl : G.Adj x l)
    (wc : G.Adj w c) (tb : G.Adj t b) (by' : G.Adj b y) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  have p := rp.prefix xl (by decide)
  have q := p.prefix ax (by decide)
  have r := q.prefix sa (by decide)
  have c' := cp.suffix tb (by decide)
  have c'' := c'.suffix by' (by decide)
  exact row_all _ (r.join c'' (by decide) wc) (by decide)

private theorem finish_isolated_dark {l r w c t : V} (wd : w∈D)
    (rp : RouteOn G (D.erase w) l r) (cp : RouteOn G K c t)
    (sa : G.Adj s a) (ax : G.Adj a x) (xl : G.Adj x l)
    (ry : G.Adj r y) (yw : G.Adj y w) (wc : G.Adj w c) (tb : G.Adj t b) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  have p := rp.prefix xl (fun h=>(by decide : x∉D) (mem_of_mem_erase h))
  have q := p.prefix ax (by
    intro h
    rcases mem_insert.mp h with i|i
    · exact (by decide : a≠x) i
    exact (by decide : a∉D) (mem_of_mem_erase i))
  have r' := q.prefix sa (by
    intro h
    simp only [mem_insert] at h
    exact h.elim (by decide : s≠a) (fun h=>h.elim (by decide : s≠x)
      (fun h=>(by decide : s∉D) (mem_of_mem_erase h))))
  have c' := cp.prefix wc (fun h=>disjoint_left.mp (by decide : Disjoint D K) wd h)
  have c'' := c'.prefix yw (by
    intro h
    rcases mem_insert.mp h with e|e
    · exact (by decide : y∉D) (e.symm ▸ wd)
    exact (by decide : y∉K) e)
  have c''' := c''.suffix tb (by
    intro h
    simp only [mem_insert] at h
    rcases h with e|e|e
    · exact (by decide : b≠y) e
    · exact (by decide : b∉D) (e.symm ▸ wd)
    exact (by decide : b∉K) e)
  have dis : Disjoint (insert s (insert a (insert x (D.erase w))))
      (insert b (insert y (insert w K))) := by
    apply disjoint_left.mpr
    intro z zl zr
    have h₁ : z∈(insert s (insert a (insert x D))) := by
      simp only [mem_insert] at zl ⊢
      exact zl.imp id (fun r=>r.imp id (fun r=>r.imp id mem_of_mem_erase))
    rcases (mem_insert.mp zr) with h|h
    · exact (by decide : b∉insert s (insert a (insert x D))) (h ▸ h₁)
    rcases (mem_insert.mp h) with h|h
    · exact (by decide : y∉insert s (insert a (insert x D))) (h ▸ h₁)
    rcases (mem_insert.mp h) with h|h
    · subst z
      rcases (mem_insert.mp zl) with h|h
      · exact (by decide : s∉D) (h ▸ wd)
      rcases (mem_insert.mp h) with h|h
      · exact (by decide : a∉D) (h ▸ wd)
      rcases (mem_insert.mp h) with h|h
      · exact (by decide : x∉D) (h ▸ wd)
      exact (mem_erase.mp h).1 rfl
    exact disjoint_left.mp (by decide : Disjoint (insert s (insert a (insert x D))) K) h₁ h
  apply row_all _ (r'.join c''' dis ry)
  intro z
  by_cases h : z=w
  · simp [h]
  have base : z∈insert s (insert a (insert x D)) ∪ insert b (insert y K) :=
    (by decide : ∀ u : V,u∈insert s (insert a (insert x D))∪insert b (insert y K)) z
  simp only [mem_union,mem_insert,mem_erase] at base ⊢
  tauto

private theorem balance_common_if_low {L R : Finset V} (F : Frame G L R)
    {w : V} (wd : w∈D) (low : (inside G D w).card≤2) :
    ∃ c∈K,G.Adj w c := by
  classical
  by_contra no
  have h : G.neighborFinset w⊆insert x (insert y (inside G D w)) := by
    intro z zm
    have wz := (mem_neighborFinset _ _ _).mp zm
    rcases mem_union.mp (F.darkBounds w wd z wz) with zp|zd
    · rcases mem_insert.mp zp with e|e
      · exact mem_insert.mpr (.inl e)
      rcases mem_insert.mp e with e|e
      · exact mem_insert_of_mem (mem_insert.mpr (.inl e))
      exact (no ⟨z,e,wz⟩).elim
    exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨zd,wz⟩))
  have q := card_le_card h
  rw [card_neighborFinset_eq_degree] at q
  have i := card_insert_le x (insert y (inside G D w))
  have j := card_insert_le y (inside G D w)
  have high := F.darkHigh _ wd
  omega

private theorem every_port_of_isolated_dark {L R : Finset V} (F : Frame G L R)
    {w : V} (wd : w∈D) (no : ∀ z∈D,¬G.Adj w z) :
    P⊆G.neighborFinset w := by
  have h : G.neighborFinset w⊆P := by
    intro z zm
    have wz := (mem_neighborFinset _ _ _).mp zm
    exact (mem_union.mp (F.darkBounds w wd z wz)).resolve_right (fun zd=>no z zd wz)
  exact (eq_of_subset_of_card_le h (by rw [p6,card_neighborFinset_eq_degree]; exact F.darkHigh w wd)).ge

private theorem common_needs_balance_if_no_exclusive {L R : Finset V} (F : Frame G L R)
    (noX : ¬∃ c∈K,G.Adj x c) (noY : ¬∃ c∈K,G.Adj y c) :
    ∃ w∈D\(L∪R),∃ c∈K,G.Adj w c := by
  classical
  have cK : (5:V)∈K := by decide
  by_contra no
  have h : G.neighborFinset 5⊆insert a (insert b (K.erase 5)) := by
    intro z zm
    have e := (mem_neighborFinset _ _ _).mp zm
    rcases mem_insert.mp (F.commonBounds 5 cK z e) with p|p
    · exact mem_insert.mpr (.inl p)
    rcases mem_insert.mp p with p|p
    · exact mem_insert_of_mem (mem_insert.mpr (.inl p))
    rcases mem_union.mp p with p|p
    · rcases mem_insert.mp p with p|p
      · exact (noX ⟨5,cK,p ▸ e.symm⟩).elim
      rcases mem_insert.mp p with p|p
      · exact (noY ⟨5,cK,p ▸ e.symm⟩).elim
      exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨e.ne.symm,p⟩))
    exact (no ⟨z,p,5,cK,e.symm⟩).elim
  have k := card_le_card h
  rw [card_neighborFinset_eq_degree] at k
  have high := F.commonHigh 5 cK
  have q : (insert a (insert b (K.erase 5))).card=5 := by decide
  omega

/-- Nonadjacent singleton order-16 routing checkpoint on the exact
normalized dark/common board, when at most two dark vertices are balanced. -/
theorem traceable_of_frame_common_min_two {L R : Finset V} (F : Frame G L R)
    (comm : ∀ c∈K,2≤(inside G K c).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let S := L∪R
  have sub : S⊆D := union_subset F.left_sub F.right_sub
  have lpos : L.Nonempty := card_pos.mp (by have h:=F.l2; omega)
  have rpos : R.Nonempty := card_pos.mp (by have h:=F.r2; omega)
  obtain ⟨l,ll⟩ := lpos
  obtain ⟨r,rr⟩ := rpos
  have lr : l≠r := fun e=>disjoint_left.mp F.lr_dis ll (e.symm ▸ rr)
  have rootedK (z : V) (zk : z∈K) : ∃ t∈K,RouteOn G K z t :=
    rooted_high_residual_Ore_at_d 2 K (by decide) comm zk
  by_cases all : ∀ w∈D,w∉S → 3≤(inside G D w).card
  · have route {u v : V} (ud : u∈D) (vd : v∈D) (uv : u≠v) :=
      dark_block_seven_hamilton_connected D S sub d7 F.strict5 F.dark5 all ud vd uv
    have p := route (F.left_sub ll) (F.right_sub rr) lr
    by_cases Y : ∃ c∈K,G.Adj y c
    · obtain ⟨c,ck,yc⟩ := Y
      obtain ⟨t,tk,Q⟩ := rootedK c ck
      exact finish_standard p Q F.sa F.ax (F.xL l ll) (F.yR r rr).symm yc (F.bc t tk).symm
    by_cases X : ∃ c∈K,G.Adj x c
    · obtain ⟨c,ck,xc⟩ := X
      obtain ⟨t,tk,Q⟩ := rootedK c ck
      exact finish_standard_swap p Q F.sb F.by' (F.yR r rr) (F.xL l ll).symm xc (F.ac t tk).symm
    obtain ⟨w,ww,c,ck,wc⟩ := common_needs_balance_if_no_exclusive F X Y
    have wp := mem_sdiff.mp ww
    have nw : l≠w := fun e=>wp.2 (mem_union_left _ (e ▸ ll))
    obtain ⟨t,tk,Q⟩ := rootedK c ck
    exact finish_balance_end (route (F.left_sub ll) wp.1 nw) Q F.sa F.ax (F.xL l ll) wc (F.bc t tk).symm F.by'
  push_neg at all
  obtain ⟨w,wd,ws,lo⟩ := all
  have route {u v : V} (ud : u∈D.erase w) (vd : v∈D.erase w) (uv : u≠v) :=
    dark_block_remove_low_hamilton_connected D S sub d7 F.strict5 F.dark5 wd ws (by omega) ud vd uv
  obtain ⟨c,ck,wc⟩ := balance_common_if_low F wd (by omega)
  obtain ⟨t,tk,Q⟩ := rootedK c ck
  have lW {p : V} (pl : p∈L) : p∈D.erase w :=
    mem_erase.mpr ⟨fun e=>ws (mem_union_left _ (e ▸ pl)),F.left_sub pl⟩
  have rW : r∈D.erase w := mem_erase.mpr ⟨fun e=>ws (mem_union_right _ (e ▸ rr)),F.right_sub rr⟩
  by_cases e : ∃ z∈D,G.Adj w z
  · obtain ⟨z,zd,wz⟩ := e
    obtain ⟨p,pl,pz⟩ := exists_ne_of_one_lt_card (s:=L) (by have u:=F.l2; omega) z
    have r1 := route (lW pl) (mem_erase.mpr ⟨wz.ne.symm,zd⟩) pz
    have r2 := r1.suffix wz.symm (not_mem_erase _ _)
    rw [insert_erase wd] at r2
    exact finish_balance_end r2 Q F.sa F.ax (F.xL p pl) wc (F.bc t tk).symm F.by'
  push_neg at e
  have wy := (mem_neighborFinset _ _ _).mp (every_port_of_isolated_dark F wd e (by decide : y∈P))
  exact finish_isolated_dark wd (route (lW ll) rW lr) Q F.sa F.ax (F.xL l ll)
    (F.yR r rr).symm wy.symm wc (F.bc t tk).symm

#print axioms traceable_of_frame_common_min_two
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Singleton16
