import ShoreIntervals

open private six_le_treeNumber_of_five_independent_neighbors from CubicEdgeCuts
open private shore_anticomplete from CubicPortThreeShores
open private two_present_ports from TwoShortShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}
variable {A B : Set V} {D : Finset V}

/-- A component consisting of a center and three independent neighbors. -/
structure ClawShore (G : SimpleGraph V) (B : Set V) where
  center : V
  leaves : Finset V
  cover : B = insert center (↑leaves : Set V)
  three : leaves.card = 3
  off : center ∉ leaves
  spokes : ∀ x ∈ leaves, G.Adj center x
  independent : ∀ x ∈ leaves, ∀ y ∈ leaves, ¬ G.Adj x y

private theorem ClawShore.leaf_mem (C : ClawShore G B) {x : V} (hx : x ∈ C.leaves) : x ∈ B :=
  Eq.mpr (congrArg (fun U : Set V => x ∈ U) C.cover) (Set.mem_insert_of_mem _ hx)

private theorem ClawShore.center_mem (C : ClawShore G B) : C.center ∈ B :=
  Eq.mpr (congrArg (fun U : Set V => C.center ∈ U) C.cover) (Set.mem_insert _ _)

private theorem ClawShore.leaf_only (C : ClawShore G B) {x : V} (hx : x ∈ C.leaves) :
    ∀ y ∈ B, G.Adj x y → y = C.center := by
  intro y hy edge
  have h := Eq.mp (congrArg (fun U : Set V => y ∈ U) C.cover) hy
  rcases h with eq|hl
  · exact eq
  · exact (C.independent x hx y hl edge).elim

variable [DecidableEq V] [Fintype V]

/-- A port touching both endpoints of the first shore must miss a leaf
of the opposite claw. Otherwise the five endpoints and that port are an
induced six-vertex star. -/
private theorem port_misses_opposite_leaf (S : ThreeVertexShore G A)
    (C : ClawShore G B) (budget : treeNumber G ≤ 5)
    (offB : ∀ v ∈ D, v ∉ B) (boundA : ShoreBoundary G D A) (apart : Disjoint A B)
    {p : V} (pu : G.Adj p S.left) (pz : G.Adj p S.right) :
    ∃ t ∈ C.leaves, ¬ G.Adj p t := by
  classical
  by_contra! none
  let T := insert S.left (insert S.right C.leaves)
  have off (x : V) (xA : x ∈ A) : x ∉ C.leaves := fun h =>
    Set.disjoint_left.mp apart xA (C.leaf_mem h)
  have cnt : T.card = 5 := by
    change (insert S.left (insert S.right C.leaves)).card = _
    rw [Finset.card_insert_of_not_mem (by simp [S.lr,off _ S.left_mem]),
      Finset.card_insert_of_not_mem (off _ S.right_mem),C.three]
  have contacts (x : V) (hx : x ∈ T) : G.Adj p x := by
    simp only [T,Finset.mem_insert] at hx
    rcases hx with eq|eq|hl
    · exact eq.symm ▸ pu
    · exact eq.symm ▸ pz
    · exact none x hl
  have cross (x : V) (xA : x ∈ A) (y : V) (h : y ∈ C.leaves) : ¬ G.Adj x y :=
    shore_anticomplete offB boundA apart xA (C.leaf_mem h)
  have independent (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ T) : ¬ G.Adj x y := by
    simp only [T,Finset.mem_insert] at hx hy
    rcases hx with eq|eq|hl <;> rcases hy with eq'|eq'|hl'
    · subst x; subst y; exact G.loopless _
    · subst x; subst y; exact S.noLR
    · subst x; exact cross _ S.left_mem _ hl'
    · subst x; subst y; exact fun e => S.noLR e.symm
    · subst x; subst y; exact G.loopless _
    · subst x; exact cross _ S.right_mem _ hl'
    · subst y; exact fun e => cross _ S.left_mem _ hl e.symm
    · subst y; exact fun e => cross _ S.right_mem _ hl e.symm
    · exact C.independent _ hl _ hl'
  have six := six_le_treeNumber_of_five_independent_neighbors T p (by omega) contacts independent
  omega

omit [Fintype V] in
private theorem traceable_of_claw_sequence (S : ThreeVertexShore G A) (C : ClawShore G B)
    {p q s x y t : V}
    (pq : p ≠ q) (ps : p ≠ s) (qs : q ≠ s)
    (offA : ∀ v ∈ ({p,q,s} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,q,s} : Finset V), v ∉ B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,q,s} : Finset V))
    (leaves : C.leaves = {x,y,t}) (xy : x ≠ y) (xt : x ≠ t) (yt : y ≠ t)
    (pt : G.Adj p t) (pu : G.Adj p S.left)
    (qz : G.Adj q S.right) (qx : G.Adj q x) (sx : G.Adj s x) :
    Traceable G := by
  have cx : x ∈ C.leaves := leaves.symm ▸ (by simp : x ∈ ({x,y,t} : Finset V))
  have cy : y ∈ C.leaves := leaves.symm ▸ (by simp : y ∈ ({x,y,t} : Finset V))
  have ct : t ∈ C.leaves := leaves.symm ▸ (by simp : t ∈ ({x,y,t} : Finset V))
  let leftPorts := [p,q,s]
  let firstSide := [S.left,S.middle,S.right]
  let secondSide := [C.center,x,y,t]
  have ports (v : V) : v ∈ leftPorts ↔ v ∈ ({p,q,s} : Finset V) := by simp [leftPorts]
  have first (v : V) : v ∈ firstSide ↔ v ∈ A := by
    have f : v ∈ A ↔ v ∈ ({S.left,S.middle,S.right} : Set V) :=
      Iff.of_eq (congrArg (fun U : Set V => v ∈ U) S.shape)
    rw [f]
    simp [firstSide]
  have second (v : V) : v ∈ secondSide ↔ v ∈ B := by
    have f : v ∈ B ↔ v ∈ insert C.center (↑C.leaves : Set V) :=
      Iff.of_eq (congrArg (fun U : Set V => v ∈ U) C.cover)
    rw [f,leaves]
    simp [secondSide]
  have lp : leftPorts.Nodup := by simp [leftPorts,pq,ps,qs]
  have fs : firstSide.Nodup := by simp [firstSide,S.lm.ne,S.lr,S.mr.ne]
  have ss : secondSide.Nodup := by
    have n (v : V) (hv : v ∈ C.leaves) : C.center ≠ v := fun e => C.off (e.symm ▸ hv)
    simp [secondSide,n _ cx,n _ cy,n _ ct,xy,xt,yt]
  have nd : (leftPorts ++ firstSide ++ secondSide).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.nodup_append.mpr ⟨lp,fs,?_⟩,ss,?_⟩
    · exact fun v hp hp' => offA v ((ports v).mp hp) ((first v).mp hp')
    · intro v h₁ h₂
      rcases List.mem_append.mp h₁ with hp|ha
      · exact offB v ((ports v).mp hp) ((second v).mp h₂)
      · exact Set.disjoint_left.mp apart ((first v).mp ha) ((second v).mp h₂)
  let f : Fin 10 → V := ![p,q,s,S.left,S.middle,S.right,C.center,x,y,t]
  let order := [y,C.center,t,p,S.left,S.middle,S.right,q,x,s]
  have perm : order.Perm (leftPorts ++ firstSide ++ secondSide) := by
    exact (show ([8,6,9,0,3,4,5,1,7,2] : List (Fin 10)).Perm [0,1,2,3,4,5,6,7,8,9] by decide).map f
  have chain : order.Chain' G.Adj := by
    simp [order,List.chain'_cons,(C.spokes _ cy).symm,C.spokes _ ct,pt.symm,pu,
      S.lm,S.mr,qz.symm,qx,sx.symm]
  have all (v : V) : v ∈ order := by
    apply perm.mem_iff.mpr
    rcases cover v with ha|hb|hd
    · exact List.mem_append_left _ (List.mem_append_right _ ((first v).mpr ha))
    · exact List.mem_append_right _ ((second v).mpr hb)
    · exact List.mem_append_left _ (List.mem_append_left _ ((ports v).mpr hd))
  have ne : order ≠ [] := by simp [order]
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp
    ⟨⟨order,ne,chain,(List.Perm.nodup_iff perm).mpr nd,fun v => iff_of_true (all v) trivial⟩⟩)

variable [DecidableRel G.Adj]

/-- A twin-ended three-vertex path and an opposite claw admit a whole
spanning path even though the claw has no single spanning route. -/
theorem traceable_of_twin_path_shore_and_claw
    (S : ThreeVertexShore G A) (C : ClawShore G B) {p q s : V}
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (pq : p ≠ q) (ps : p ≠ s) (qs : q ≠ s)
    (offA : ∀ v ∈ ({p,q,s} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,q,s} : Finset V), v ∉ B)
    (boundA : ShoreBoundary G {p,q,s} A) (boundB : ShoreBoundary G {p,q,s} B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,q,s} : Finset V))
    (pu : G.Adj p S.left) (qu : G.Adj q S.left)
    (pz : G.Adj p S.right) (qz : G.Adj q S.right) :
    Traceable G := by
  classical
  obtain ⟨x,hx,px⟩ := port_misses_opposite_leaf S C budget offB boundA apart pu pz
  obtain ⟨y,hy,qy⟩ := port_misses_opposite_leaf S C budget offB boundA apart qu qz
  have two (v : V) (hv : v ∈ C.leaves) :
      2 ≤ (({p,q,s} : Finset V).filter (G.Adj v)).card :=
    at_least_two_ports_of_shore_endpoint conn boundB (C.leaf_mem hv) (C.leaf_only hv)
  have pair (v : V) (hv : v ∈ C.leaves) (no : ¬ G.Adj p v) : G.Adj q v ∧ G.Adj s v := by
    have perm : ({q,s,p} : Finset V) = {p,q,s} := by
      ext i
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    have h : 2 ≤ (({q,s,p} : Finset V).filter (G.Adj v)).card := by rw [perm]; exact two _ hv
    exact two_present_ports qs h no
  have qx := (pair x hx px).1
  have sx := (pair x hx px).2
  have sy : G.Adj s y := by
    have perm : ({p,s,q} : Finset V) = {p,q,s} := by
      ext i
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    have h : 2 ≤ (({p,s,q} : Finset V).filter (G.Adj y)).card := by rw [perm]; exact two _ hy
    exact (two_present_ports ps h qy).2
  have py : G.Adj p y := by
    have perm : ({p,s,q} : Finset V) = {p,q,s} := by
      ext i
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
    have h : 2 ≤ (({p,s,q} : Finset V).filter (G.Adj y)).card := by rw [perm]; exact two _ hy
    exact (two_present_ports ps h qy).1
  have xy : x ≠ y := fun e => qy (e ▸ qx)
  obtain ⟨t,ht,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (show ({x,y} : Finset V).card < C.leaves.card by rw [Finset.card_pair xy,C.three]; decide)
  have xt : x ≠ t := fun e => off (by simp [← e])
  have yt : y ≠ t := fun e => off (by simp [← e])
  have all : C.leaves = {x,y,t} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with e|e|e
      · exact e.symm ▸ hx
      · exact e.symm ▸ hy
      · exact e.symm ▸ ht
    · rw [C.three,Finset.card_insert_of_not_mem (by simp [xy,xt]),Finset.card_pair yt]
  by_cases pt : G.Adj p t
  · exact traceable_of_claw_sequence S C pq ps qs offA offB apart cover all xy xt yt pt pu qz qx sx
  · have perm : ({q,p,s} : Finset V) = {p,q,s} := Finset.insert_comm _ _ _
    have other : C.leaves = {y,x,t} := all.trans (Finset.insert_comm _ _ _)
    exact traceable_of_claw_sequence S C pq.symm qs ps (perm.symm ▸ offA) (perm.symm ▸ offB)
      apart (perm.symm ▸ cover) other xy.symm yt xt (pair t ht pt).1 qu pz py sy

/-- If the deleted cubic endpoint leaves a spanning path, the local
repair or the opposite-claw splice closes this exact two-component case. -/
theorem traceable_of_cubic_path_shore_and_claw
    (S : ThreeVertexShore G A) (C : ClawShore G B)
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (degree : G.degree S.left = 3) (P : PathOn G {x | x ≠ S.left}) : Traceable G := by
  classical
  by_contra no
  obtain ⟨s,sD,_,eqU,eqZ⟩ := cubic_three_vertex_shore_profile S conn size offA boundA degree P no
  have count : (D.erase s).card = 2 := by rw [Finset.card_erase_of_mem sD,size]
  obtain ⟨p,q,pq,ports⟩ := Finset.card_eq_two.mp count
  have pE : p ∈ D.erase s := ports.symm ▸ (by simp : p ∈ ({p,q} : Finset V))
  have qE : q ∈ D.erase s := ports.symm ▸ (by simp : q ∈ ({p,q} : Finset V))
  have ps := (Finset.mem_erase.mp pE).1
  have qs := (Finset.mem_erase.mp qE).1
  have frame : D = {p,q,s} := by
    rw [← Finset.insert_erase sD,ports]
    ext v
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  have adjU (v : V) (vE : v ∈ D.erase s) : G.Adj v S.left :=
    ((G.mem_neighborFinset _ _).mp (eqU.symm ▸ Finset.mem_insert_of_mem vE)).symm
  have adjZ (v : V) (vE : v ∈ D.erase s) : G.Adj v S.right :=
    ((G.mem_neighborFinset _ _).mp (eqZ.symm ▸ Finset.mem_insert_of_mem vE)).symm
  exact no (traceable_of_twin_path_shore_and_claw S C conn budget pq ps qs
    (frame ▸ offA) (frame ▸ offB) (frame ▸ boundA) (frame ▸ boundB) apart (frame ▸ cover)
    (adjU p pE) (adjU q qE) (adjZ p pE) (adjZ q qE))

/-- The minimum-order independent-cubic branch supplies the deletion
path for the induced-claw splice. -/
theorem traceable_of_minimum_cubic_path_shore_and_claw
    (S : ThreeVertexShore G A) (C : ClawShore G B)
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V)
    (ind : ∀ x y, G.degree x = 3 → G.degree y = 3 → ¬ G.Adj x y)
    (size : D.card = 3) (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (degree : G.degree S.left = 3) : Traceable G := by
  by_contra no
  obtain ⟨P⟩ := pathOn_of_traceable_delete
    (traceable_after_cubic_delete smaller conn budget order no ind degree)
  exact no (traceable_of_cubic_path_shore_and_claw S C conn budget size offA offB
    boundA boundB apart cover degree P)

#print axioms traceable_of_twin_path_shore_and_claw
#print axioms traceable_of_cubic_path_shore_and_claw
#print axioms traceable_of_minimum_cubic_path_shore_and_claw

end Graffiti199Depleted.Catalogue
