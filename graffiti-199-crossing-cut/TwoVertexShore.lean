import FilledPath

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}

private theorem singleton_of_isolated_member {L : List V} {x : V}
    (chain : L.Chain' G.Adj) (mem : x ∈ L) (iso : ∀ y ∈ L, ¬ G.Adj x y) :
    L = [x] := by
  induction L with
  | nil => exact (List.not_mem_nil mem).elim
  | cons a L ih =>
    cases L with
    | nil => simp_all
    | cons b T =>
      have edge := chain.rel_head
      rcases List.mem_cons.mp mem with xa|tail
      · subst x
        exact (iso b (by simp) edge).elim
      · have same := ih chain.tail tail (fun y h => iso y (List.mem_cons_of_mem _ h))
        have bx : b = x := (List.cons.inj same).1
        exact (iso a (by simp) (bx ▸ edge.symm)).elim

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem traceable_of_actual_two_shore_path {x z : V} {D : Finset V}
    (p : FilledPath G (G.neighborFinset z) z) (actual : p.vertices.Chain' G.Adj)
    (xz : G.Adj x z) (xout : ∀ v, v ≠ z → G.Adj x v → v ∈ D)
    (oneMiss : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → G.Adj z a ∨ G.Adj z b) :
    Traceable G := by
  obtain ⟨L,R,form⟩ := List.append_of_mem ((p.covers x).mpr xz.ne)
  have real : (L ++ x :: R).Chain' G.Adj := form ▸ actual
  cases L with
  | nil =>
    apply traceable_from_augmented_fill p (List.Perm.refl _)
    rw [form]
    exact List.chain'_cons.mpr ⟨xz.symm,real⟩
  | cons l L =>
    cases R with
    | nil =>
      let P := ((l :: L) ++ [x]) ++ [z]
      have added : P.Chain' G.Adj := by
        apply real.append (List.chain'_singleton _)
        intro a ha b hb
        have ax : x = a := by
          rw [List.getLast?_append_of_ne_nil _ (by simp)] at ha
          simpa using ha
        have bz : z = b := by simpa using hb
        exact ax ▸ bz ▸ xz
      apply traceable_from_augmented_fill p (L := P) _ added
      simpa only [P,form,List.append_assoc,List.cons_append,List.nil_append] using
        (List.perm_middle (a := z) (l₁ := (l :: L) ++ [x]) (l₂ := []))
    | cons b R =>
      have nonempty : l :: L ≠ [] := by simp
      let A := (l :: L).dropLast
      let a := (l :: L).getLast nonempty
      have preceding : A ++ [a] = l :: L := List.dropLast_append_getLast nonempty
      have form' : p.vertices = A ++ a :: x :: b :: R := by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using
          (form.trans (congrArg (fun q : List V => q ++ x :: b :: R) preceding.symm))
      have ch : (A ++ a :: x :: b :: R).Chain' G.Adj := form' ▸ actual
      obtain ⟨left,ax,tail⟩ := List.chain'_append_cons_cons.mp ch
      obtain ⟨xb,right⟩ := List.chain'_cons.mp tail
      have nd := (List.nodup_append.mp (form' ▸ p.nodup)).2.1
      have aNot : a ≠ z := (p.covers a).mp (by simp [form'])
      have bNot : b ≠ z := (p.covers b).mp (by simp [form'])
      have distinct : a ≠ b := fun eq => (List.nodup_cons.mp nd).1 (by simp [eq])
      rcases oneMiss a (xout a aNot ax.symm) b (xout b bNot xb) distinct with za|zb
      · exact traceable_of_single_fill p form' ((G.mem_neighborFinset _ _).mpr za)
          ((G.mem_neighborFinset _ _).mpr xz.symm) left tail
      · have second : p.vertices = (A ++ [a]) ++ x :: b :: R := by
          simpa only [List.append_assoc,List.cons_append,List.nil_append] using form'
        have before := List.chain'_split.mp ch
        have middle : ((A ++ [a]) ++ [x]).Chain' G.Adj := by
          apply before.1.append (List.chain'_singleton _)
          intro u hu v hv
          have au : a = u := by simpa using hu
          have xv : x = v := by simpa using hv
          exact au ▸ xv ▸ ax
        exact traceable_of_single_fill p second ((G.mem_neighborFinset _ _).mpr xz.symm)
          ((G.mem_neighborFinset _ _).mpr zb) middle right

private theorem traceable_of_double_fill_two_shore {x z : V} {D : Finset V}
    (p : FilledPath G (G.neighborFinset z) z) (xz : G.Adj x z)
    (xout : ∀ v, v ≠ z → G.Adj x v → v ∈ D)
    (xall : ∀ v ∈ D, G.Adj x v) (xD : x ∉ D)
    {L R : List V} {a b c : V} (form : p.vertices = L ++ a :: b :: c :: R)
    (left : (L ++ [a]).Chain' G.Adj) (right : (c :: R).Chain' G.Adj)
    (ports : ∀ v, v ∈ D ↔ v = a ∨ v = b ∨ v = c)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c) : Traceable G := by
  have aD := (ports a).mpr (Or.inl rfl)
  have bD := (ports b).mpr (Or.inr (Or.inl rfl))
  have cD := (ports c).mpr (Or.inr (Or.inr rfl))
  have xa := xall a aD
  have xb := xall b bD
  have xc := xall c cD
  have nd := List.nodup_append.mp (form ▸ p.nodup)
  have offL (v : V) (hv : v ∈ L) : v ∉ D := by
    intro h
    rcases (ports v).mp h with rfl|rfl|rfl
    · exact nd.2.2 hv (by simp)
    · exact nd.2.2 hv (by simp)
    · exact nd.2.2 hv (by simp)
  have offR (v : V) (hv : v ∈ R) : v ∉ D := by
    intro h
    have dn := nd.2.1
    rcases (ports v).mp h with rfl|rfl|rfl
    · exact (List.nodup_cons.mp dn).1 (by simp [hv])
    · exact (List.nodup_cons.mp (List.nodup_cons.mp dn).2).1 (by simp [hv])
    · exact (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp dn).2).2).1 hv
  have xLR : x ∈ L ∨ x ∈ R := by
    have mem := (p.covers x).mpr xz.ne
    rw [form,List.mem_append] at mem
    rcases mem with l|r
    · exact Or.inl l
    · rcases (show x = a ∨ x = b ∨ x = c ∨ x ∈ R by simpa using r) with eq|eq|eq|hr
      · exact (xD (eq.symm ▸ aD)).elim
      · exact (xD (eq.symm ▸ bD)).elim
      · exact (xD (eq.symm ▸ cD)).elim
      · exact Or.inr hr
  have presentL (v : V) (h : v ∈ L) : v ≠ z := (p.covers v).mp (by simp [form,h])
  have presentR (v : V) (h : v ∈ R) : v ≠ z := (p.covers v).mp (by simp [form,h])
  rcases xLR with xL|xR
  · have l : L = [x] := singleton_of_isolated_member left.left_of_append xL
      (fun v hv e => offL v hv (xout v (presentL v hv) e))
    let P := a :: x :: b :: z :: c :: R
    have real : P.Chain' G.Adj :=
      List.chain'_cons.mpr ⟨xa.symm,List.chain'_cons.mpr ⟨xb,
        List.chain'_cons.mpr ⟨zb.symm,List.chain'_cons.mpr ⟨zc,right⟩⟩⟩⟩
    apply traceable_from_augmented_fill p (L := P) _ real
    have move : P.Perm (z :: a :: x :: b :: c :: R) :=
      List.perm_middle (a := z) (l₁ := [a,x,b]) (l₂ := c :: R)
    simpa only [form,l,List.cons_append,List.nil_append] using
      move.trans ((List.Perm.swap x a (b :: c :: R)).cons z)
  · have r : R = [x] := singleton_of_isolated_member right.tail xR
      (fun v hv e => offR v hv (xout v (presentR v hv) e))
    let P := L ++ a :: z :: b :: x :: c :: []
    have real : P.Chain' G.Adj := by
      apply List.chain'_split.mpr
      exact ⟨left,List.chain'_cons.mpr ⟨za.symm,List.chain'_cons.mpr ⟨zb,
        List.chain'_cons.mpr ⟨xb.symm,List.chain'_cons.mpr ⟨xc,List.chain'_singleton _⟩⟩⟩⟩⟩
    apply traceable_from_augmented_fill p (L := P) _ real
    have swap : P.Perm (L ++ a :: z :: b :: c :: x :: []) :=
      (((List.Perm.swap c x []).cons b).cons z |>.cons a).append_left L
    have move := List.perm_middle (a := z) (l₁ := L ++ [a]) (l₂ := [b,c,x])
    have move' : (L ++ a :: z :: b :: c :: x :: []).Perm (z :: p.vertices) := by
      simpa only [form,r,List.append_assoc,List.cons_append,List.nil_append] using move
    exact swap.trans move'

/-- A two-vertex component of a three-cut can be expanded along a spanning
path of the smoothed graph if one of its vertices sees all three ports. -/
theorem traceable_of_two_vertex_shore_with_universal {x z : V} {D : Finset V}
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (size : D.card = 3)
    (xD : x ∉ D) (xz : G.Adj x z)
    (xall : ∀ v ∈ D, G.Adj x v)
    (boundary : ShoreBoundary G D ({x,z} : Set V)) : Traceable G := by
  classical
  have xout (v : V) (off : v ≠ z) (e : G.Adj x v) : v ∈ D :=
    boundary x (by simp) v (by simp [e.ne.symm,off]) e
  have zout (v : V) (off : v ≠ x) (e : G.Adj z v) : v ∈ D :=
    boundary z (by simp) v (by simp [e.ne.symm,off]) e
  let C := D.filter fun v => G.Adj z v
  have memC (v : V) : v ∈ C ↔ v ∈ D ∧ G.Adj z v := by simp [C]
  have two : 2 ≤ C.card := by
    have bound : G.neighborFinset z ⊆ insert x C := by
      intro v h
      have e := (G.mem_neighborFinset _ _).mp h
      by_cases eq : v = x
      · exact Finset.mem_insert.mpr (Or.inl eq)
      · exact Finset.mem_insert.mpr (Or.inr ((memC v).mpr ⟨zout v eq e,e⟩))
    have count := (Finset.card_le_card bound).trans (Finset.card_insert_le x C)
    rw [G.card_neighborFinset_eq_degree] at count
    have low := degree_of_small_deletion_preconnected (G := G)
      (by omega : 4 ≤ Fintype.card V) (fun E h => (conn.2 E h).preconnected) z
    omega
  have misses : (D \ C).card ≤ 1 := by
    have inc : C ⊆ D := Finset.filter_subset ..
    rw [Finset.card_sdiff inc,size]
    omega
  have oneMiss (a : V) (aD : a ∈ D) (b : V) (bD : b ∈ D) (ab : a ≠ b) :
      G.Adj z a ∨ G.Adj z b := by
    by_cases za : G.Adj z a
    · exact Or.inl za
    · by_cases zb : G.Adj z b
      · exact Or.inr zb
      · exact (ab (Finset.card_le_one_iff.mp misses
          (Finset.mem_sdiff.mpr ⟨aD,fun h => za ((memC a).mp h).2⟩)
          (Finset.mem_sdiff.mpr ⟨bD,fun h => zb ((memC b).mp h).2⟩))).elim
  obtain ⟨p⟩ := filledPath_of_traceable
    (traceable_after_smoothing_of_smaller (z := z) smaller conn budget order)
  have narrowed : p.vertices.Chain' (FilledAdj G C) := by
    apply p.chain.imp
    intro a b step
    rcases step with real|⟨ne,ha,hb⟩
    · exact Or.inl real
    have za := (G.mem_neighborFinset _ _).mp ha
    have zb := (G.mem_neighborFinset _ _).mp hb
    by_cases ax : a = x
    · exact Or.inl (ax.symm ▸ xall b (zout b (ax ▸ ne.symm) zb))
    · by_cases bx : b = x
      · exact Or.inl (bx.symm ▸ (xall a (zout a ax za)).symm)
      · exact Or.inr ⟨ne,(memC a).mpr ⟨zout a ax za,za⟩,(memC b).mpr ⟨zout b bx zb,zb⟩⟩
  have Csmall : C.card ≤ 3 := (Finset.card_le_card (Finset.filter_subset ..)).trans size.le
  rcases filled_chain_cases Csmall p.nodup narrowed with real|one|both
  · exact traceable_of_actual_two_shore_path p real xz xout oneMiss
  · obtain ⟨L,a,b,R,form,aC,bC,_,left,right⟩ := one
    exact traceable_of_single_fill p form ((G.mem_neighborFinset _ _).mpr ((memC a).mp aC).2)
      ((G.mem_neighborFinset _ _).mpr ((memC b).mp bC).2) left right
  · obtain ⟨L,a,b,c,R,form,aC,bC,cC,_,_,left,right⟩ := both
    have nd := (List.nodup_append.mp (form ▸ p.nodup)).2.1
    have ab : a ≠ b := fun h => (List.nodup_cons.mp nd).1 (by simp [h])
    have ac : a ≠ c := fun h => (List.nodup_cons.mp nd).1 (by simp [h])
    have bc : b ≠ c := fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h])
    let T : Finset V := {a,b,c}
    have inc : T ⊆ D := by
      intro v h
      rcases (show v = a ∨ v = b ∨ v = c by simpa [T] using h) with rfl|rfl|rfl
      · exact ((memC _).mp aC).1
      · exact ((memC _).mp bC).1
      · exact ((memC _).mp cC).1
    have count : T.card = 3 := by
      change (insert a ({b,c} : Finset V)).card = 3
      rw [Finset.card_insert_of_not_mem (by simp [ab,ac]),Finset.card_pair bc]
    have eq := Finset.eq_of_subset_of_card_le inc (by rw [count,size])
    exact traceable_of_double_fill_two_shore p xz xout xall xD form left right
      (fun v => by rw [← eq]; simp [T]) ((memC a).mp aC).2 ((memC b).mp bC).2 ((memC c).mp cC).2

/-- Under independent cubic vertices, an edge cannot be a whole component
of a three-cut of a nontraceable minimum-order graph. -/
theorem traceable_of_two_vertex_shore_of_independent_cubics {x z : V} {D : Finset V}
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (size : D.card = 3)
    (xD : x ∉ D) (zD : z ∉ D) (xz : G.Adj x z)
    (boundary : ShoreBoundary G D ({x,z} : Set V))
    (independent : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b) : Traceable G := by
  classical
  have min (v : V) := degree_of_small_deletion_preconnected (G := G)
    (by omega : 4 ≤ Fintype.card V) (fun E h => (conn.2 E h).preconnected) v
  have extend {a b : V} (ab : G.Adj a b) (hi : 4 ≤ G.degree a) (bD : b ∉ D)
      (bound : ShoreBoundary G D ({a,b} : Set V)) : ∀ v ∈ D, G.Adj a v := by
    have sub : G.neighborFinset a ⊆ insert b D := by
      intro v hv
      have e := (G.mem_neighborFinset _ _).mp hv
      by_cases vb : v = b
      · exact Finset.mem_insert.mpr (Or.inl vb)
      · exact Finset.mem_insert.mpr (Or.inr (bound a (by simp) v (by simp [e.ne.symm,vb]) e))
    have eq := Finset.eq_of_subset_of_card_le sub (by
      rw [Finset.card_insert_of_not_mem bD,size,G.card_neighborFinset_eq_degree]; exact hi)
    intro v h
    exact (G.mem_neighborFinset _ _).mp (eq.symm ▸ Finset.mem_insert_of_mem h)
  by_cases high : 4 ≤ G.degree x
  · exact traceable_of_two_vertex_shore_with_universal smaller conn budget order size xD xz
      (extend xz high zD boundary) boundary
  · have xd : G.degree x = 3 := by have l := min x; omega
    have zd : G.degree z ≠ 3 := fun h => independent x z xd h xz
    have zh : 4 ≤ G.degree z := by have l := min z; omega
    have swap : ShoreBoundary G D ({z,x} : Set V) := by simpa only [Set.pair_comm] using boundary
    exact traceable_of_two_vertex_shore_with_universal smaller conn budget order size zD xz.symm
      (extend xz.symm zh xD swap) swap

#print axioms traceable_of_two_vertex_shore_of_independent_cubics

end Graffiti199Depleted.Catalogue
