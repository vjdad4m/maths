import ContractEdge

namespace Graffiti199Depleted.ContractedEdge

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} (E : ContractedEdge G)
variable [DecidableEq V]

omit [DecidableEq V] in
private theorem chain_away_from_contracted {L : List E.Vertex}
    (off : (none : E.Vertex) ∉ L) (h : L.Chain' E.graph.Adj) :
    (L.map E.representative).Chain' G.Adj := by
  apply (List.chain'_map _).mpr
  apply List.Chain'.imp _ (List.Chain'.iff_mem.mp h)
  intro x y ⟨xL,yL,edge⟩
  cases x with
  | none => exact (off xL).elim
  | some x =>
    cases y with
    | none => exact (off yL).elim
    | some y => exact edge

omit [DecidableEq V] in
private theorem map_avoids_edge {L : List E.Vertex} (off : (none : E.Vertex) ∉ L)
    {x : V} (hx : x ∈ L.map E.representative) : x ≠ E.a ∧ x ≠ E.b := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
  refine ⟨?_,E.rep_ne_b v⟩
  intro eq
  have h : v = none := E.representative.injective (show E.representative v = E.representative none from eq)
  exact off (h ▸ hv)

/-- Replace the contracted vertex with the original edge in the
orientation prescribed by the two surviving links. Either link can
be absent at a path endpoint. -/
theorem lift_path (p : PathOn E.graph Set.univ) {L R : List E.Vertex}
    (split : p.vertices = L ++ none :: R)
    {a b : V} (orientation : (a = E.a ∧ b = E.b) ∨ (a = E.b ∧ b = E.a))
    (left : ∀ x ∈ L.getLast?, G.Adj (E.representative x) a)
    (right : ∀ y ∈ R.head?, G.Adj b (E.representative y)) :
    Catalogue.Traceable G := by
  have edge : G.Adj a b := by
    rcases orientation with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact E.edge
    · exact E.edge.symm
  have ends (x : V) : x ∈ [a,b] ↔ x = E.a ∨ x = E.b := by
    rcases orientation with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [or_comm]
  have first := p.chain
  rw [split] at first
  have last : R.Chain' E.graph.Adj := (first.right_of_append).tail
  have nodup := p.nodup
  rw [split] at nodup
  obtain ⟨nL,nR0,dis⟩ := List.nodup_append.mp nodup
  obtain ⟨offR,nR⟩ := List.nodup_cons.mp nR0
  have offL : none ∉ L := fun h => (List.disjoint_left.mp dis) h (List.mem_cons_self ..)
  let L' := L.map E.representative
  let R' := R.map E.representative
  have lc : L'.Chain' G.Adj := E.chain_away_from_contracted offL first.left_of_append
  have rc : R'.Chain' G.Adj := E.chain_away_from_contracted offR last
  have ab : ([a,b] : List V).Chain' G.Adj := by simp [List.chain'_cons,edge]
  have w : (L' ++ ([a,b] ++ R')).Chain' G.Adj := by
    have tail : ([a,b] ++ R').Chain' G.Adj := by
      apply ab.append rc
      intro x hx y hy
      have xeq : b = x := by simpa using hx
      subst x
      obtain ⟨z,hz,rfl⟩ := Option.mem_map.mp (by simpa only [R',List.head?_map] using hy)
      exact right z hz
    apply lc.append tail
    intro x hx y hy
    have yeq : a = y := by simpa using hy
    subst y
    obtain ⟨z,hz,rfl⟩ := Option.mem_map.mp (by simpa only [L',List.getLast?_map] using hx)
    exact left z hz
  have nd : (L' ++ ([a,b] ++ R')).Nodup := by
    have abn : ([a,b] : List V).Nodup := by simp [edge.ne]
    have tail : ([a,b] ++ R').Nodup := by
      refine abn.append (nR.map E.representative.injective) (List.disjoint_left.mpr ?_)
      intro x xEnds xR
      have off := E.map_avoids_edge offR xR
      exact ((ends x).mp xEnds).elim off.1 off.2
    refine (nL.map E.representative.injective).append tail (List.disjoint_left.mpr ?_)
    intro x xL xTail
    rcases List.mem_append.mp xTail with xEnds|xR
    · have off := E.map_avoids_edge offL xL
      exact ((ends x).mp xEnds).elim off.1 off.2
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp xL
      obtain ⟨j,hj,eq⟩ := List.mem_map.mp xR
      have ji := E.representative.injective eq
      exact List.disjoint_left.mp dis hi (List.mem_cons_of_mem _ (ji ▸ hj))
  have cover (x : V) : x ∈ L' ++ ([a,b] ++ R') := by
    have all := (p.covers (E.project x)).mpr (Set.mem_univ _)
    rw [split] at all
    by_cases endsX : x = E.a ∨ x = E.b
    · exact List.mem_append_right _ (List.mem_append_left _ ((ends x).mpr endsX))
    · have notB : x ≠ E.b := fun eq => endsX (Or.inr eq)
      have notNone : E.project x ≠ none := fun eq => endsX ((E.project_none_iff x).mp eq)
      rcases List.mem_append.mp all with l|r
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨_,l,E.rep_project x notB⟩)
      · have rest := (List.mem_cons.mp r).resolve_left notNone
        exact List.mem_append_right _ (List.mem_append_right _
          (List.mem_map.mpr ⟨_,rest,E.rep_project x notB⟩))
  apply Catalogue.traceable_iff_hamiltonian_walk.mpr
  apply pathOn_univ_iff_hamiltonian_walk.mp
  have nonempty : (L' ++ ([a,b] ++ R')) ≠ [] := by simp [List.append_eq_nil_iff]
  exact ⟨⟨_,nonempty,w,nd,fun x => iff_of_true (cover x) trivial⟩⟩

/-- In a nontraceable original graph, every spanning path of the
contraction meets the contracted vertex internally and uses both
links on the same side of the original edge. -/
theorem reduced_path_same_side (noTrace : ¬ Catalogue.Traceable G)
    (p : PathOn E.graph Set.univ) {L R : List E.Vertex}
    (split : p.vertices = L ++ none :: R) :
    ∃ x y : E.Other, L.getLast? = some (some x) ∧ R.head? = some (some y) ∧
      ((G.Adj E.a x.val ∧ G.Adj E.a y.val) ∨ (G.Adj E.b x.val ∧ G.Adj E.b y.val)) := by
  classical
  have path := p.chain
  rw [split] at path
  have left (x : E.Vertex) (hx : x ∈ L.getLast?) : E.graph.Adj x none :=
    (List.chain'_append.mp path).2.2 x hx none (by simp)
  have right (y : E.Vertex) (hy : y ∈ R.head?) : E.graph.Adj none y :=
    path.right_of_append.rel_head? hy
  have lNone : (none : E.Vertex) ∉ L.getLast? := fun h => E.graph.loopless none (left none h)
  have rNone : (none : E.Vertex) ∉ R.head? := fun h => E.graph.loopless none (right none h)
  have liftAB (la : ∀ x ∈ L.getLast?, G.Adj (E.representative x) E.a)
      (rb : ∀ y ∈ R.head?, G.Adj E.b (E.representative y)) : False :=
    noTrace (E.lift_path p split (Or.inl ⟨rfl,rfl⟩) la rb)
  have liftBA (lb : ∀ x ∈ L.getLast?, G.Adj (E.representative x) E.b)
      (ra : ∀ y ∈ R.head?, G.Adj E.a (E.representative y)) : False :=
    noTrace (E.lift_path p split (Or.inr ⟨rfl,rfl⟩) lb ra)
  have Lcases : L.getLast? = none ∨ ∃ x : E.Other, L.getLast? = some (some x) := by
    cases e : L.getLast? with
    | none => exact Or.inl rfl
    | some o =>
      cases o with
      | none => exact (lNone (by simp [e])).elim
      | some o => exact Or.inr ⟨o,rfl⟩
  have Rcases : R.head? = none ∨ ∃ y : E.Other, R.head? = some (some y) := by
    cases e : R.head? with
    | none => exact Or.inl rfl
    | some o =>
      cases o with
      | none => exact (rNone (by simp [e])).elim
      | some o => exact Or.inr ⟨o,rfl⟩
  have LeftA {x : E.Other} (h : L.getLast? = some (some x)) (e : G.Adj E.a x.val) :
      ∀ z ∈ L.getLast?, G.Adj (E.representative z) E.a := by simpa [h] using e.symm
  have LeftB {x : E.Other} (h : L.getLast? = some (some x)) (e : G.Adj E.b x.val) :
      ∀ z ∈ L.getLast?, G.Adj (E.representative z) E.b := by simpa [h] using e.symm
  have RightA {y : E.Other} (h : R.head? = some (some y)) (e : G.Adj E.a y.val) :
      ∀ z ∈ R.head?, G.Adj E.a (E.representative z) := by simpa [h] using e
  have RightB {y : E.Other} (h : R.head? = some (some y)) (e : G.Adj E.b y.val) :
      ∀ z ∈ R.head?, G.Adj E.b (E.representative z) := by simpa [h] using e
  have goLeft (x : E.Other) (h : L.getLast? = some (some x)) :
      G.Adj E.a x.val ∨ G.Adj E.b x.val := left (some x) (by simp [h])
  have goRight (y : E.Other) (h : R.head? = some (some y)) :
      G.Adj E.a y.val ∨ G.Adj E.b y.val := right (some y) (by simp [h])
  rcases Lcases with emptyL|⟨x,l⟩
  · rcases Rcases with emptyR|⟨y,r⟩
    · exact (liftAB (by simp [emptyL]) (by simp [emptyR])).elim
    · rcases goRight y r with a|b
      · exact (liftBA (by simp [emptyL]) (RightA r a)).elim
      · exact (liftAB (by simp [emptyL]) (RightB r b)).elim
  · rcases Rcases with emptyR|⟨y,r⟩
    · rcases goLeft x l with a|b
      · exact (liftAB (LeftA l a) (by simp [emptyR])).elim
      · exact (liftBA (LeftB l b) (by simp [emptyR])).elim
    · refine ⟨x,y,l,r,?_⟩
      rcases goLeft x l with a|b <;> rcases goRight y r with c|d
      · exact Or.inl ⟨a,c⟩
      · exact (liftAB (LeftA l a) (RightB r d)).elim
      · exact (liftBA (LeftB l b) (RightA r c)).elim
      · exact Or.inr ⟨b,d⟩

#print axioms lift_path
#print axioms reduced_path_same_side

end Graffiti199Depleted.ContractedEdge
