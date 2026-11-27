import ContractOmission

namespace Graffiti199Depleted

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- In a path missing one vertex, any visit to two consecutive
neighbors of that vertex permits its insertion. -/
theorem traceable_of_omission_between_neighbors [DecidableEq V]
    {z : V} (p : PathOn G {v | v ≠ z})
    {L R : List V} {x y : V}
    (split : p.vertices = L ++ x :: y :: R)
    (xz : G.Adj x z) (zy : G.Adj z y) :
    Catalogue.Traceable G := by
  have oldChain := p.chain
  rw [split] at oldChain
  have rChain : (y :: R).Chain' G.Adj := oldChain.right_of_append.tail
  have newSuffix : (x :: z :: y :: R).Chain' G.Adj :=
    List.chain'_cons.mpr ⟨xz,List.chain'_cons.mpr ⟨zy,rChain⟩⟩
  have newChain : (L ++ x :: z :: y :: R).Chain' G.Adj := by
    apply oldChain.left_of_append.append newSuffix
    intro s hs t ht
    exact (List.chain'_append.mp oldChain).2.2 s hs t ht
  have off : z ∉ L ++ x :: y :: R := by
    rw [← split,p.covers]
    exact fun h => h rfl
  have zOffL : z ∉ L := fun h => off (List.mem_append_left _ h)
  have zOffR : z ∉ x :: y :: R := fun h => off (List.mem_append_right _ h)
  have oldND := p.nodup
  rw [split] at oldND
  obtain ⟨nL,nR,dis⟩ := List.nodup_append.mp oldND
  obtain ⟨xOff,nY⟩ := List.nodup_cons.mp nR
  have nZ : (z :: y :: R).Nodup :=
    List.nodup_cons.mpr ⟨fun h => zOffR (List.mem_cons_of_mem _ h),nY⟩
  have nX : (x :: z :: y :: R).Nodup := by
    refine List.nodup_cons.mpr ⟨?_,nZ⟩
    intro h
    rcases List.mem_cons.mp h with eq|hy
    · exact xz.ne eq
    · exact xOff hy
  have newND : (L ++ x :: z :: y :: R).Nodup := by
    refine nL.append nX (List.disjoint_left.mpr ?_)
    intro v vL vR
    rcases List.mem_cons.mp vR with eq|after
    · exact List.disjoint_left.mp dis vL (List.mem_cons.mpr (Or.inl eq))
    · rcases List.mem_cons.mp after with eq|rest
      · exact zOffL (eq ▸ vL)
      · exact List.disjoint_left.mp dis vL (List.mem_cons_of_mem _ rest)
  have covers (v : V) : v ∈ L ++ x :: z :: y :: R := by
    by_cases eq : v = z
    · simp [eq]
    · have prev := (p.covers v).mpr eq
      rw [split] at prev
      simpa [List.mem_append,List.mem_cons,eq] using prev
  have ine : (L ++ x :: z :: y :: R) ≠ [] := by simp [List.append_eq_nil_iff]
  apply Catalogue.traceable_iff_hamiltonian_walk.mpr
  apply pathOn_univ_iff_hamiltonian_walk.mp
  exact ⟨⟨_,ine,newChain,newND,fun v => iff_of_true (covers v) trivial⟩⟩

/-- The omitted vertex has no link to either endpoint and its
neighbors are never consecutive along a one-omission path. -/
structure ConstrainedOmission (z : V) (p : PathOn G {v | v ≠ z}) : Prop where
  firstOff : ¬ G.Adj z p.first
  lastOff : ¬ G.Adj z p.last
  transitionOff : ∀ (L R : List V) (x y : V), p.vertices = L ++ x :: y :: R →
    ¬ (G.Adj z x ∧ G.Adj z y)

theorem omission_constraints [DecidableEq V] (noTrace : ¬ Catalogue.Traceable G)
    {z : V} (p : PathOn G {v | v ≠ z}) : ConstrainedOmission z p := by
  let q : PathOn G ({z} : Set V) :=
    ⟨[z],by simp,by simp,by simp,fun x => by simp⟩
  have first : q.first = z := rfl
  have last : q.last = z := rfl
  have dis : Disjoint ({z} : Set V) {v | v ≠ z} :=
    Set.disjoint_left.mpr (by intro x hx h; exact h hx)
  have all : ({z} : Set V) ∪ {v | v ≠ z} = Set.univ := by
    ext x
    simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_setOf_eq,Set.mem_univ,iff_true]
    exact Classical.em (x = z)
  have all' : {v | v ≠ z} ∪ ({z} : Set V) = Set.univ := (Set.union_comm _ _).trans all
  have trace (q : PathOn G Set.univ) : Catalogue.Traceable G :=
    Catalogue.traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨q⟩)
  refine ⟨?_,?_,?_⟩
  · intro e
    exact noTrace (trace (all ▸ q.join p dis (last.symm ▸ e)))
  · intro e
    exact noTrace (trace (all' ▸ p.join q dis.symm (first.symm ▸ e.symm)))
  · rintro L R x y split ⟨a,b⟩
    exact noTrace (traceable_of_omission_between_neighbors p split a.symm b)

namespace ContractedEdge

variable (E : ContractedEdge G)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every cubic edge of the minimal counterexample has an end that
can be omitted by a path visiting every other vertex, with the
endpoint and transition constraints imposed by nontraceability. -/
theorem minimum_cubic_edge_constrained_omission
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card V)
    (da : G.degree E.a = 3) (db : G.degree E.b = 3)
    (noTrace : ¬ Catalogue.Traceable G) :
    ∃ z : V, (z = E.a ∨ z = E.b) ∧ ∃ p : PathOn G {x | x ≠ z}, ConstrainedOmission z p := by
  rcases E.minimum_cubic_edge_one_omission smaller conn cross budget order da db noTrace with a|b
  · obtain ⟨p⟩ := a
    exact ⟨E.a,Or.inl rfl,p,omission_constraints noTrace p⟩
  · obtain ⟨p⟩ := b
    exact ⟨E.b,Or.inr rfl,p,omission_constraints noTrace p⟩

#print axioms minimum_cubic_edge_constrained_omission

end ContractedEdge

end Graffiti199Depleted
