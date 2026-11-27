import ShoreRouting

open private triangle_absurd from CutTorsoBudget

namespace Graffiti199Depleted.Catalogue.HighCutRoutingWitness

open SimpleGraph

abbrev ports : Finset (Fin 9) := {0,1,2}
abbrev left : Set (Fin 9) := ↑({3,4,5} : Finset (Fin 9))
abbrev right : Set (Fin 9) := ↑({6,7,8} : Finset (Fin 9))

private def universal (x : Fin 9) : Prop := x = 0 ∨ x = 1
private def core (x : Fin 9) : Prop := x = 2 ∨ 6 ≤ x.val
private def spoke (x : Fin 9) : Prop := x = 2 ∨ x = 3 ∨ x = 5

instance (x : Fin 9) : Decidable (universal x) := inferInstanceAs (Decidable (_ ∨ _))
instance (x : Fin 9) : Decidable (core x) := inferInstanceAs (Decidable (_ ∨ _))
instance (x : Fin 9) : Decidable (spoke x) := inferInstanceAs (Decidable (_ ∨ _))

/-- Ports zero and one are universal. Port two only sees the middle of the
three-vertex path shore, and all three vertices of the clique shore. -/
def graph : SimpleGraph (Fin 9) where
  Adj x y := x ≠ y ∧ (universal x ∨ universal y ∨ (core x ∧ core y) ∨
    (x = 4 ∧ spoke y) ∨ (y = 4 ∧ spoke x))
  symm := by
    intro x y
    simp only
    tauto
  loopless := fun _ h => h.1 rfl

instance graphAdjDecidable : DecidableRel graph.Adj := by
  intro x y
  change Decidable (x ≠ y ∧ (universal x ∨ universal y ∨ (core x ∧ core y) ∨
    (x = 4 ∧ spoke y) ∨ (y = 4 ∧ spoke x)))
  infer_instance

theorem connectivity : ConnectivityAtLeast graph 3 := by
  refine ⟨by decide,?_⟩
  intro D small
  by_cases existsHub : ∃ p : Fin 9, universal p ∧ p ∉ D
  · obtain ⟨p,hub,off⟩ := existsHub
    let P : Survives D := ⟨p,off⟩
    refine @SimpleGraph.Connected.mk _ (DeletionGraph graph D) ?_ ⟨P⟩
    intro a b
    have attach (x : Survives D) : (DeletionGraph graph D).Reachable x P := by
      by_cases eq : x.val = p
      · exact (show x = P from Subtype.ext eq) ▸ .rfl
      · exact (show (DeletionGraph graph D).Adj x P from ⟨eq,Or.inr (Or.inl hub)⟩).reachable
    exact (attach a).trans (attach b).symm
  have both : ({0,1} : Finset (Fin 9)) ⊆ D := by
    intro p h
    by_contra off
    have uni : universal p := (show ∀ x ∈ ({0,1} : Finset (Fin 9)), universal x by decide) p h
    exact existsHub ⟨p,uni,off⟩
  have eq : ({0,1} : Finset (Fin 9)) = D := Finset.eq_of_subset_of_card_le both
    (by rw [show ({0,1} : Finset (Fin 9)).card = 2 by decide]; omega)
  rw [← eq]
  let P : Survives ({0,1} : Finset (Fin 9)) := ⟨2,by decide⟩
  let M : Survives ({0,1} : Finset (Fin 9)) := ⟨4,by decide⟩
  refine @SimpleGraph.Connected.mk _ (DeletionGraph graph {0,1}) ?_ ⟨P⟩
  intro a b
  have attach (x : Survives ({0,1} : Finset (Fin 9))) :
      (DeletionGraph graph {0,1}).Reachable x P := by
    have localModes : ∀ v : Fin 9, v ∉ ({0,1} : Finset (Fin 9)) →
        v = 2 ∨ graph.Adj v 2 ∨ graph.Adj v 4 := by decide
    rcases localModes x.val x.property with e|e|e
    · exact (show x = P from Subtype.ext e) ▸ .rfl
    · exact (show (DeletionGraph graph {0,1}).Adj x P from e).reachable
    · exact (show (DeletionGraph graph {0,1}).Adj x M from e).reachable.trans
        (show (DeletionGraph graph {0,1}).Adj M P by decide).reachable
  exact (attach a).trans (attach b).symm

theorem no_crossing : ¬ CrossingBetweenSurvivingEdges graph := by
  intro cross
  have banned : ∀ x y : Fin 9, x ∈ left → y ∉ left → y ∉ ports → ¬ graph.Adj x y := by decide
  obtain ⟨x,xA,y,yA,_,yD,xy⟩ := cross ports (by decide) left
    ⟨3,by decide,4,by decide,by decide,by decide,by decide⟩
    ⟨6,by decide,7,by decide,by decide,by decide,by decide⟩
  exact banned x y xA yA yD xy

theorem exact_connectivity : vertexConnectivity graph = 3 := by
  classical
  have ge : 3 ≤ vertexConnectivity graph := by
    unfold vertexConnectivity
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by decide),connectivity⟩)
  have le : vertexConnectivity graph ≤ 3 := by
    by_contra! h
    apply no_crossing
    apply edgeReach_iff_crossing_between_surviving_edges.mp
    intro D small a _ c _ _ _
    exact ((connectivityAtLeast_vertexConnectivity (G := graph)).2 D (by omega)).preconnected a c
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem large_triangle :
    ∀ S : Finset (Fin 9), 6 ≤ S.card →
      ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, graph.Adj a b ∧ graph.Adj a c ∧ graph.Adj c b := by
  decide +kernel

theorem budget : treeNumber graph ≤ 5 := by
  classical
  unfold treeNumber
  apply Finset.sup_le
  intro S h
  change S.card ≤ 5
  by_cases high : 6 ≤ S.card
  · obtain ⟨a,aS,b,bS,c,cS,ab,ac,cb⟩ := large_triangle S high
    let H := graph.induce (↑S : Set (Fin 9))
    have tree : H.IsTree := (Finset.mem_filter.mp h).2
    exact (triangle_absurd tree
      (show H.Adj ⟨a,aS⟩ ⟨b,bS⟩ from ab) (show H.Adj ⟨a,aS⟩ ⟨c,cS⟩ from ac)
      (show H.Adj ⟨c,cS⟩ ⟨b,bS⟩ from cb)).elim
  · omega

theorem port_high : ∀ p ∈ ports, 4 ≤ graph.degree p := by decide +kernel
theorem cubics : ∀ v : Fin 9, graph.degree v = 3 ↔ v = 3 ∨ v = 5 := by decide +kernel
theorem independent_cubics : ∀ a b, graph.degree a = 3 → graph.degree b = 3 → ¬ graph.Adj a b := by
  decide +kernel

theorem left_hall : ∃ f : ↥ports ↪ left, ∀ p : ports, graph.Adj p.val (f p).val := by
  apply shore_distinct_attachments connectivity (by decide) (by decide)
  · unfold ShoreBoundary
    decide
  · rw [Nat.card_eq_fintype_card]
    decide
  · exact ⟨6,by decide,by decide⟩

/-- An exactly three-vertex nonclique shore can fail every route from
one of its ports, despite the Hall certificate and all-high cut. -/
theorem no_route_from_two (q : Fin 9) : ¬ ShoreRoute graph left 2 q := by
  rintro ⟨a,b,entry,_,P,first,_⟩
  have aMem : a ∈ left := (P.covers a).mp (first ▸ List.head_mem P.nonempty)
  have aEq : a = 4 := (show ∀ v : Fin 9, v ∈ left → graph.Adj 2 v → v = 4 by decide) a aMem entry
  have eq : P.vertices.toFinset = ({3,4,5} : Finset (Fin 9)) := by
    ext x
    rw [List.mem_toFinset,P.covers]
    rfl
  have count : P.vertices.length = 3 := by
    rw [← List.toFinset_card_of_nodup P.nodup,eq]
    decide
  obtain ⟨c,d,e,form⟩ := List.length_eq_three.mp count
  have cf : c = 4 := by
    change P.vertices.head P.nonempty = a at first
    have start : P.vertices.head P.nonempty = c :=
      (List.head_eq_iff_head?_eq_some P.nonempty).mpr (by simp [form])
    exact start.symm.trans (first.trans aEq)
  subst c
  have dL : d ∈ left := (P.covers d).mp (by simp [form])
  have eL : e ∈ left := (P.covers e).mp (by simp [form])
  have nd := P.nodup
  rw [form] at nd
  have hd : d ≠ 4 := fun he => (List.nodup_cons.mp nd).1 (by simp [he])
  have he : e ≠ 4 := fun he => (List.nodup_cons.mp nd).1 (by simp [he])
  have chain := P.chain
  rw [form] at chain
  have de : graph.Adj d e := chain.tail.rel_head
  exact (show ∀ v w : Fin 9, v ∈ left → w ∈ left → v ≠ 4 → w ≠ 4 → ¬ graph.Adj v w by decide)
    d e dL eL hd he de

theorem route_zero_one : ShoreRoute graph left 0 1 := by
  let P : PathOn graph left := ⟨[3,4,5],by simp,by decide,by decide,fun v => by
    fin_cases v <;> decide⟩
  exact ⟨3,5,by decide,by decide,P,rfl,rfl⟩

/-- The path shore supports exactly the pair of ports zero and one. -/
theorem left_routes {p q : Fin 9} (hp : p ∈ ports) (hq : q ∈ ports) (ne : p ≠ q) :
    ShoreRoute graph left p q ↔ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0) := by
  constructor
  · intro route
    have p2 : p ≠ 2 := fun eq => no_route_from_two q (eq ▸ route)
    have q2 : q ≠ 2 := fun eq => no_route_from_two p (eq ▸ route.reverse)
    exact (show ∀ p q : Fin 9, p ∈ ports → q ∈ ports → p ≠ q → p ≠ 2 → q ≠ 2 →
      (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0) by decide) p q hp hq ne p2 q2
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact route_zero_one
    · exact route_zero_one.reverse

theorem right_routes {p q : Fin 9} (hp : p ∈ ports) (hq : q ∈ ports) (ne : p ≠ q) :
    ShoreRoute graph right p q := by
  have clique : right.Pairwise graph.Adj := by unfold Set.Pairwise; decide
  have direct : ∃ f : ↥ports ↪ right, ∀ p : ports, graph.Adj p.val (f p).val := by
    apply shore_distinct_attachments connectivity (by decide) (by decide)
    · unfold ShoreBoundary
      decide
    · rw [Nat.card_eq_fintype_card]
      decide
    · exact ⟨3,by decide,by decide⟩
  obtain ⟨f,edges⟩ := direct
  exact clique_shore_route clique (p := ⟨p,hp⟩) (q := ⟨q,hq⟩)
    (fun h => ne (congrArg Subtype.val h)) f edges

abbrev blockedDomain : Finset (Fin 9) := {2,3,4,5}
abbrev blockedGraph := graph.induce (↑blockedDomain : Set (Fin 9))

instance blockedAdjDecidable : DecidableRel blockedGraph.Adj := fun x y =>
  graphAdjDecidable x.val y.val

/-- In the obstructed one-terminal domain, the rooted Ore threshold
fails at every missing edge. -/
theorem no_rooted_ore_step :
    ∀ x y : ↥blockedDomain, x ≠ y → ¬ blockedGraph.Adj x y →
      blockedGraph.degree x + blockedGraph.degree y < Fintype.card (↥blockedDomain) := by
  decide +kernel

theorem traceable : Traceable graph := by
  apply traceable_iff_hamiltonian_walk.mpr
  apply pathOn_univ_iff_hamiltonian_walk.mp
  refine ⟨⟨[3,4,5,0,6,7,8,2,1],by simp,by decide,by decide,?_⟩⟩
  intro v
  change v ∈ ([3,4,5,0,6,7,8,2,1] : List (Fin 9)) ↔ True
  fin_cases v <;> decide

#print axioms exact_connectivity
#print axioms no_crossing
#print axioms budget
#print axioms port_high
#print axioms independent_cubics
#print axioms left_hall
#print axioms no_route_from_two
#print axioms left_routes
#print axioms right_routes
#print axioms no_rooted_ore_step
#print axioms traceable

end Graffiti199Depleted.Catalogue.HighCutRoutingWitness
