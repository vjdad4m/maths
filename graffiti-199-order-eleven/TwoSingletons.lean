import StarContacts

open private clique_or_path_of_three from CrossingOrder

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}
variable {A B : Set V} {D : Finset V}

private theorem traverses_edge {x y : V} (edge : G.Adj x y) : Traverses G {x,y} x y := by
  let P : PathOn G ({x,y} : Set V) :=
    ⟨[x,y],by simp,List.chain'_pair.mpr edge,by simp [edge.ne],fun _ => by simp⟩
  exact ⟨P,rfl,rfl⟩

variable [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Two terminal-compatible spanning routes permit one singleton at
each end of the full path. -/
theorem traceable_of_two_routes_and_two_singletons {p q t r s : V}
    (pq : p ≠ q) (pt : p ≠ t) (qt : q ≠ t)
    (rs : r ≠ s)
    (hr : CutSingleton G {p,q,t} r) (hs : CutSingleton G {p,q,t} s)
    (offA : ∀ v ∈ ({p,q,t} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,q,t} : Finset V), v ∉ B)
    (rA : r ∉ A) (rB : r ∉ B) (sA : s ∉ A) (sB : s ∉ B)
    (apart : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,q,t} : Finset V) ∨ v = r ∨ v = s)
    (routeA : ShoreRoute G A p q) (routeB : ShoreRoute G B q t) : Traceable G := by
  obtain ⟨a,a',pa,aq,P⟩ := routeA
  obtain ⟨b,b',qb,bt,Q⟩ := routeB
  have rp : G.Adj r p := (hr.2 _).mpr (by simp)
  have ts : G.Adj t s := ((hs.2 _).mpr (by simp)).symm
  have disA : Disjoint ({r,p} : Set V) A := by
    intro U hU hA
    exact (Set.disjoint_left.mpr (fun v h h' => by
      rcases (show v = r ∨ v = p from h) with e|e
      · exact rA (e ▸ h')
      · exact offA p (by simp) (e ▸ h'))) hU hA
  have disB : Disjoint ({q} : Set V) B :=
    Set.disjoint_left.mpr (fun v h h' => offB q (by simp) ((show v = q from h) ▸ h'))
  have disEnd : Disjoint (({q} : Set V) ∪ B) {t,s} := by
    apply Set.disjoint_left.mpr
    intro v hv h
    rcases hv with qV|bV <;> rcases (show v = t ∨ v = s from h) with e|e
    · exact qt ((show v = q from qV).symm.trans e)
    · have eq := (show v = q from qV).symm.trans e
      exact hs.1 (by simp [← eq])
    · exact offB t (by simp) (e ▸ bV)
    · exact sB (e ▸ bV)
  have disBoth : Disjoint (({r,p} : Set V) ∪ A) ((({q} : Set V) ∪ B) ∪ {t,s}) := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    rcases hv with rpV|aV <;> rcases hw with (qV|bV)|tsV
    · rcases (show v = r ∨ v = p from rpV) with e|e
      · exact hr.1 (by simp [← e,(show v = q from qV)])
      · exact pq (e.symm.trans (show v = q from qV))
    · rcases (show v = r ∨ v = p from rpV) with e|e
      · exact rB (e ▸ bV)
      · exact offB p (by simp) (e ▸ bV)
    · rcases (show v = r ∨ v = p from rpV) with e|e <;>
        rcases (show v = t ∨ v = s from tsV) with f|f
      · exact hr.1 (by simp [e.symm.trans f])
      · exact rs (e.symm.trans f)
      · exact pt (e.symm.trans f)
      · exact hs.1 (by simp [← e.symm.trans f])
    · exact offA q (by simp) ((show v = q from qV) ▸ aV)
    · exact Set.disjoint_left.mp apart aV bV
    · rcases (show v = t ∨ v = s from tsV) with e|e
      · exact offA t (by simp) (e ▸ aV)
      · exact sA (e ▸ aV)
  have full : ((({r,p} : Set V) ∪ A) ∪ ((({q} : Set V) ∪ B) ∪ {t,s})) = Set.univ := by
    ext v
    have h := cover v
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_univ,iff_true]
    tauto
  have P₁ := (traverses_edge rp).join P disA pa
  have Q₁ := (Traverses.single q).join Q disB qb
  have Q₂ := Q₁.join (traverses_edge ts) disEnd bt
  obtain ⟨L,_,_⟩ := full ▸ P₁.join Q₂ disBoth aq
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨L⟩)

variable [DecidableRel G.Adj]

/-- The eleven-vertex split into two order-three components and two
singletons is traceable. The star budget forces both large components
to be cliques, and Hall supplies the two compatible routes. -/
theorem traceable_of_two_three_shores_and_two_singletons
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B)
    {r s : V} (rs : r ≠ s) (hr : CutSingleton G D r) (hs : CutSingleton G D s)
    (rA : r ∉ A) (rB : r ∉ B) (sA : s ∉ A) (sB : s ∉ B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D ∨ v = r ∨ v = s)
    (connA : (G.induce A).Connected) (connB : (G.induce B).Connected)
    (nA : Nat.card A = 3) (nB : Nat.card B = 3) : Traceable G := by
  classical
  obtain ⟨a⟩ := connA.nonempty
  obtain ⟨b⟩ := connB.nonempty
  have clA : A.Pairwise G.Adj := by
    rcases clique_or_path_of_three connA nA with clique|path
    · exact clique
    · obtain ⟨P⟩ := path
      exact (no_three_vertex_path_with_two_singleton_components P conn budget size
        offA offB boundA boundB apart ⟨b.val,b.property⟩ rs hr hs rA rB sA sB).elim
  have clB : B.Pairwise G.Adj := by
    rcases clique_or_path_of_three connB nB with clique|path
    · exact clique
    · obtain ⟨P⟩ := path
      exact (no_three_vertex_path_with_two_singleton_components P conn budget size
        offB offA boundB boundA apart.symm ⟨a.val,a.property⟩ rs hr hs rB rA sB sA).elim
  obtain ⟨f,hf⟩ := shore_distinct_attachments conn size offA boundA (by omega) ⟨r,rA,hr.1⟩
  obtain ⟨g,hg⟩ := shore_distinct_attachments conn size offB boundB (by omega) ⟨r,rB,hr.1⟩
  obtain ⟨p,q,t,pq,pt,qt,eq⟩ := Finset.card_eq_three.mp size
  subst D
  have routeA := clique_shore_route clA (p := ⟨p,by simp⟩) (q := ⟨q,by simp⟩)
    (fun h => pq (congrArg Subtype.val h)) f hf
  have routeB := clique_shore_route clB (p := ⟨q,by simp⟩) (q := ⟨t,by simp⟩)
    (fun h => qt (congrArg Subtype.val h)) g hg
  exact traceable_of_two_routes_and_two_singletons pq pt qt rs hr hs offA offB rA rB sA sB
    apart cover routeA routeB

#print axioms traceable_of_two_routes_and_two_singletons
#print axioms traceable_of_two_three_shores_and_two_singletons

end Graffiti199Depleted.Catalogue
