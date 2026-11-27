import ShoreHall

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V]
variable {D : Finset V} {A B : Set V}

/-- A path spanning the shore and attachable to the indicated ordered pair
of ports. The path's vertex set is precisely the shore. -/
def ShoreRoute (G : SimpleGraph V) (A : Set V) (p q : V) : Prop :=
  ∃ x y, G.Adj p x ∧ G.Adj y q ∧ Traverses G A x y

omit [Fintype V] in
theorem ShoreRoute.reverse {p q : V} (route : ShoreRoute G A p q) : ShoreRoute G A q p := by
  obtain ⟨x,y,px,yq,path⟩ := route
  exact ⟨y,x,yq.symm,px.symm,path.reverse⟩

/-- A clique shore with the Hall attachments supports every ordered
pair of distinct terminals. -/
theorem clique_shore_route (clique : A.Pairwise G.Adj) {p q : ↥D} (ne : p ≠ q)
    (f : ↥D ↪ A) (edges : ∀ s : ↥D, G.Adj s.val (f s).val) :
    ShoreRoute G A p.val q.val :=
  ⟨(f p).val,(f q).val,edges p,(edges q).symm,
    Traverses.clique clique (f p).property (f q).property
      (fun h => ne (f.injective (Subtype.ext h)))⟩

omit [Fintype V] in
/-- Consecutive, compatible port pairs splice the two spanning shore
routes into a Hamiltonian path of the entire graph. -/
theorem traceable_of_compatible_shore_routes [DecidableEq V] {p q r : V}
    (pq : p ≠ q) (pr : p ≠ r) (qr : q ≠ r)
    (offA : ∀ v ∈ ({p,q,r} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,q,r} : Finset V), v ∉ B)
    (disjoint : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,q,r} : Finset V))
    (first : ShoreRoute G A p q) (second : ShoreRoute G B q r) : Traceable G := by
  classical
  obtain ⟨a,a',pa,aq,L⟩ := first
  obtain ⟨b,b',qb,br,R⟩ := second
  have sep₁ : Disjoint ({p} : Set V) A := by
    apply Set.disjoint_left.mpr
    intro v vP
    have eq : v = p := vP
    subst v
    exact offA p (by simp)
  have sep₂ : Disjoint (({p} : Set V) ∪ A) {q} := by
    apply Set.disjoint_left.mpr
    rintro v (vp|vA) vQ
    · exact pq ((show v = p from vp).symm.trans (show v = q from vQ))
    · exact offA q (by simp) ((show v = q from vQ) ▸ vA)
  have sep₃ : Disjoint ((({p} : Set V) ∪ A) ∪ {q}) B := by
    apply Set.disjoint_left.mpr
    rintro v ((vp|vA)|vq) vB
    · exact offB p (by simp) ((show v = p from vp) ▸ vB)
    · exact Set.disjoint_left.mp disjoint vA vB
    · exact offB q (by simp) ((show v = q from vq) ▸ vB)
  have sep₄ : Disjoint (((({p} : Set V) ∪ A) ∪ {q}) ∪ B) {r} := by
    apply Set.disjoint_left.mpr
    rintro v (((vp|vA)|vq)|vB) vR
    · exact pr ((show v = p from vp).symm.trans vR)
    · exact offA r (by simp) ((show v = r from vR) ▸ vA)
    · exact qr ((show v = q from vq).symm.trans vR)
    · exact offB r (by simp) ((show v = r from vR) ▸ vB)
  have full : ((((({p} : Set V) ∪ A) ∪ {q}) ∪ B) ∪ {r}) = Set.univ := by
    ext v
    have h := cover v
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_univ,iff_true]
    tauto
  have path := ((((Traverses.single (G := G) p).join L sep₁ pa).join
    (Traverses.single q) sep₂ aq).join R sep₃ qb).join (Traverses.single r) sep₄ br
  rw [full] at path
  obtain ⟨W,_,_⟩ := path
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨W⟩)

/-- If the nonclique side has one valid terminal route, any clique on the other
side supplies the two complementary attachments needed for the splice. -/
theorem traceable_of_routable_and_clique_shores (conn : ConnectivityAtLeast G 3)
    (cutSize : D.card = 3) (offA : ∀ x ∈ D, x ∉ A) (offB : ∀ x ∈ D, x ∉ B)
    (boundB : ShoreBoundary G D B) (largeB : 3 ≤ Nat.card B)
    (disjoint : Disjoint A B) (nonempty : A.Nonempty)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D) (clique : B.Pairwise G.Adj)
    {p q : V} (pD : p ∈ D) (qD : q ∈ D) (pq : p ≠ q)
    (route : ShoreRoute G A p q) : Traceable G := by
  classical
  obtain ⟨a,aA⟩ := nonempty
  obtain ⟨f,edges⟩ := shore_distinct_attachments conn cutSize offB boundB largeB
    ⟨a,fun aB => Set.disjoint_left.mp disjoint aA aB,fun aD => offA a aD aA⟩
  have count : ({p,q} : Finset V).card < D.card := by rw [Finset.card_pair pq,cutSize]; decide
  obtain ⟨r,rD,rOff⟩ := Finset.exists_mem_not_mem_of_card_lt_card count
  have pr : p ≠ r := by intro eq; exact rOff (by simp [← eq])
  have qr : q ≠ r := by intro eq; exact rOff (by simp [← eq])
  have eq : ({p,q,r} : Finset V) = D := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl
      · exact pD
      · exact qD
      · exact rD
    · rw [cutSize,Finset.card_insert_of_not_mem (by simp [pq,pr]),Finset.card_pair qr]
  have rest := clique_shore_route clique (p := ⟨q,qD⟩) (q := ⟨r,rD⟩)
    (fun h => qr (congrArg Subtype.val h)) f edges
  exact traceable_of_compatible_shore_routes pq pr qr (eq.symm ▸ offA) (eq.symm ▸ offB)
    disjoint (eq.symm ▸ cover) route rest

variable [DecidableRel G.Adj]

/-- A shore vertex with a single neighbor in its own shore must see
at least two of the three cut vertices. -/
theorem at_least_two_ports_of_shore_endpoint (conn : ConnectivityAtLeast G 3)
    (boundary : ShoreBoundary G D A) {v w : V} (vA : v ∈ A)
    (only : ∀ x ∈ A, G.Adj v x → x = w) :
    2 ≤ (D.filter (G.Adj v)).card := by
  classical
  have low := degree_of_small_deletion_preconnected (G := G)
    (by have n := conn.1; omega : 4 ≤ Fintype.card V)
    (fun R hR => (conn.2 R hR).preconnected) v
  have sub : G.neighborFinset v ⊆ insert w (D.filter (G.Adj v)) := by
    intro x hx
    have edge := (G.mem_neighborFinset _ _).mp hx
    by_cases xA : x ∈ A
    · rw [only x xA edge]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨boundary _ vA _ xA edge,edge⟩)
  have up := Finset.card_le_card sub
  rw [G.card_neighborFinset_eq_degree] at up
  have h := Finset.card_insert_le w (D.filter (G.Adj v))
  omega

/-- An induced three-vertex path shore supplies at least one allowable
terminal pair. Each endpoint has at least two choices of terminal. -/
theorem three_vertex_path_shore_route
    (conn : ConnectivityAtLeast G 3) {x y z : V}
    (boundary : ShoreBoundary G D A) (shape : A = {x,y,z})
    (xy : G.Adj x y) (yz : G.Adj y z) (xz : x ≠ z) (notXZ : ¬ G.Adj x z) :
    ∃ p ∈ D, ∃ q ∈ D, p ≠ q ∧ ShoreRoute G A p q := by
  classical
  subst A
  have twoX := at_least_two_ports_of_shore_endpoint (D := D) conn boundary
    (show x ∈ ({x,y,z} : Set V) by simp) (w := y) (by
      intro v hv edge
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl|rfl
      · exact (G.loopless _ edge).elim
      · rfl
      · exact (notXZ edge).elim)
  have twoZ := at_least_two_ports_of_shore_endpoint (D := D) conn boundary
    (show z ∈ ({x,y,z} : Set V) by simp) (w := y) (by
      intro v hv edge
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
      rcases hv with rfl|rfl|rfl
      · exact (notXZ edge.symm).elim
      · rfl
      · exact (G.loopless _ edge).elim)
  obtain ⟨p,hp⟩ : (D.filter (G.Adj x)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q,hq,qp⟩ := Finset.exists_ne_of_one_lt_card (by omega : 1 < (D.filter (G.Adj z)).card) p
  obtain ⟨pD,xp⟩ := Finset.mem_filter.mp hp
  obtain ⟨qD,zq⟩ := Finset.mem_filter.mp hq
  let P : PathOn G ({x,y,z} : Set V) :=
    ⟨[x,y,z],by simp,List.chain'_cons.mpr ⟨xy,List.chain'_pair.mpr yz⟩,
      by simp [xy.ne,yz.ne,xz],fun _ => by simp⟩
  exact ⟨p,pD,q,qD,qp.symm,x,z,xp.symm,zq,⟨P,rfl,rfl⟩⟩

/-- An exactly-two-component cut with a clique shore of order at least three
and a three-vertex induced-path shore admits a Hamiltonian path. -/
theorem traceable_of_three_vertex_path_and_clique_shores
    (conn : ConnectivityAtLeast G 3) (cutSize : D.card = 3)
    (offA : ∀ x ∈ D, x ∉ A) (offB : ∀ x ∈ D, x ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (largeB : 3 ≤ Nat.card B) (disjoint : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D) (clique : B.Pairwise G.Adj)
    {x y z : V} (shape : A = {x,y,z})
    (xy : G.Adj x y) (yz : G.Adj y z) (xz : x ≠ z) (notXZ : ¬ G.Adj x z) :
    Traceable G := by
  obtain ⟨p,pD,q,qD,pq,route⟩ := three_vertex_path_shore_route conn boundA shape xy yz xz notXZ
  exact traceable_of_routable_and_clique_shores conn cutSize offA offB boundB largeB disjoint
    ⟨x,shape.symm ▸ (by simp : x ∈ ({x,y,z} : Set V))⟩ cover clique pD qD pq route

#print axioms clique_shore_route
#print axioms traceable_of_compatible_shore_routes
#print axioms traceable_of_routable_and_clique_shores
#print axioms three_vertex_path_shore_route
#print axioms traceable_of_three_vertex_path_and_clique_shores

end Graffiti199Depleted.Catalogue
