import OrderTen

open private six_le_treeNumber_of_five_independent_neighbors from CubicEdgeCuts
open private shore_anticomplete from CubicPortThreeShores
open private ThreeVertexShore.left_two ThreeVertexShore.right_two from TwoShortShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}
variable {A B : Set V} {D : Finset V}

/-- A singleton component whose full neighborhood is the three-cut. -/
def CutSingleton (G : SimpleGraph V) (D : Finset V) (r : V) : Prop :=
  r ∉ D ∧ ∀ v, G.Adj r v ↔ v ∈ D

def shoreContacts (G : SimpleGraph V) (A : Set V) (p : V) : Set V :=
  {v | v ∈ A ∧ G.Adj p v}

variable [Fintype V] [DecidableEq V]

/-- Independent contacts on two different sides and singleton components
all contribute to one potential induced star at the same port. -/
theorem card_independent_shore_contacts_le_four
    (budget : treeNumber G ≤ 5)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (apart : Disjoint A B)
    {p : V} (hp : p ∈ D) (U W R : Finset V)
    (hU : ∀ x ∈ U, x ∈ shoreContacts G A p)
    (hW : ∀ x ∈ W, x ∈ shoreContacts G B p)
    (iU : ∀ x ∈ U, ∀ y ∈ U, ¬ G.Adj x y)
    (iW : ∀ x ∈ W, ∀ y ∈ W, ¬ G.Adj x y)
    (hR : ∀ x ∈ R, CutSingleton G D x ∧ x ∉ A ∧ x ∉ B) :
    U.card + W.card + R.card ≤ 4 := by
  have awayUW : Disjoint U W := Finset.disjoint_left.mpr (by
    intro x xu xw
    exact Set.disjoint_left.mp apart (hU _ xu).1 (hW _ xw).1)
  have awayR : Disjoint (U ∪ W) R := Finset.disjoint_left.mpr (by
    intro x hx xr
    rcases Finset.mem_union.mp hx with xu|xw
    · exact (hR x xr).2.1 (hU _ xu).1
    · exact (hR x xr).2.2 (hW _ xw).1)
  let T := (U ∪ W) ∪ R
  have cardT : T.card = U.card + W.card + R.card := by
    change ((U ∪ W) ∪ R).card = _
    rw [Finset.card_union_of_disjoint awayR,Finset.card_union_of_disjoint awayUW]
  have contact (v : V) (hv : v ∈ T) : G.Adj p v := by
    simp only [T,Finset.mem_union] at hv
    rcases hv with (hu|hw)|hr
    · exact (hU _ hu).2
    · exact (hW _ hw).2
    · exact (((hR _ hr).1.2 p).mpr hp).symm
  have noUW {x y : V} (hx : x ∈ U) (hy : y ∈ W) : ¬ G.Adj x y :=
    shore_anticomplete offB boundA apart (hU _ hx).1 (hW _ hy).1
  have noRU {x y : V} (hx : x ∈ R) (hy : y ∈ U) : ¬ G.Adj x y :=
    fun e => offA _ (((hR _ hx).1.2 _).mp e) (hU _ hy).1
  have noRW {x y : V} (hx : x ∈ R) (hy : y ∈ W) : ¬ G.Adj x y :=
    fun e => offB _ (((hR _ hx).1.2 _).mp e) (hW _ hy).1
  have stable (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ T) : ¬ G.Adj x y := by
    simp only [T,Finset.mem_union] at hx hy
    rcases hx with (xu|xw)|xr <;> rcases hy with (yu|yw)|yr
    · exact iU _ xu _ yu
    · exact noUW xu yw
    · exact fun e => noRU yr xu e.symm
    · exact fun e => noUW yu xw e.symm
    · exact iW _ xw _ yw
    · exact fun e => noRW yr xw e.symm
    · exact noRU xr yu
    · exact noRW xr yw
    · exact fun e => (hR _ yr).1.1 (((hR _ xr).1.2 _).mp e)
  by_contra! large
  have six := six_le_treeNumber_of_five_independent_neighbors T p (by omega) contact stable
  omega

omit [Fintype V] in
private theorem independent_pair {x y : V} (no : ¬ G.Adj x y) :
    ∀ u ∈ ({x,y} : Finset V), ∀ v ∈ ({x,y} : Finset V), ¬ G.Adj u v := by
  simp only [Finset.mem_insert,Finset.mem_singleton]
  intro u hu v hv
  rcases hu with e|e <;> subst u <;> rcases hv with e|e <;> subst v
  · exact G.loopless _
  · exact no
  · exact fun h => no h.symm
  · exact G.loopless _

/-- One singleton component forbids a port from having nonadjacent
contacts in both large components. -/
theorem contact_clique_on_one_side_of_singleton
    (budget : treeNumber G ≤ 5)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (apart : Disjoint A B)
    {p r : V} (hp : p ∈ D) (hr : CutSingleton G D r) (rA : r ∉ A) (rB : r ∉ B) :
    (shoreContacts G A p).Pairwise G.Adj ∨ (shoreContacts G B p).Pairwise G.Adj := by
  classical
  by_cases hA : (shoreContacts G A p).Pairwise G.Adj
  · exact Or.inl hA
  right
  by_contra hB
  change ¬ (∀ x ∈ shoreContacts G A p, ∀ y ∈ shoreContacts G A p, x ≠ y → G.Adj x y) at hA
  change ¬ (∀ x ∈ shoreContacts G B p, ∀ y ∈ shoreContacts G B p, x ≠ y → G.Adj x y) at hB
  push_neg at hA hB
  obtain ⟨a,ha,a',ha',aa,na⟩ := hA
  obtain ⟨b,hb,b',hb',bb,nb⟩ := hB
  have small := card_independent_shore_contacts_le_four budget offA offB boundA apart hp
    {a,a'} {b,b'} {r}
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with e|e
      · exact e.symm ▸ ha
      · exact (Finset.mem_singleton.mp e).symm ▸ ha')
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with e|e
      · exact e.symm ▸ hb
      · exact (Finset.mem_singleton.mp e).symm ▸ hb')
    (independent_pair na) (independent_pair nb) (by
      intro x hx
      have e := Finset.mem_singleton.mp hx
      exact e.symm ▸ ⟨hr,rA,rB⟩)
  rw [Finset.card_pair aa,Finset.card_pair bb,Finset.card_singleton] at small
  omega

/-- Two singleton components and one contact on the opposite side force
the contacts through a given port to be a clique. -/
theorem contacts_are_clique_of_two_singletons
    (budget : treeNumber G ≤ 5)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (apart : Disjoint A B)
    {p b r s : V} (hp : p ∈ D) (hb : b ∈ shoreContacts G B p) (rs : r ≠ s)
    (hr : CutSingleton G D r) (hs : CutSingleton G D s)
    (rA : r ∉ A) (rB : r ∉ B) (sA : s ∉ A) (sB : s ∉ B) :
    (shoreContacts G A p).Pairwise G.Adj := by
  intro a ha c hc ac
  by_contra no
  have small := card_independent_shore_contacts_le_four budget offA offB boundA apart hp
    {a,c} {b} {r,s}
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with e|e
      · exact e.symm ▸ ha
      · exact (Finset.mem_singleton.mp e).symm ▸ hc)
    (by intro x hx; exact (Finset.mem_singleton.mp hx).symm ▸ hb)
    (independent_pair no) (by
      intro x hx y hy
      have e : x = y := (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm
      exact fun h => G.loopless x (e.symm ▸ h)) (by
      intro x hx
      rcases Finset.mem_insert.mp hx with e|e
      · exact e.symm ▸ ⟨hr,rA,rB⟩
      · exact (Finset.mem_singleton.mp e).symm ▸ ⟨hs,sA,sB⟩)
  rw [Finset.card_pair ac,Finset.card_singleton,Finset.card_pair rs] at small
  omega

/-- With two nonempty sides of a three-cut, there can be at most two
additional singleton components. -/
theorem card_cut_singletons_le_two (conn : ConnectivityAtLeast G 3)
    (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B) (apart : Disjoint A B)
    (aNon : A.Nonempty) (bNon : B.Nonempty) (R : Finset V)
    (hR : ∀ x ∈ R, CutSingleton G D x ∧ x ∉ A ∧ x ∉ B) : R.card ≤ 2 := by
  obtain ⟨p,hp⟩ : D.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha,pa⟩ := contact_of_shore conn (by omega) offA boundA aNon hp
  obtain ⟨b,hb,pb⟩ := contact_of_shore conn (by omega) offB boundB bNon hp
  have small := card_independent_shore_contacts_le_four budget offA offB boundA apart hp
    {a} {b} R
    (by intro x hx; exact (Finset.mem_singleton.mp hx).symm ▸ ⟨ha,pa⟩)
    (by intro x hx; exact (Finset.mem_singleton.mp hx).symm ▸ ⟨hb,pb⟩)
    (by intro x hx y hy; have e := (Finset.mem_singleton.mp hx).trans
          (Finset.mem_singleton.mp hy).symm; exact fun h => G.loopless x (e.symm ▸ h))
    (by intro x hx y hy; have e := (Finset.mem_singleton.mp hx).trans
          (Finset.mem_singleton.mp hy).symm; exact fun h => G.loopless x (e.symm ▸ h))
    hR
  simp only [Finset.card_singleton] at small
  omega

variable [DecidableRel G.Adj]

omit [Fintype V] in
theorem exists_common_port_of_two_contacts
    {x y : V} (size : D.card = 3)
    (lu : 2 ≤ (D.filter (G.Adj x)).card) (lw : 2 ≤ (D.filter (G.Adj y)).card) :
    ∃ p ∈ D, G.Adj p x ∧ G.Adj p y := by
  let U := D.filter (G.Adj x)
  let W := D.filter (G.Adj y)
  change 2 ≤ U.card at lu
  change 2 ≤ W.card at lw
  have uw : (U ∪ W).card ≤ 3 := by
    rw [← size]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset ..) (Finset.filter_subset ..))
  have pl := Finset.card_union_add_card_inter U W
  obtain ⟨p,hp⟩ : (U ∩ W).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨pu,pw⟩ := Finset.mem_inter.mp hp
  obtain ⟨pD,up⟩ := Finset.mem_filter.mp pu
  obtain ⟨_,wp⟩ := Finset.mem_filter.mp pw
  exact ⟨p,pD,up.symm,wp.symm⟩

/-- The two ends of a three-vertex path side give two leaves of an
induced claw centered in the cut. Its third leaf lies in the other side. -/
theorem induced_claw_at_cut_of_three_vertex_path
    (P : ThreeVertexShore G A)
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (bNon : B.Nonempty) :
    ∃ p ∈ D, ∃ z ∈ B, G.Adj p P.left ∧ G.Adj p P.right ∧ G.Adj p z ∧
      z ≠ P.left ∧ z ≠ P.right ∧ ¬ G.Adj P.left P.right ∧
      ¬ G.Adj P.left z ∧ ¬ G.Adj P.right z := by
  obtain ⟨p,pD,px,py⟩ := exists_common_port_of_two_contacts size
    (ThreeVertexShore.left_two P conn boundA) (ThreeVertexShore.right_two P conn boundA)
  obtain ⟨z,zB,pz⟩ := contact_of_shore conn (by omega) offB boundB bNon pD
  have zA := Set.disjoint_left.mp apart.symm zB
  exact ⟨p,pD,z,zB,px,py,pz,fun e => zA (e.symm ▸ P.left_mem),
    fun e => zA (e.symm ▸ P.right_mem),P.noLR,
    shore_anticomplete offB boundA apart P.left_mem zB,
    shore_anticomplete offB boundA apart P.right_mem zB⟩

/-- Two contacts each force a common port. With two singleton
components, this already forces adjacency inside the side. -/
theorem adjacent_of_two_port_contacts_and_two_singletons
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (bNon : B.Nonempty) {r s : V} (rs : r ≠ s)
    (hr : CutSingleton G D r) (hs : CutSingleton G D s)
    (rA : r ∉ A) (rB : r ∉ B) (sA : s ∉ A) (sB : s ∉ B)
    {x y : V} (xA : x ∈ A) (yA : y ∈ A) (xy : x ≠ y)
    (lu : 2 ≤ (D.filter (G.Adj x)).card) (lw : 2 ≤ (D.filter (G.Adj y)).card) : G.Adj x y := by
  obtain ⟨p,pD,px,py⟩ := exists_common_port_of_two_contacts size lu lw
  obtain ⟨b,bB,pb⟩ := contact_of_shore conn (by omega) offB boundB bNon pD
  have cl := contacts_are_clique_of_two_singletons budget offA offB boundA apart
    pD (show b ∈ shoreContacts G B p from ⟨bB,pb⟩) rs hr hs rA rB sA sB
  exact cl (show x ∈ shoreContacts G A p from ⟨xA,px⟩)
    (show y ∈ shoreContacts G A p from ⟨yA,py⟩) xy

/-- A three-vertex path side is incompatible with two singleton components. -/
theorem no_three_vertex_path_with_two_singleton_components (P : ThreeVertexShore G A)
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (bNon : B.Nonempty) {r s : V} (rs : r ≠ s)
    (hr : CutSingleton G D r) (hs : CutSingleton G D s)
    (rA : r ∉ A) (rB : r ∉ B) (sA : s ∉ A) (sB : s ∉ B) : False :=
  P.noLR (adjacent_of_two_port_contacts_and_two_singletons conn budget size offA offB
    boundA boundB apart bNon rs hr hs rA rB sA sB P.left_mem P.right_mem P.lr
    (ThreeVertexShore.left_two P conn boundA) (ThreeVertexShore.right_two P conn boundA))

#print axioms card_independent_shore_contacts_le_four
#print axioms contact_clique_on_one_side_of_singleton
#print axioms contacts_are_clique_of_two_singletons
#print axioms card_cut_singletons_le_two
#print axioms induced_claw_at_cut_of_three_vertex_path
#print axioms adjacent_of_two_port_contacts_and_two_singletons
#print axioms no_three_vertex_path_with_two_singleton_components

end Graffiti199Depleted.Catalogue
