import PrivateComponents

open private shore_anticomplete from CubicPortThreeShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {D : Finset V} {X Y : Set V} {r : V}

/-- No four-vertex induced tree rooted at the port and supported otherwise
on the indicated side. -/
def NoRootedFour (G : SimpleGraph V) (X : Set V) (r : V) : Prop :=
  ∀ f : Fin 4 ↪ V, f 0 = r → (∀ i, i ≠ 0 → f i ∈ X) → ¬ RootOrdering G f

theorem no_rooted_four_across_cut [Fintype V]
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (cut : D.card = 3)
    (offY : ∀ v ∈ D, v ∉ Y) (boundX : ShoreBoundary G D X) (boundY : ShoreBoundary G D Y)
    (apart : Disjoint X Y) (connY : (G.induce Y).Connected)
    (rD : r ∈ D) (missing : ∃ y ∈ Y, ¬ G.Adj r y) : NoRootedFour G X r := by
  intro f eq0 onX root
  have nonempty : Y.Nonempty := by obtain ⟨y,hy,_⟩ := missing; exact ⟨y,hy⟩
  obtain ⟨y,hy,z,hz,ry,yz,rz⟩ := two_step_into_shore connY.preconnected
    (contact_of_shore conn cut.le offY boundY nonempty rD) missing
  have different {u : V} (hu : u ∈ Y) (i : Fin 4) : u ≠ f i := by
    intro eq
    by_cases h : i = 0
    · subst i
      exact offY r rD ((eq.trans eq0) ▸ hu)
    · exact Set.disjoint_left.mp apart (onX i h) (eq ▸ hu)
  have anti {u : V} (hu : u ∈ Y) (i : Fin 4) (hi : i ≠ 0) : ¬ G.Adj (f i) u :=
    shore_anticomplete offY boundX apart (onX i hi) hu
  have noTail (i : Fin 4) : ¬ G.Adj (f i) z := by
    by_cases h : i = 0
    · subst i
      rwa [eq0]
    · exact anti hz i h
  have six := six_le_treeNumber_of_rooted_four_and_tail f root yz (eq0.symm ▸ ry)
    (different hy) (different hz) noTail (anti hy)
  omega

private theorem NoRootedFour.forbids_four (none : NoRootedFour G X r)
    {p u v : V} (pX : p ∈ X) (uX : u ∈ X) (vX : v ∈ X)
    (nd : [r,p,u,v].Nodup) (rp : G.Adj r p)
    (u1 : (G.Adj u r ∧ ¬ G.Adj u p) ∨ (G.Adj u p ∧ ¬ G.Adj u r))
    (v1 : (G.Adj v r ∧ ¬ G.Adj v p ∧ ¬ G.Adj v u) ∨
      (G.Adj v p ∧ ¬ G.Adj v r ∧ ¬ G.Adj v u) ∨
      (G.Adj v u ∧ ¬ G.Adj v r ∧ ¬ G.Adj v p)) : False := by
  obtain ⟨f,h0,h1,h2,h3,root⟩ := four_ordering nd rp u1 v1
  apply none f h0 _ root
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · change f (1 : Fin 4) ∈ X
    exact h1.symm ▸ pX
  · change f (2 : Fin 4) ∈ X
    exact h2.symm ▸ uX
  · change f (3 : Fin 4) ∈ X
    exact h3.symm ▸ vX

private theorem contact_list_nodup (rOff : r ∉ X) {p u v : V}
    (pX : p ∈ X) (uX : u ∈ X) (vX : v ∈ X) (rp : G.Adj r p)
    (ru : ¬ G.Adj r u) (rv : ¬ G.Adj r v) (uv : u ≠ v) :
    [r,p,u,v].Nodup := by
  have ruNe : r ≠ u := fun e => rOff (e.symm ▸ uX)
  have rvNe : r ≠ v := fun e => rOff (e.symm ▸ vX)
  have pu : p ≠ u := fun e => ru (e ▸ rp)
  have pv : p ≠ v := fun e => rv (e ▸ rp)
  simp [show r ≠ p from fun e => rOff (e.symm ▸ pX),ruNe,rvNe,pu,pv,uv]

theorem NoRootedFour.contact_propagates (none : NoRootedFour G X r) (rOff : r ∉ X)
    {p u v : V} (pX : p ∈ X) (uX : u ∈ Noncontacts G X r)
    (vX : v ∈ Noncontacts G X r) (rp : G.Adj r p) (uv : G.Adj u v)
    (pu : G.Adj p u) : G.Adj p v := by
  apply Classical.byContradiction
  intro npv
  exact none.forbids_four pX uX.1 vX.1
    (contact_list_nodup rOff pX uX.1 vX.1 rp uX.2 vX.2 uv.ne) rp
    (Or.inr ⟨pu.symm,fun e => uX.2 e.symm⟩)
    (Or.inr (Or.inr ⟨uv.symm,fun e => vX.2 e.symm,fun e => npv e.symm⟩))

theorem NoRootedFour.two_contacts_adjacent (none : NoRootedFour G X r) (rOff : r ∉ X)
    {p u v : V} (pX : p ∈ X) (uX : u ∈ Noncontacts G X r)
    (vX : v ∈ Noncontacts G X r) (rp : G.Adj r p)
    (uv : u ≠ v) (pu : G.Adj p u) (pv : G.Adj p v) : G.Adj u v := by
  apply Classical.byContradiction
  intro n
  exact none.forbids_four pX uX.1 vX.1
    (contact_list_nodup rOff pX uX.1 vX.1 rp uX.2 vX.2 uv) rp
    (Or.inr ⟨pu.symm,fun e => uX.2 e.symm⟩)
    (Or.inr (Or.inl ⟨pv.symm,fun e => vX.2 e.symm,fun e => n e.symm⟩))

theorem NoRootedFour.cross_contacts_complete (none : NoRootedFour G X r)
    (rOff : r ∉ X) {p q u : V} (pX : p ∈ X) (qX : q ∈ X)
    (uX : u ∈ Noncontacts G X r) (rp : G.Adj r p) (rq : G.Adj r q)
    (pu : G.Adj p u) (qu : ¬ G.Adj q u) : G.Adj p q := by
  apply Classical.byContradiction
  intro pq
  have rpNe := rp.ne
  have rqNe := rq.ne
  have ruNe : r ≠ u := fun e => rOff (e.symm ▸ uX.1)
  have puNe := pu.ne
  have pqNe : p ≠ q := fun e => qu (e ▸ pu)
  have uqNe : u ≠ q := fun e => uX.2 (e.symm ▸ rq)
  have nd : [r,p,u,q].Nodup := by simp [rpNe,rqNe,ruNe,puNe,pqNe,uqNe]
  exact none.forbids_four pX uX.1 qX nd rp (Or.inr ⟨pu.symm,fun e => uX.2 e.symm⟩)
    (Or.inl ⟨rq.symm,fun e => pq e.symm,qu⟩)

theorem NoRootedFour.contact_common_on_component (none : NoRootedFour G X r) (rOff : r ∉ X)
    (c : (G.induce (Noncontacts G X r)).ConnectedComponent)
    {p u v : V} (pX : p ∈ X) (rp : G.Adj r p)
    (uC : u ∈ noncontactComponent G X r c) (vC : v ∈ noncontactComponent G X r c)
    (pu : G.Adj p u) : G.Adj p v := by
  apply Classical.byContradiction
  intro npv
  obtain ⟨u,hu,rfl⟩ := uC
  obtain ⟨v,hv,rfl⟩ := vC
  obtain ⟨w⟩ := c.connected_induce_supp.preconnected ⟨u,hu⟩ ⟨v,hv⟩
  obtain ⟨s,yes,t,no,edge⟩ := crossingOnWalk (U := {x : c.supp | G.Adj p x.val.val}) w pu npv
  exact no (none.contact_propagates rOff pX s.val.property t.val.property rp edge yes)

/-- A component with a contact in the neighborhood of the port is a clique.
All of its vertices share that contact. -/
theorem NoRootedFour.clique_of_contact (none : NoRootedFour G X r) (rOff : r ∉ X)
    (c : (G.induce (Noncontacts G X r)).ConnectedComponent)
    {p u : V} (pX : p ∈ X) (rp : G.Adj r p)
    (uC : u ∈ noncontactComponent G X r c) (pu : G.Adj p u) :
    (noncontactComponent G X r c).Pairwise G.Adj := by
  intro x xC y yC xy
  have px := none.contact_common_on_component rOff c pX rp uC xC pu
  have py := none.contact_common_on_component rOff c pX rp uC yC pu
  obtain ⟨x,_,rfl⟩ := xC
  obtain ⟨y,_,rfl⟩ := yC
  exact none.two_contacts_adjacent rOff pX x.property y.property rp xy px py

def rootedBlockContacts (G : SimpleGraph V) (X : Set V) (r : V)
    (c : (G.induce (Noncontacts G X r)).ConnectedComponent) : Set V :=
  {p | p ∈ X ∧ G.Adj r p ∧ ∃ u ∈ noncontactComponent G X r c, G.Adj p u}

/-- Every noncontact block meets at least one neighbor of the port, as
long as the shore is connected and the port has some contact. -/
theorem rootedBlockContacts_nonempty
    (connX : (G.induce X).Connected) (some : (shoreContacts G X r).Nonempty)
    (c : (G.induce (Noncontacts G X r)).ConnectedComponent) :
    (rootedBlockContacts G X r c).Nonempty := by
  obtain ⟨p,pX,rp⟩ := some
  obtain ⟨u,hu⟩ := c.nonempty_supp
  obtain ⟨w⟩ := connX.preconnected ⟨u.val,u.property.1⟩ ⟨p,pX⟩
  have pOutside : p ∉ noncontactComponent G X r c := fun h => by
    obtain ⟨v,_,eq⟩ := h
    exact v.property.2 (eq.symm ▸ rp)
  obtain ⟨v,hv,z,hz,vz⟩ := crossingOnWalk
    (U := {x : X | x.val ∈ noncontactComponent G X r c}) w ⟨u,hu,rfl⟩ pOutside
  have edge : G.Adj v.val z.val := vz
  by_cases rz : G.Adj r z.val
  · exact ⟨z.val,z.property,rz,v.val,hv,edge.symm⟩
  obtain ⟨v',hv',eq⟩ := hv
  let z' : Noncontacts G X r := ⟨z.val,z.property,rz⟩
  have step : (G.induce (Noncontacts G X r)).Adj v' z' := by
    change G.Adj v'.val z.val
    rw [eq]
    exact edge
  exact (hz ⟨z',(c.mem_supp_congr_adj step).mp hv',rfl⟩).elim

/-- Contact sets of distinct noncontact blocks are disjoint. -/
theorem NoRootedFour.blockContacts_disjoint
    (none : NoRootedFour G X r) (rOff : r ∉ X)
    {c d : (G.induce (Noncontacts G X r)).ConnectedComponent} (ne : c ≠ d) :
    Disjoint (rootedBlockContacts G X r c) (rootedBlockContacts G X r d) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨pX,rp,u,⟨u',uc,rfl⟩,pu⟩ ⟨_,_,v,⟨v',vd,rfl⟩,pv⟩
  have diff : u'.val ≠ v'.val := fun eq =>
    ne (ConnectedComponent.eq_of_common_vertex uc ((Subtype.ext eq.symm : v' = u') ▸ vd))
  have uv : (G.induce (Noncontacts G X r)).Adj u' v' :=
    none.two_contacts_adjacent rOff pX u'.property v'.property rp diff pu pv
  exact ne (ConnectedComponent.eq_of_common_vertex ((c.mem_supp_congr_adj uv).mp uc) vd)

theorem NoRootedFour.all_noncontact_blocks_cliques
    (none : NoRootedFour G X r) (rOff : r ∉ X)
    (connX : (G.induce X).Connected) (some : (shoreContacts G X r).Nonempty)
    (c : (G.induce (Noncontacts G X r)).ConnectedComponent) :
    (noncontactComponent G X r c).Pairwise G.Adj := by
  obtain ⟨p,pX,rp,u,uc,pu⟩ := rootedBlockContacts_nonempty connX some c
  exact none.clique_of_contact rOff c pX rp uc pu

/-- The neighbor set on the first shore has independence number at most
two, in the form of a bound on every independent finite subset. -/
theorem NoRootedFour.card_independent_contacts_le_two (none : NoRootedFour G X r)
    (U : Finset V) (within : ∀ u ∈ U, u ∈ shoreContacts G X r)
    (ind : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v) : U.card ≤ 2 := by
  classical
  apply Classical.byContradiction
  intro notSmall
  obtain ⟨T,sub,card⟩ := Finset.exists_subset_card_eq (show 3 ≤ U.card by omega)
  let e : Fin 3 ≃ ↥T := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe,card])).symm
  let v (i : Fin 3) : V := (e i).val
  have mem (i : Fin 3) : v i ∈ U := sub (e i).property
  have rn (i : Fin 3) : r ≠ v i := (within _ (mem i)).2.ne
  have dn (i j : Fin 3) (h : i ≠ j) : v i ≠ v j :=
    fun eq => h (e.injective (Subtype.ext eq))
  have nd : [r,v 0,v 1,v 2].Nodup := by
    simp [rn,dn (0 : Fin 3) 1 (by decide),dn (0 : Fin 3) 2 (by decide),
      dn (1 : Fin 3) 2 (by decide)]
  have adj (i : Fin 3) : G.Adj r (v i) := (within _ (mem i)).2
  have no (i j : Fin 3) : ¬ G.Adj (v i) (v j) := ind _ (mem i) _ (mem j)
  exact none.forbids_four (within _ (mem 0)).1 (within _ (mem 1)).1 (within _ (mem 2)).1
    nd (adj 0) (Or.inl ⟨(adj 1).symm,no 1 0⟩)
    (Or.inl ⟨(adj 2).symm,no 2 0,no 2 1⟩)

#print axioms no_rooted_four_across_cut
#print axioms NoRootedFour.contact_common_on_component
#print axioms NoRootedFour.clique_of_contact
#print axioms NoRootedFour.cross_contacts_complete
#print axioms rootedBlockContacts_nonempty
#print axioms NoRootedFour.blockContacts_disjoint
#print axioms NoRootedFour.all_noncontact_blocks_cliques
#print axioms NoRootedFour.card_independent_contacts_le_two

end Graffiti199Depleted.Catalogue
