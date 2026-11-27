import MixedCutReduction

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/-- A deletion of at most three vertices containing a cubic vertex leaves
every surviving vertex in one component, including vertices not specified by an edge. -/
theorem deletion_preconnected_with_cubic
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    {D : Finset V} (small : D.card ≤ 3) {r : V} (hr : r ∈ D) (rdeg : G.degree r = 3) :
    (DeletionGraph G D).Preconnected := by
  classical
  have neighbor (a : Survives D) : ∃ b : Survives D, G.Adj a.val b.val := by
    by_contra! none
    have sub : G.neighborFinset a.val ⊆ D := by
      intro v hv
      by_contra out
      exact none ⟨v,out⟩ ((G.mem_neighborFinset _ _).mp hv)
    have lo := degree_of_small_deletion_preconnected (G := G) (by omega : 4 ≤ Fintype.card V)
      (fun K hK => (conn.2 K hK).preconnected) a.val
    have hi := Finset.card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at hi
    have adeg : G.degree a.val = 3 := by omega
    have eq := Finset.eq_of_subset_of_card_le sub (by rw [G.card_neighborFinset_eq_degree]; omega)
    have hN : r ∈ G.neighborFinset a.val := by rw [eq]; exact hr
    exact ind a.val r adeg rdeg ((G.mem_neighborFinset _ _).mp hN)
  intro a c
  obtain ⟨b,ab⟩ := neighbor a
  obtain ⟨d,cd⟩ := neighbor c
  exact edge_reach_of_cut_with_cubic smaller conn budget order no ind small hr rdeg ab cd

private theorem order_after_delete (r : V) :
    Fintype.card {x : V // x ≠ r} = Fintype.card V - 1 := by
  classical
  rw [Fintype.card_subtype_compl (fun x => x = r)]
  simp

/-- In the independent-cubic minimum-order branch, deleting a cubic
vertex preserves three-connectivity without adding any edges. -/
theorem connectivity_after_cubic_delete {r : V}
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    (rdeg : G.degree r = 3) :
    ConnectivityAtLeast (G.induce {x | x ≠ r}) 3 := by
  classical
  let S : Set V := {x | x ≠ r}
  let H := G.induce S
  have sz : Fintype.card S = Fintype.card V - 1 := order_after_delete r
  refine ⟨(by change 3 < Fintype.card S; omega),?_⟩
  intro D small
  let emb : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let R := insert r (D.map emb)
  have upper := Finset.card_insert_le r (D.map emb)
  rw [Finset.card_map] at upper
  have rsize : R.card ≤ 3 := by change (insert r (D.map emb)).card ≤ 3; omega
  let X := Survives R
  have keep (a : X) : a.val ≠ r := fun eq => a.property (by simp [R,eq])
  have connected := deletion_preconnected_with_cubic smaller conn budget order no ind rsize
    (Finset.mem_insert_self r (D.map emb)) rdeg
  let T : Set S := {x | x ∉ D}
  let forward : X → T :=
    fun a => ⟨⟨a.val,keep a⟩,fun mem => a.property (Finset.mem_insert_of_mem
      (Finset.mem_map.mpr ⟨⟨a.val,keep a⟩,mem,rfl⟩))⟩
  let back : T → X := fun a =>
    ⟨a.val.val,by
      intro mem
      rcases Finset.mem_insert.mp mem with eq|hm
      · exact a.val.property eq
      · obtain ⟨b,hb,eq⟩ := Finset.mem_map.mp hm
        exact a.property ((show b = a.val from Subtype.ext eq) ▸ hb)⟩
  have right (a : T) : forward (back a) = a := Subtype.ext (Subtype.ext rfl)
  let f : DeletionGraph G R →g H.induce T := ⟨forward,fun e => e⟩
  have reach : (H.induce T).Preconnected := by
    intro a b
    have h := (connected (back a) (back b)).map f
    change (H.induce T).Reachable (forward (back a)) (forward (back b)) at h
    simpa only [right] using h
  have proper : D.card < (Finset.univ : Finset S).card := by rw [Finset.card_univ]; omega
  obtain ⟨a,_,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card proper
  exact @SimpleGraph.Connected.mk _ (H.induce T) reach ⟨⟨a,off⟩⟩

omit [DecidableRel G.Adj] in
private theorem treeNumber_after_delete_le (r : V) :
    treeNumber (G.induce {x | x ≠ r}) ≤ treeNumber G := by
  classical
  let S : Set V := {x | x ≠ r}
  change treeNumber (G.induce S) ≤ _
  unfold treeNumber
  apply Finset.sup_le
  intro C hC
  have htree := (Finset.mem_filter.mp hC).2
  let f : (↑C : Set S) ↪ V := (Function.Embedding.subtype _).trans (Function.Embedding.subtype _)
  simpa using card_le_treeNumber_of_induced_copy f (fun _ _ => Iff.rfl) htree

/-- Every cubic vertex in the independent-cubic minimum-order branch can
be omitted from a Hamiltonian path in the actual induced deletion. -/
theorem traceable_after_cubic_delete {r : V}
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    (rdeg : G.degree r = 3) :
    Traceable (G.induce {x | x ≠ r}) := by
  classical
  have sz := order_after_delete r
  exact smaller {x : V // x ≠ r} (G.induce {x | x ≠ r}) (by omega)
    (connectivity_after_cubic_delete smaller conn budget order no ind rdeg)
    ((treeNumber_after_delete_le (G := G) r).trans budget)

/-- If a cubic vertex is deleted in addition to a three-cut, each of
the remaining components is adjacent to every cut vertex. -/
theorem all_ports_contact_components_after_cubic_delete
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ a b, G.degree a = 3 → G.degree b = 3 → ¬ G.Adj a b)
    {r : V} (rdeg : G.degree r = 3) {D : Finset V} (cutSize : D.card = 3)
    (rOff : r ∉ D) (C : (DeletionGraph G (insert r D)).ConnectedComponent)
    {p : V} (pD : p ∈ D) : ∃ x ∈ componentShore (insert r D) C, G.Adj p x := by
  classical
  let R := insert r (D.erase p)
  have size : R.card ≤ 3 := by
    have le := Finset.card_insert_le r (D.erase p)
    rw [Finset.card_erase_of_mem pD,cutSize] at le
    exact le
  have connR := deletion_preconnected_with_cubic smaller conn budget order no ind
    size (Finset.mem_insert_self r (D.erase p)) rdeg
  let A := componentShore (insert r D) C
  have outside := componentShore_off_cut (insert r D) C
  have boundary := componentShore_boundary (insert r D) C
  obtain ⟨a⟩ := (componentShore_connected (insert r D) C).nonempty
  have keepA : a.val ∉ R := by
    intro h
    apply outside a.val _ a.property
    rcases Finset.mem_insert.mp h with eq|hp
    · exact Finset.mem_insert.mpr (Or.inl eq)
    · exact Finset.mem_insert_of_mem (Finset.mem_of_mem_erase hp)
  have keepP : p ∉ R := by
    intro hp
    rcases Finset.mem_insert.mp hp with eq|hp
    · exact rOff (eq ▸ pD)
    · exact (Finset.not_mem_erase _ _) hp
  obtain ⟨w⟩ := connR ⟨a.val,keepA⟩ ⟨p,keepP⟩
  obtain ⟨x,xA,y,yA,xy⟩ := crossingOnWalk
    (U := {v : Survives R | v.val ∈ A}) w a.property
    (outside p (Finset.mem_insert_of_mem pD))
  have yIn : y.val ∈ insert r D := boundary x.val xA y.val yA xy
  have yp : y.val = p := by
    rcases Finset.mem_insert.mp yIn with eq|mem
    · exact (y.property (Finset.mem_insert.mpr (Or.inl eq))).elim
    · by_contra ne
      exact y.property (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨ne,mem⟩))
  have adj : G.Adj y.val x.val := G.symm xy
  exact ⟨x.val,xA,yp ▸ adj⟩

#print axioms deletion_preconnected_with_cubic
#print axioms connectivity_after_cubic_delete
#print axioms traceable_after_cubic_delete
#print axioms all_ports_contact_components_after_cubic_delete

end Graffiti199Depleted.Catalogue
