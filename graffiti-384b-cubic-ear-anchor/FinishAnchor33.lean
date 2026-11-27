import ParityAnchor33

namespace Graffiti384b.EarAnchorFinish
open Finset SimpleGraph EarAnchor OneEar EarExchange33 CliquePivot33
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Putting both ends of the ear edge back into a residual solution costs two
vertices. In particular, the reduced domination number is at least fourteen. -/
theorem core_lower {e a c : V} (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c) :
    gamma H≤gamma (H.induce (outside e a c : Set V))+2 := by
  classical
  let W := outside e a c
  change gamma H≤gamma (H.induce (W : Set V))+2
  obtain ⟨X,cov,sz⟩ := (gamma_induced_iff H (W:=W)).mp le_rfl
  let D := insert e (insert c X)
  have dom : TwoDominates H D := by
    intro v out
    by_cases va : v=a
    · subst v
      exact PinnedColor34.two H ec.ne ea.symm ac (mem_insert_self ..) (mem_insert_of_mem (mem_insert_self ..))
    have wm : v∈W := outside_mem.mpr ⟨fun h => out (h ▸ mem_insert_self ..),va,
      fun h => out (h ▸ mem_insert_of_mem (mem_insert_self ..))⟩
    have sub : X⊆D := (subset_insert c X).trans (subset_insert ..)
    exact (cov.2 v wm (fun m => out (sub m))).trans (Repair.nbr_mono H v sub)
  have bound : gamma H≤D.card := Nat.sInf_le ⟨_,dom,rfl⟩
  have one := card_insert_le c X
  have two : D.card≤(insert c X).card+1 := card_insert_le ..
  omega

/-- At a cubic root on the ear, ordinary unconstrained 2-domination of the
29-vertex induced graph decides whether a minimum core set can be exchanged. -/
theorem core_exchange {e a c : V} (de : H.degree e=2) (da : H.degree a=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c) (pos : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) (n : Fintype.card V=32) (g : gamma H=16)
    {C : Finset V} (cl : H.IsNClique 5 C) :
    let J := H.induce (outside e a c : Set V)
    (gamma J=14 ∨ gamma J=15) ∧ ((∃ D,Exchange H a D) ↔ gamma J=14) ∧
    ((¬∃ v∈outside e a c,H.degree v=3 ∧ trianglesAt H v=3 ∧ H.Adj c v) → ∃ D,Exchange H a D) := by
  classical
  let W := outside e a c
  let J := H.induce (W : Set V)
  change (gamma J=14 ∨ gamma J=15) ∧ ((∃ D,Exchange H a D) ↔ gamma J=14) ∧ _
  obtain ⟨_,_,_,_,ear,_,_,_⟩ := diamond H de da ea ec ac pos inj
  have lower : gamma H≤gamma J+2 := core_lower H ea ec ac
  have solved (h : ∃ D,Exchange H a D) : gamma J=14 := by
    obtain ⟨X,cov,_,sz⟩ := (exchange_iff_guarded H ear ea ec ac n g).mp h
    have up : gamma J≤14 := (gamma_induced_iff H).mpr ⟨X,cov,sz⟩
    omega
  have bad (h : ¬∃ D,Exchange H a D) :
      gamma J=15 ∧ ∃ v∈W,H.degree v=3 ∧ trianglesAt H v=3 ∧ H.Adj c v := by
    have tight : Tight H {a} := by
      apply Classical.byContradiction; intro no; exact h ((EarExchange33.exchange_iff H a (by omega)).mp no)
    obtain ⟨_,val,v,vm,d,score,edge,_⟩ := cubic_failure H de da ea ec ac pos inj n g tight cl
    exact ⟨val,v,vm,d,score,edge⟩
  by_cases ok : ∃ D,Exchange H a D
  · exact ⟨Or.inl (solved ok),⟨solved,fun _ => ok⟩,fun _ => ok⟩
  · obtain ⟨v15,cub⟩ := bad ok
    exact ⟨Or.inr v15,⟨solved,fun v14 => by omega⟩,fun miss => (miss cub).elim⟩

/-- A minimum full solution projects to a set no larger in the leaf-deleted
core by replacing the mandatory leaf by its neighbor. -/
theorem leaf_lower {z a : V} (leaf : H.neighborFinset z={a}) :
    gamma (H.induce ((({z} : Finset V)ᶜ : Finset V) : Set V))≤gamma H := by
  classical
  let W := ({z} : Finset V)ᶜ
  have za : H.Adj z a := (H.mem_neighborFinset _ _).mp (leaf ▸ mem_singleton_self _)
  have available : {s : ℕ | ∃ D,TwoDominates H D ∧ D.card=s}.Nonempty := ⟨_,univ,by simp [TwoDominates],rfl⟩
  obtain ⟨D,dom,sz⟩ := Nat.sInf_mem available
  change D.card=gamma H at sz
  have zm : z∈D := by
    apply Classical.byContradiction; intro out
    have lower := dom z out
    have inc : D.filter (H.Adj z)⊆H.neighborFinset z := fun u m => (H.mem_neighborFinset _ _).mpr (mem_filter.mp m).2
    have le := card_le_card inc
    rw [leaf,card_singleton] at le; change 2≤(D.filter (H.Adj z)).card at lower; omega
  let X := insert a (D.erase z)
  apply (gamma_induced_iff H (W:=W)).mpr
  refine ⟨X,⟨insert_subset (by simp [W,za.ne.symm]) (fun v m => by simpa [W] using (mem_erase.mp m).1),?_⟩,?_⟩
  · intro v vm out
    have ne : v≠z := by simpa [W] using vm
    have vd : v∉D := fun m => out (mem_insert_of_mem (mem_erase.mpr ⟨ne,m⟩))
    have vz : ¬H.Adj v z := by
      intro edge
      have h := (H.mem_neighborFinset _ _).mpr edge.symm
      rw [leaf,mem_singleton] at h
      exact out (h ▸ mem_insert_self ..)
    have sub : D.filter (H.Adj v)⊆X.filter (H.Adj v) := by
      intro u m; obtain ⟨ud,vu⟩ := mem_filter.mp m
      exact mem_filter.mpr ⟨mem_insert_of_mem (mem_erase.mpr ⟨fun eq => vz (eq ▸ vu),ud⟩),vu⟩
    exact (dom v vd).trans (card_le_card sub)
  · have up := card_insert_le a (D.erase z)
    rw [card_erase_of_mem zm] at up
    have dp := card_pos.mpr (show D.Nonempty from ⟨z,zm⟩)
    change (insert a (D.erase z)).card≤gamma H; omega

/-- Full-graph numerical identity under the normalized cubic-anchor
hypotheses. The two possible pairs are (16,14) and (17,15). -/
theorem full_value (n : Fintype.card V=33) (t : (types H).card=33) {z a : V}
    (leaf : H.neighborFinset z={a}) :
    let P := ({z} : Finset V)ᶜ
    let G := H.induce (P : Set V)
    ∀ r e c : P,r.val=a → G.degree e=2 → G.degree r=3 → G.Adj e r → G.Adj e c → G.Adj r c →
    (∀ v,0<trianglesAt G v) → Function.Injective (trianglesAt G) → gamma G=16 →
    (∃ C,G.IsNClique 5 C) →
    let J := G.induce (outside e r c : Set P)
    gamma H=gamma J+2 ∧ (gamma H≤bound H ↔ gamma J=14) := by
  let P := ({z} : Finset V)ᶜ
  let G := H.induce (P : Set V)
  change ∀ r e c : P,_
  intro r e c ra de dr er ec rc pos inj g five
  let J := G.induce (outside e r c : Set P)
  change gamma H=gamma J+2 ∧ (gamma H≤bound H ↔ gamma J=14)
  have order : Fintype.card P=32 := by rw [Fintype.card_coe]; simp [P,card_compl,n]
  obtain ⟨C,cl⟩ := five
  obtain ⟨pair,eq,_⟩ := core_exchange G de dr er ec rc pos inj order g cl
  have iffFull := (EarRoot33.attachment_iff H n t leaf r ra g).trans eq
  have hi := within_one H
  have lo : gamma G≤gamma H := leaf_lower H leaf
  change gamma G=16 at g
  have cap : bound H=16 := by unfold bound; rw [n,t]
  change (gamma H≤bound H ↔ gamma J=14) at iffFull
  change gamma J=14 ∨ gamma J=15 at pair
  refine ⟨?_,iffFull⟩
  rcases pair with h|h
  · have yes := iffFull.mpr h; omega
  · have no : ¬gamma H≤bound H := fun ok => by have := iffFull.mp ok; omega
    omega

/-- Every cubic-anchor failure has a second triangular ear in the reduced
graph. Every simple path between its neighbors avoiding the new ear is odd
and meets each clique of size at least three away from that ear at most once. -/
theorem failure_routes {e a c : V} (de : H.degree e=2) (da : H.degree a=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c) (pos : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) (n : Fintype.card V=32) (g : gamma H=16)
    (tight : Tight H {a}) {C : Finset V} (cl : H.IsNClique 5 C) :
    let W := outside e a c
    let J := H.induce (W : Set V)
    ∃ v p q : W,H.degree v.val=3 ∧ trianglesAt H v.val=3 ∧ H.Adj c v.val ∧
      J.degree v=2 ∧ J.neighborFinset v={p,q} ∧ J.Adj p q ∧
      (∀ x,x≠v → 3≤J.degree x) ∧ (opened J {v,p,q}).Reachable p q ∧
      (∃ l,2≤l ∧ Nonempty (Route J v p q l)) ∧ (∀ l,Route J v p q l → l%2=1) ∧
      ∀ l (r : Route J v p q l) (K : Finset W),J.IsClique (K : Set W) → 3≤K.card → v∉K →
        ∀ i j,i≤l → j≤l → r.atIdx i∈K → r.atIdx j∈K → i=j := by
  classical
  let W := outside e a c
  let J := H.induce (W : Set V)
  change ∃ v p q : W,_
  obtain ⟨sz,jval,u,um,d,score,cu,du,other,_⟩ := cubic_failure H de da ea ec ac pos inj n g tight cl
  let v : W := ⟨u,um⟩
  have d2 : J.degree v=2 := (induced_degree H v).trans du
  have cnt : (J.neighborFinset v).card=2 := (card_neighborFinset_eq_degree ..).trans d2
  obtain ⟨p,q,ne,ear⟩ := card_eq_two.mp cnt
  have vp : J.Adj v p := (J.mem_neighborFinset _ _).mp (ear ▸ mem_insert_self ..)
  have vq : J.Adj v q := (J.mem_neighborFinset _ _).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have pq : J.Adj p q := full_neighbors H d score vp vq (fun h => ne (Subtype.ext h))
  have minJ (x : W) (nx : x≠v) : 3≤J.degree x := by
    rw [show J.degree x=nbr H x.val W from induced_degree H x]
    exact other x.val x.property (fun eq => nx (Subtype.ext eq))
  obtain ⟨reach,route,odd,hits⟩ := AnchorParity.odd_routes J ((Fintype.card_coe W).trans sz)
    jval ear vp vq pq minJ
  exact ⟨v,p,q,d,score,cu,d2,ear,pq,minJ,reach,route,odd,hits⟩

end Graffiti384b.EarAnchorFinish
#print axioms Graffiti384b.EarAnchorFinish.core_lower
#print axioms Graffiti384b.EarAnchorFinish.core_exchange
#print axioms Graffiti384b.EarAnchorFinish.full_value
#print axioms Graffiti384b.EarAnchorFinish.failure_routes
