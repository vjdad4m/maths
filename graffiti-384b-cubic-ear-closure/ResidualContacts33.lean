import ResidualLongest33

namespace Graffiti384b.ResidualShore
open Finset SimpleGraph EarAnchor OneEar
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def region (W : Finset V) (x : W) : Finset V := by
  classical
  exact univ.filter (fun t => ∃ m : t∈W,(G.induce (W : Set V)).Reachable x ⟨t,m⟩)

omit [DecidableRel G.Adj] in
theorem region_mem {W : Finset V} (x : W) (t : V) :
    t∈region G W x ↔ ∃ m : t∈W,(G.induce (W : Set V)).Reachable x ⟨t,m⟩ := by
  classical
  simp [region]

theorem region_arm {v r b : V} {W : Finset V} (x : W) (vr : v≠r) (bv : b≠v) (br : b≠r)
    (vw : v∉W) (bw : b∉W) (rx : G.Adj r x.val)
    (closed : ∀ t∈W,∀ y,G.Adj t y → y∈W ∨ y=r ∨ y=b)
    (minimum : ∀ t∈W,3≤G.degree t) (odd : ∀ l,Route G v r b l → l%2=1) :
    ∃ P Q,Arm G r (insert r (region G W x)) P Q := by
  classical
  have inc {t : V} (h : t∈region G W x) : t∈W := ((region_mem G x t).mp h).choose
  apply shore_arm G (show v∉insert r (region G W x) from fun m =>
    (mem_insert.mp m).elim vr (fun h => vw (inc h))) (show b∉insert r (region G W x) from fun m =>
    (mem_insert.mp m).elim br (fun h => bw (inc h))) bv (mem_insert_self ..)
  · exact ⟨x.val,mem_insert_of_mem ((region_mem G x _).mpr ⟨x.property,Reachable.refl _⟩),rx⟩
  · intro t tm tr y ty
    obtain ⟨tw,reach⟩ := (region_mem G x t).mp ((mem_insert.mp tm).resolve_left tr)
    rcases closed t tw y ty with yw|yr|yb
    · have edge : (G.induce (W : Set V)).Adj (⟨t,tw⟩ : W) ⟨y,yw⟩ := ty
      exact Or.inl (mem_insert_of_mem ((region_mem G x y).mpr ⟨yw,reach.trans edge.reachable⟩))
    · exact Or.inl (yr ▸ mem_insert_self ..)
    · exact Or.inr yb
  · intro t tm tr
    exact minimum t (inc ((mem_insert.mp tm).resolve_left tr))
  · exact odd

/-- All contacts from the two endpoints belong to one component after
the three ear vertices are removed. Components without contacts are allowed. -/
theorem contacts_connected {v p q : V} (n29 : Fintype.card V=29) (g15 : gamma G=15)
    (ear : G.neighborFinset v={p,q}) (vp : G.Adj v p) (vq : G.Adj v q) (pq : G.Adj p q)
    (minimum : ∀ x,x≠v → 3≤G.degree x) :
    let W := outside v p q
    ∀ x y : W,G.Adj p x.val → G.Adj q y.val → (G.induce (W : Set V)).Reachable x y := by
  classical
  let W := outside v p q
  change ∀ x y : W,_
  intro x y px qy
  obtain ⟨_,_,odd,_⟩ := AnchorParity.odd_routes G n29 g15 ear vp vq pq minimum
  have vw : v∉W := fun m => (outside_mem.mp m).1 rfl
  have pw : p∉W := fun m => (outside_mem.mp m).2.1 rfl
  have qw : q∉W := fun m => (outside_mem.mp m).2.2 rfl
  have closed (t : V) (tw : t∈W) (u : V) (tu : G.Adj t u) : u∈W ∨ u=p ∨ u=q := by
    by_cases up : u=p
    · exact Or.inr (Or.inl up)
    by_cases uq : u=q
    · exact Or.inr (Or.inr uq)
    have uv : u≠v := by
      intro eq; subst u
      have h := (G.mem_neighborFinset _ _).mpr tu.symm
      rw [ear] at h
      rcases mem_insert.mp h with eq|m
      · exact (outside_mem.mp tw).2.1 eq
      · exact (outside_mem.mp tw).2.2 (mem_singleton.mp m)
    exact Or.inl (outside_mem.mpr ⟨uv,up,uq⟩)
  have low (t : V) (tw : t∈W) := minimum t (outside_mem.mp tw).1
  apply Classical.byContradiction
  intro apart
  obtain ⟨P,Q,hp⟩ := region_arm G x vp.ne vq.ne.symm pq.ne.symm vw qw px closed low odd
  obtain ⟨L,R,hq⟩ := region_arm G y vq.ne vp.ne.symm pq.ne vw pw qy
    (fun t tw u tu => by simpa only [or_comm (a:=u=p) (b:=u=q)] using closed t tw u tu)
    low (fun l s => odd l s.reverse)
  have inc {t : V} {z : W} (m : t∈region G W z) : t∈W := ((region_mem G z t).mp m).choose
  have dis : Disjoint (insert p (region G W x)) (insert q (region G W y)) := by
    apply disjoint_left.mpr; intro t sm tm
    rcases mem_insert.mp sm with rfl|s
    · exact (mem_insert.mp tm).elim pq.ne (fun h => pw (inc h))
    rcases mem_insert.mp tm with rfl|t'
    · exact qw (inc s)
    obtain ⟨m,reach⟩ := (region_mem G x t).mp s
    obtain ⟨_,other⟩ := (region_mem G y t).mp t'
    exact apart (reach.trans other.symm)
  obtain ⟨D,dom,sz⟩ := combine G vp vq pq.ne dis
    (fun m => (mem_insert.mp m).elim vp.ne (fun h => vw (inc h)))
    (fun m => (mem_insert.mp m).elim vq.ne (fun h => vw (inc h))) hp hq minimum
  have lb : gamma G≤D.card := Nat.sInf_le ⟨_,dom,rfl⟩
  omega

end Graffiti384b.ResidualShore
#print axioms Graffiti384b.ResidualShore.contacts_connected
