import FinishAnchor33

namespace Graffiti384b.EarAnchorEdge
open Finset SimpleGraph EarAnchor OneEar CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The alternative odd path and its closing edge form a cycle in the core.
Each path edge has at most one possible common neighbor, the opposite ear
anchor. The closing edge has precisely that anchor and the new ear. -/
theorem thin_cycle {e a c : V} (de : H.degree e=2) (da : H.degree a=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c) (pos : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) (n : Fintype.card V=32) (g : gamma H=16)
    (tight : Tight H {a}) {C : Finset V} (cl : H.IsNClique 5 C) :
    let W := outside e a c
    let J := H.induce (W : Set V)
    ∃ v p q : W, ∃ l, ∃ r : Route J v p q l, 3≤l ∧ l%2=1 ∧ J.Adj p q ∧
      (∀ u,H.Adj p.val u ∧ H.Adj q.val u ↔ u=c ∨ u=v.val) ∧
      ∀ i,i<l → ∀ u,H.Adj (r.atIdx i).val u → H.Adj (r.atIdx (i+1)).val u → u=c := by
  classical
  let W := outside e a c
  let J := H.induce (W : Set V)
  change ∃ v p q : W, ∃ l, ∃ r : Route J v p q l, _
  obtain ⟨v,p,q,d,s,cv,_,ear,pq,_,_,⟨l,len,⟨r⟩⟩,odd,hit⟩ :=
    EarAnchorFinish.failure_routes H de da ea ec ac pos inj n g tight cl
  have parity := odd l r
  have vp : J.Adj v p := (J.mem_neighborFinset _ _).mp (ear ▸ mem_insert_self ..)
  have vq : J.Adj v q := (J.mem_neighborFinset _ _).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have cp : H.Adj c p.val := full_neighbors H d s cv.symm vp (outside_mem.mp p.property).2.2.symm
  have cq : H.Adj c q.val := full_neighbors H d s cv.symm vq (outside_mem.mp q.property).2.2.symm
  obtain ⟨w,_,_,_,ear0,root,_⟩ := diamond H de da ea ec ac pos inj
  have cover (i j : ℕ) (hi : i≤l) (hj : j≤l) (ne : i≠j)
      (edge : J.Adj (r.atIdx i) (r.atIdx j)) (u : V)
      (ux : H.Adj (r.atIdx i).val u) (uy : H.Adj (r.atIdx j).val u) : u=c ∨ u=v.val := by
    let x := r.atIdx i
    let y := r.atIdx j
    have xe := outside_mem.mp x.property
    have ye := outside_mem.mp y.property
    by_cases uc : u=c
    · exact Or.inl uc
    by_cases uv : u=v.val
    · exact Or.inr uv
    have ue : u≠e := by
      intro eq; subst u
      have m := (H.mem_neighborFinset _ _).mpr ux.symm
      change x.val∈H.neighborFinset e at m
      rw [ear0] at m; simp [xe.2.1,xe.2.2] at m
    have ua : u≠a := by
      intro eq; subst u
      have mx := (H.mem_neighborFinset _ _).mpr ux.symm
      have my := (H.mem_neighborFinset _ _).mpr uy.symm
      change x.val∈H.neighborFinset a at mx
      change y.val∈H.neighborFinset a at my
      rw [root] at mx my
      simp [xe.1,xe.2.2] at mx
      simp [ye.1,ye.2.2] at my
      exact edge.ne (Subtype.ext (mx.trans my.symm))
    let t : W := ⟨u,outside_mem.mpr ⟨ue,ua,uc⟩⟩
    let K : Finset W := {x,y,t}
    have xt : J.Adj x t := ux
    have yt : J.Adj y t := uy
    have xy : J.Adj x y := edge
    have complete : J.IsClique (K : Set W) := by
      intro i im j jm nd
      rcases (show i=x ∨ i=y ∨ i=t by simpa [K] using im) with rfl|rfl|rfl <;>
        rcases (show j=x ∨ j=y ∨ j=t by simpa [K] using jm) with rfl|rfl|rfl <;>
        first | exact (nd rfl).elim | exact xy | exact xy.symm | exact xt | exact xt.symm | exact yt | exact yt.symm
    have size : 3≤K.card := by simp [K,xy.ne,xt.ne,yt.ne]
    have miss : v∉K := by
      have vx := (r.avoid i hi).symm
      have vy := (r.avoid j hj).symm
      have vt : v≠t := fun h => uv (congrArg Subtype.val h.symm)
      simp [K,x,y,vx,vy,vt]
    exact (ne (hit l r K complete size miss i j hi hj (by simp [K,x]) (by simp [K,y]))).elim
  refine ⟨v,p,q,l,r,by omega,parity,pq,?_,?_⟩
  · intro u
    constructor
    · rintro ⟨pu,qu⟩
      apply cover 0 l (by omega) le_rfl (by omega) (by simpa [r.start,r.finish] using pq)
      · simpa [r.start] using pu
      · simpa [r.finish] using qu
    · rintro (rfl|rfl)
      · exact ⟨cp.symm,cq.symm⟩
      · exact ⟨vp.symm,vq.symm⟩
  · intro i hi u xu yu
    rcases cover i (i+1) (by omega) (by omega) (by omega) (r.step i hi) u xu yu with yes|h
    · exact yes
    subst u
    have endpoints (j : ℕ) (hj : j≤l) (z : J.Adj (r.atIdx j) v) : j=0 ∨ j=l := by
      have mem := (J.mem_neighborFinset _ _).mpr z.symm
      rw [ear] at mem
      rcases (show r.atIdx j=p ∨ r.atIdx j=q by simpa using mem) with h|h
      · exact Or.inl (r.unique j hj 0 (by omega) (h.trans r.start.symm))
      · exact Or.inr (r.unique j hj l le_rfl (h.trans r.finish.symm))
    have xend := endpoints i (by omega) xu
    have yend := endpoints (i+1) (by omega) yu
    omega

end Graffiti384b.EarAnchorEdge
#print axioms Graffiti384b.EarAnchorEdge.thin_cycle
