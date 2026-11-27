import AffineHost
import FourRingCycleArc

open SimpleGraph KelmansCactus.NearPerfectReplica.Layout
namespace KelmansCactus.AtomicBridge.AffineHost
open AffineBase FourRingBudget FourRingReplica FourRingReplica.Layout FourRingCycleArc
noncomputable section
variable {U : Type*} {A : SimpleGraph U} {r : Bool→U}
variable (L : Layout A r)

private def tag : V r→Option Point
  | .inl z => some z.1
  | .inr _ => none

private def project : V r→U
  | .inl z => z.2.val
  | .inr _ => r false

private theorem tag_is_cell {v : V r} {i : Point} (h : tag v=some i) :
    ∃ x : Piece r,v=cell i x := by
  cases v with
  | inl z =>
    exact ⟨z.2,congrArg Sum.inl (Prod.ext (Option.some.inj h) rfl)⟩
  | inr l => cases h

private theorem project_eq_in_cell {x y : V r} {i : Point}
    (xt : tag x=some i) (yt : tag y=some i) (eq : project x=project y) : x=y := by
  obtain ⟨u,rfl⟩ := tag_is_cell xt
  obtain ⟨v,rfl⟩ := tag_is_cell yt
  exact congrArg (cell i) (Subtype.ext eq)

private theorem internal_projects {x y : V r} (adj : (graph L).Adj x y)
    {i : Point} (xt : tag x=some i) (yt : tag y=some i) : A.Adj (project x) (project y) := by
  obtain ⟨w,rfl⟩ := tag_is_cell xt
  obtain ⟨z,rfl⟩ := tag_is_cell yt
  exact adj.2

private theorem no_cell_in_cell_out {x y : V r} (adj : (graph L).Adj x y)
    {i : Point} (xt : tag x=some i) (yt : tag y≠some i) :
    ∃ l : Line,y=control l := by
  obtain ⟨w,rfl⟩ := tag_is_cell xt
  cases y with
  | inl y =>
    rcases y with ⟨j,z⟩
    exact (yt (congrArg some adj.1.symm)).elim
  | inr l => exact ⟨l,rfl⟩

private theorem control_adjacency_project {x : V r} {l : Line}
    (adj : (graph L).Adj x (control l)) : ∃ b,A.Adj (r b) (project x) := by
  cases x with
  | inl z =>
    obtain ⟨s,p,_⟩ := adj
    refine ⟨s.1,?_⟩
    change A.Adj (r s.1) z.2.val
    rw [←p]
    exact L.conn s
  | inr q => exact adj.elim

private theorem control_adj_cell {x : V r} {l : Line}
    (adj : (graph L).Adj x (control l)) : ∃ i,tag x=some i := by
  cases x with
  | inl z => exact ⟨z.1,rfl⟩
  | inr q => exact adj.elim

private theorem single_control_for_cell_vertex {x : V r} {l q : Line}
    (a : (graph L).Adj x (control l)) (b : (graph L).Adj x (control q)) :
    l=q := by
  cases x with
  | inl z =>
    obtain ⟨i,x⟩ := z
    obtain ⟨s,sx,sl⟩ := a
    obtain ⟨t,tx,tq⟩ := b
    have st := L.port.injective (sx.trans tx.symm)
    exact sl.symm.trans ((congrArg (route i) st).trans tq)
  | inr k => exact a.elim

private theorem single_cell_vertex_for_control {x y : V r} {l : Line} {i : Point}
    (a : (graph L).Adj x (control l)) (b : (graph L).Adj y (control l))
    (xt : tag x=some i) (yt : tag y=some i) : x=y := by
  obtain ⟨x,rfl⟩ := tag_is_cell xt
  obtain ⟨y,rfl⟩ := tag_is_cell yt
  obtain ⟨s,sx,sl⟩ := a
  obtain ⟨t,tx,tl⟩ := b
  have st := route_injective i (sl.trans tl.symm)
  exact congrArg (cell i) (sx.symm.trans ((congrArg L.port st).trans tx))

private def atNat {W : Type*} {n : ℕ} [NeZero n] (f : Fin n→W) (j : ℕ) : W := f j

private theorem adjNat {W : Type*} {G : SimpleGraph W} {n : ℕ} [NeZero n]
    {f : Fin n→W} (h : CycleList G n f) (j : ℕ) : G.Adj (atNat f j) (atNat f (j+1)) := by
  have step : ((j+1 : ℕ) : Fin n) = (j : Fin n)+1 := by
    apply Fin.ext
    exact Nat.add_mod j 1 n
  change G.Adj (f j) (f (↑(j+1)))
  rw [step]
  exact h.2 _

private theorem wrap {W : Type*} {n : ℕ} [NeZero n] (f : Fin n→W) :
    atNat f n=atNat f 0 := by
  unfold atNat
  congr 1
  apply Fin.ext
  change n%n=0%n
  simp

private theorem atNat_inj {W : Type*} {n : ℕ} [NeZero n] {f : Fin n→W}
    (hi : Function.Injective f) {j k : ℕ} (jn : j<n) (kn : k<n)
    (same : atNat f j=atNat f k) : j=k := by
  have q := congrArg Fin.val (hi same)
  change j%n=k%n at q
  rwa [Nat.mod_eq_of_lt jn,Nat.mod_eq_of_lt kn] at q

private theorem from_control {n : ℕ} [NeZero n] (n3 : 3≤n) {f : Fin n→V r}
    (cy : CycleList (graph L) n f) (l : Line) (f0 : f 0=control l) :
    ∃ k,∃ hn : NeZero k,3≤k ∧ k≤n ∧ @HasShortCycle U A k hn := by
  classical
  let F := atNat f
  have step (j : ℕ) : (graph L).Adj (F j) (F (j+1)) := adjNat cy j
  have start : F 0=control l := f0
  have entry : (graph L).Adj (F 1) (control l) := by rw [←start]; exact (step 0).symm
  obtain ⟨i,tag1⟩ := control_adj_cell L entry
  let Q : ℕ→Prop := fun j=>2≤j ∧ tag (F j)≠some i
  have endQ : Q n := by
    refine ⟨by omega,?_⟩
    change tag (atNat f n)≠some i
    rw [wrap]
    change tag (F 0)≠some i
    rw [start]
    intro bad
    cases bad
  have existsQ : ∃j,Q j := ⟨n,endQ⟩
  let m := Nat.find existsQ
  have hm : 2≤m ∧ tag (F m)≠some i := Nat.find_spec existsQ
  have mn : m≤n := Nat.find_min' existsQ endQ
  have body {j : ℕ} (lo : 1≤j) (hi : j<m) : tag (F j)=some i := by
    by_cases en : j=1
    · rwa [en]
    · exact Classical.not_not.mp (fun no=>Nat.find_min existsQ hi ⟨by omega,no⟩)
  have last : tag (F (m-1))=some i := body (by omega) (by omega)
  have ex : (graph L).Adj (F (m-1)) (F m) := by
    simpa only [show m-1+1=m by omega] using step (m-1)
  obtain ⟨q,eq⟩ := no_cell_in_cell_out L ex last hm.2
  have m3 : 3≤m := by
    refine Classical.byContradiction ?_
    intro few
    have lower := hm.1
    have m2 : m=2 := by omega
    have tr : (graph L).Adj (F 1) (control q) := by
      rw [eq] at ex
      simpa only [m2,Nat.reduceSub] using ex
    have lq := single_control_for_cell_vertex L entry tr
    have e : F 0=F 2 := by rw [start,←m2,eq,lq]
    have no : (0:ℕ)=2 := atNat_inj cy.1 (by omega) (by omega) e
    omega
  have short : m<n := by
    refine Classical.byContradiction ?_
    intro h
    have same : m=n := by omega
    have e : F m=control l := by
      change atNat f m=control l
      rw [same,wrap]
      exact start
    have ext : (graph L).Adj (F (m-1)) (control l) := by rw [←e]; exact ex
    have together := single_cell_vertex_for_control L entry ext tag1 last
    have ne : (1:ℕ)=m-1 := atNat_inj cy.1 (by omega) (by omega) together
    omega
  let g : ℕ→U := fun j=>project (F j)
  have dis (j : ℕ) (lo : 1≤j) (hi : j<m) (a : Bool) : g j≠r a := by
    obtain ⟨x,h⟩ := tag_is_cell (body lo hi)
    change project (F j)≠r a
    rw [h]
    cases a
    · exact x.property.1
    · exact x.property.2
  have inj (j k : ℕ) (j1 : 1≤j) (jm : j<m) (k1 : 1≤k) (km : k<m)
      (same : g j=g k) : j=k :=
    atNat_inj cy.1 (jm.trans_le mn) (km.trans_le mn)
      (project_eq_in_cell (body j1 jm) (body k1 km) same)
  have adj (j : ℕ) (j1 : 1≤j) (h : j+1<m) : A.Adj (g j) (g (j+1)) :=
    internal_projects L (step j) (body j1 (by omega)) (body (by omega) h)
  obtain ⟨b,bEdge⟩ := control_adjacency_project L entry
  have out : (graph L).Adj (F (m-1)) (control q) := eq ▸ ex
  obtain ⟨c,cEdge⟩ := control_adjacency_project L out
  obtain ⟨nz,lo,C⟩ := close_arc L.rootEdge m3 g b c dis inj adj bEdge cEdge.symm
  refine ⟨_,nz,lo,?_,C⟩
  split <;> omega

private theorem tags_of_body_cycle {n : ℕ} [NeZero n] {f : Fin n→V r}
    (no : ∀i,∃ p,tag (f i)=some p) (cy : CycleList (graph L) n f) (i : Fin n) :
    tag (f i)=tag (f 0) := by
  have each (i : Fin n) : tag (f i)=tag (f (i+1)) := by
    obtain ⟨p,hp⟩ := no i
    obtain ⟨q,hq⟩ := no (i+1)
    obtain ⟨u,up⟩ := tag_is_cell hp
    obtain ⟨v,vp⟩ := tag_is_cell hq
    rw [hp,hq]
    have a := cy.2 i
    rw [up,vp] at a
    exact congrArg some (separate L a)
  obtain ⟨k,hk⟩ := i
  induction k with
  | zero => rfl
  | succ k ih =>
    have shorter : k<n := by omega
    have h := each ⟨k,shorter⟩
    have p : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (show 1<n by omega)
    have t : ((⟨k,shorter⟩:Fin n)+1)=⟨k+1,hk⟩ := by
      apply Fin.ext
      rw [Fin.add_def]
      simp only [p,Nat.mod_eq_of_lt hk]
    rw [t] at h
    exact h.symm.trans (ih shorter)

/-- The two-root affine replacement does not decrease girth. -/
theorem girth_preserved (g : ℕ) (clean : NoCyclesBelow A g) :
    NoCyclesBelow (graph L) g := by
  intro n n3 ng inst cyc
  letI : NeZero n := inst
  obtain ⟨f,cy⟩ := cyc
  by_cases controlCycle : ∃ i l,f i=control l
  · obtain ⟨i,l,h⟩ := controlCycle
    have cs := cycle_shift cy i
    have card : ((fun t=>f (t+i)) 0)=control l := by simpa using h
    obtain ⟨k,nz,lo,hi,C⟩ := from_control L n3 cs l card
    exact clean k lo (hi.trans_lt ng) nz C
  · have no (i : Fin n) : ∃ p,tag (f i)=some p := by
      cases h : f i with
      | inl z => exact ⟨z.1,rfl⟩
      | inr q => exact (controlCycle ⟨i,q,h⟩).elim
    obtain ⟨p,hp⟩ := no 0
    have all (i : Fin n) : tag (f i)=some p := (tags_of_body_cycle L no cy i).trans hp
    apply clean n n3 ng inst
    refine ⟨fun j=>project (f j),⟨?_,?_⟩⟩
    · intro j k e
      exact cy.1 (project_eq_in_cell (all j) (all k) e)
    · intro i
      exact internal_projects L (cy.2 i) (all i) (all (i+1))

#print axioms girth_preserved
end
end KelmansCactus.AtomicBridge.AffineHost
