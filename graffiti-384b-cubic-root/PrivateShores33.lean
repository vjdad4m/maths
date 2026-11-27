import PrivateCut33
import ResidualContacts33

namespace Graffiti384b.RootCut
open Finset SimpleGraph HighEar OneEar EarAnchor ResidualShore
open private Repair.isolate from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

def interior (e a c x : V) : Finset V := (outside e a c).erase x

theorem mem_interior {e a c x z : V} : z∈interior e a c x ↔ z≠x ∧ z≠e ∧ z≠a ∧ z≠c := by
  simp only [interior,mem_erase,outside_mem]

omit [DecidableRel H.Adj] in
/-- After deletion of a safe pivot, a surviving triangle at one endpoint
belongs to a component having no contact with the other endpoint. -/
theorem no_contact {e a c x p q : V} (ae : a≠e) (ax : a≠x) (ac : a≠c) (ce : c≠e) (cx : c≠x)
    (pm : p∈interior e a c x) (qm : q∈interior e a c x)
    (ap : H.Adj a p) (aq : H.Adj a q) (pq : H.Adj p q)
    (odd : ∀ n,Route (Repair.isolate H x) e a c n → n%2=1) :
    ∀ w∈region H (interior e a c x) ⟨p,pm⟩,¬H.Adj w c := by
  classical
  let W := interior e a c x
  let J := Repair.isolate H x
  intro w wm wc
  obtain ⟨wi,reach⟩ := (region_mem H _ w).mp wm
  obtain ⟨walk,path⟩ := reach.exists_isPath
  let f (i : ℕ) := (walk.getVert i).val
  have inside (i : ℕ) : f i∈W := (walk.getVert i).property
  let route : Route J e p w walk.length := {
    atIdx := f
    start := congrArg Subtype.val walk.getVert_zero
    finish := congrArg Subtype.val walk.getVert_length
    step := fun i hi => ⟨walk.adj_getVert_succ hi,(mem_interior.mp (inside i)).1,(mem_interior.mp (inside _)).1⟩
    unique := fun i hi j hj eq => path.getVert_injOn hi hj (Subtype.ext eq)
    avoid := fun i _ => (mem_interior.mp (inside i)).2.1 }
  let rev := route.reverse.prepend (show J.Adj c w from ⟨wc.symm,cx,(mem_interior.mp wi).1⟩) ce
    (fun i _ => (mem_interior.mp (inside (walk.length-i))).2.2.2.symm)
  let forward := rev.reverse
  have fresh (i : ℕ) (hi : i≤walk.length+1) : a≠forward.atIdx i := by
    change a≠rev.atIdx (walk.length+1-i)
    generalize walk.length+1-i=j
    cases j with
    | zero => exact ac
    | succ j => exact (mem_interior.mp (inside (walk.length-j))).2.2.1.symm
  let whole := forward.prepend (show J.Adj a p from ⟨ap,ax,(mem_interior.mp pm).1⟩) ae fresh
  let K : Finset V := {a,p,q}
  have ja : J.Adj a p := ⟨ap,ax,(mem_interior.mp pm).1⟩
  have jb : J.Adj a q := ⟨aq,ax,(mem_interior.mp qm).1⟩
  have jc : J.Adj p q := ⟨pq,(mem_interior.mp pm).1,(mem_interior.mp qm).1⟩
  have cl : J.IsClique (K : Set V) := by
    intro i im j jm ne
    change i∈K at im; change j∈K at jm
    rcases (show i=a ∨ i=p ∨ i=q by simpa [K] using im) with rfl|rfl|rfl <;>
      rcases (show j=_ ∨ j=_ ∨ j=_ by simpa only [K,mem_insert,mem_singleton] using jm) with rfl|rfl|rfl <;>
      first | exact (ne rfl).elim | exact ja | exact ja.symm | exact jb | exact jb.symm | exact jc | exact jc.symm
  have sz : 3≤K.card := by simp [K,ap.ne,aq.ne,pq.ne]
  have ke : e∉K := by simp [K,ae.symm,(mem_interior.mp pm).2.1.symm,(mem_interior.mp qm).2.1.symm]
  have m0 : whole.atIdx 0∈K := mem_insert_self ..
  have m1 : whole.atIdx 1∈K := by
    change forward.atIdx 0∈K
    rw [forward.start]; simp [K]
  obtain ⟨l,par,⟨z⟩⟩ := AnchorParity.even_of_two_contacts cl sz ke whole (by decide : 0<1) (by omega) m0 m1
  have := odd l z
  omega

/-- A surviving pair of triangles supplies two disjoint regions. Away from
their own endpoint, each region contains all neighbors except the omitted pivot. -/
theorem shores {e a c x p q u v : V} (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (ear : H.neighborFinset e={a,c}) (ax : a≠x) (cx : c≠x)
    (pm : p∈interior e a c x) (qm : q∈interior e a c x) (um : u∈interior e a c x) (vm : v∈interior e a c x)
    (ap : H.Adj a p) (aq : H.Adj a q) (pq : H.Adj p q)
    (cu : H.Adj c u) (cv : H.Adj c v) (uv : H.Adj u v)
    (odd : ∀ n,Route (Repair.isolate H x) e a c n → n%2=1) :
    ∃ S T : Finset V,Disjoint S T ∧ a∈S ∧ c∈T ∧ e∉S∪T ∧ x∉S∪T ∧
      (∃ y∈S,H.Adj a y) ∧ (∃ y∈T,H.Adj c y) ∧
      (∀ y∈S,y≠a → ∀ z,H.Adj y z → z≠x → z∈S) ∧
      (∀ y∈T,y≠c → ∀ z,H.Adj y z → z≠x → z∈T) := by
  classical
  let W := interior e a c x
  let A := region H W ⟨p,pm⟩
  let B := region H W ⟨u,um⟩
  have flip : interior e c a x=W := by ext z; simp only [W,mem_interior]; tauto
  have Wsub {h : W} {y} (m : y∈region H W h) : y∈W := ((region_mem H _ y).mp m).choose
  have nc := no_contact H ea.ne.symm ax ac.ne ec.ne.symm cx pm qm ap aq pq odd
  have na : ∀ y∈B,¬H.Adj y a := by
    have h := no_contact H ec.ne.symm cx ac.ne.symm ea.ne.symm ax (flip ▸ um) (flip ▸ vm) cu cv uv (fun n r => odd n r.reverse)
    have move {D F : Finset V} (eq : D=F) {m : u∈D} {k : u∈F} : region H D ⟨u,m⟩=region H F ⟨u,k⟩ := by subst F; rfl
    rw [move flip (k:=um)] at h
    exact h
  have closed {f : W} {r b : V} (other : ∀ y∈region H W f,¬H.Adj y b) (rb : {r,b}=({a,c}:Finset V)) :
      ∀ y∈insert r (region H W f),y≠r → ∀ z,H.Adj y z → z≠x → z∈insert r (region H W f) := by
    intro y yi yr z yz zx
    have ym := (mem_insert.mp yi).resolve_left yr
    obtain ⟨yw,re⟩ := (region_mem H _ y).mp ym
    by_cases zr : z=r
    · exact mem_insert.mpr (Or.inl zr)
    have zb : z≠b := fun h => other y ym (h ▸ yz)
    have zo : z∉({a,c}:Finset V) := rb ▸ (by simp [zr,zb] : z∉({r,b}:Finset V))
    have ze : z≠e := by
      intro h
      have m := (H.mem_neighborFinset _ _).mpr (show H.Adj e y from h ▸ yz.symm)
      rw [ear] at m; exact (by simpa [not_or] using And.intro (mem_interior.mp yw).2.2.1 (mem_interior.mp yw).2.2.2 : y∉({a,c}:Finset V)) m
    have za : z≠a ∧ z≠c := by simpa [not_or] using zo
    have zw : z∈W := mem_interior.mpr ⟨zx,ze,za⟩
    have edge : (H.induce (W:Set V)).Adj (⟨y,yw⟩:W) ⟨z,zw⟩ := yz
    exact mem_insert_of_mem ((region_mem H _ z).mpr ⟨zw,re.trans edge.reachable⟩)
  have dis : Disjoint (insert a A) (insert c B) := by
    apply disjoint_left.mpr; intro y ay by'
    rcases mem_insert.mp ay with eq|ya
    · subst y; rcases mem_insert.mp by' with eq|yb
      · exact ac.ne eq
      · exact (mem_interior.mp (Wsub yb)).2.2.1 rfl
    rcases mem_insert.mp by' with eq|yb
    · exact (mem_interior.mp (Wsub ya)).2.2.2 eq
    obtain ⟨yw,ra⟩ := (region_mem H _ y).mp ya
    obtain ⟨_,rc⟩ := (region_mem H _ y).mp yb
    exact nc u ((region_mem H _ u).mpr ⟨um,ra.trans rc.symm⟩) cu.symm
  have avoid (z : V) (za : z≠a) (zc : z≠c) (out : z∉W) : z∉insert a A∪insert c B := by
    intro m; rcases mem_union.mp m with s|t
    · exact out (Wsub ((mem_insert.mp s).resolve_left za))
    · exact out (Wsub ((mem_insert.mp t).resolve_left zc))
  refine ⟨insert a A,insert c B,dis,mem_insert_self ..,mem_insert_self ..,
    avoid e ea.ne ec.ne (fun m => (mem_interior.mp m).2.1 rfl),
    avoid x ax.symm cx.symm (fun m => (mem_interior.mp m).1 rfl),?_,?_,closed nc rfl,closed na (pair_comm ..)⟩
  · exact ⟨p,mem_insert_of_mem ((region_mem H _ p).mpr ⟨pm,Reachable.refl _⟩),ap⟩
  · exact ⟨u,mem_insert_of_mem ((region_mem H _ u).mpr ⟨um,Reachable.refl _⟩),cu⟩

end Graffiti384b.RootCut
#print axioms Graffiti384b.RootCut.no_contact
#print axioms Graffiti384b.RootCut.shores
