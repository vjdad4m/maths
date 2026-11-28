import ParityArms

namespace Graffiti384b.OddStars.HallArms
open Finset SimpleGraph PositivePalette OneEar
open private OddStars.supported_away from TriangleBlocks
open private TrianglePrune.triangle_iff from TrianglePrune384b

variable {V : Type*} {J : SimpleGraph V} {e a b : V} {n : ℕ}

private theorem choose_parity (p : Route J e a b n) (len : 0<n) (k : ℕ) (bit : k<2)
    {w : V} (we : w≠e) (aw : J.Adj a w) (dw : J.Adj (p.atIdx 1) w) :
    ∃m,m%2=k ∧ Nonempty (Route J e a b m) := by
  classical
  by_cases already : n%2=k
  · exact ⟨n,already,⟨p⟩⟩
  have ad : J.Adj a (p.atIdx 1) := by simpa only [p.start] using p.step 0 len
  have ae : a≠e := by simpa only [p.start] using p.avoid 0 (by omega)
  have earlier (i j : ℕ) (ij : i<j) (jn : j≤n) : ∀ k≤n-j,p.atIdx i≠(p.suffix j jn).atIdx k := by
    intro k hk eq; have := p.unique i (by omega) (j+k) (by omega) eq; omega
  have absent {j : ℕ} (jp : 0<j) (jn : j≤n) : ∀ k≤n-j,a≠(p.suffix j jn).atIdx k :=
    by simpa only [p.start] using earlier 0 j jp jn
  by_cases hit : ∃i≤n,p.atIdx i=w
  · obtain ⟨i,hi,iw⟩ := hit
    have gap : 1<i := by
      by_contra! low
      rcases (show i=0 ∨ i=1 by omega) with rfl|rfl
      · exact aw.ne (p.start.symm.trans iw)
      · exact dw.ne iw
    let s := p.suffix i hi
    by_cases tail : (n-i+1)%2=k
    · let r := s.prepend (by rwa [iw]) ae (absent (by omega) hi)
      exact ⟨_,tail,⟨r⟩⟩
    · let r := s.prepend (by rwa [iw]) (p.avoid 1 (by omega)) (earlier 1 i gap hi)
      have fresh (j : ℕ) (hj : j≤n-i+1) : a≠r.atIdx j := by
        cases j with
        | zero => exact ad.ne
        | succ j => exact absent (by omega) hi _ (by omega)
      exact ⟨_,by omega,⟨r.prepend ad ae fresh⟩⟩
  · let s := p.suffix 1 (by omega)
    have fresh (j : ℕ) (hj : j≤n-1) : w≠s.atIdx j := fun eq => hit ⟨1+j,by omega,eq.symm⟩
    let r := s.prepend dw.symm we fresh
    have root (j : ℕ) (hj : j≤n-1+1) : a≠r.atIdx j := by
      cases j with
      | zero => exact aw.ne
      | succ j => exact absent (j:=1) (by decide) (by omega) _ (by omega)
    exact ⟨_,by omega,⟨r.prepend aw ae root⟩⟩

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a failure, every triangle witness in the terminal-deleted graph for
the last edge of either arm lies on the other arm. -/
theorem failure_terminal_hit (bad : bound G<gamma G) {e z a b c d w : V}
    (zz : trianglesAt G z=0) (dz : G.degree z=2) (one : trianglesAt G e=1)
    (ea : (patch G {z}).Adj e a) (eb : (patch G {z}).Adj e b)
    (zc : (patch G {z}).Adj z c) (zd : (patch G {z}).Adj z d) {n m : ℕ}
    (p : Route (inside (patch G {z}) ({e,z}ᶜ)) e a c n)
    (q : Route (inside (patch G {z}) ({e,z}ᶜ)) e b d m)
    (sep : ∀i≤n,∀j≤m,p.atIdx i≠q.atIdx j) (len : 0<n)
    (cw : (inside (patch G {z}) ({e,z}ᶜ)).Adj c w)
    (uw : (inside (patch G {z}) ({e,z}ᶜ)).Adj (p.atIdx (n-1)) w) : ∃j≤m,q.atIdx j=w := by
  classical
  let K := inside (patch G {z}) ({e,z}ᶜ)
  let O := (range (m+1)).image q.atIdx
  let L := inside K Oᶜ
  by_contra no
  have om {v : V} : v∈O ↔ ∃j≤m,q.atIdx j=v := by
    simp [O,Nat.lt_succ_iff]
  have pm (i : ℕ) (hi : i≤n) : p.atIdx i∉O :=
    fun h => by obtain ⟨j,hj,jp⟩ := om.mp h; exact sep _ hi _ hj jp.symm
  have wn : w∉O := fun h => no (om.mp h)
  let r : Route L e a c n := {
    atIdx := p.atIdx
    start := p.start
    finish := p.finish
    unique := p.unique
    avoid := p.avoid
    step := fun i hi => ⟨p.step i hi,mem_compl.mpr (pm i (by omega)),mem_compl.mpr (pm (i+1) (by omega))⟩
  }
  have cn : c∉O := by simpa only [p.finish] using pm n le_rfl
  have we : w≠e := fun eq => mem_compl.mp cw.2.2 (mem_insert.mpr (Or.inl eq))
  have lc : L.Adj c w := ⟨cw,mem_compl.mpr cn,mem_compl.mpr wn⟩
  have lu : L.Adj (r.reverse.atIdx 1) w := ⟨uw,mem_compl.mpr (pm (n-1) (by omega)),mem_compl.mpr wn⟩
  obtain ⟨l,par,⟨t⟩⟩ := choose_parity r.reverse len (m%2) (by omega) we lc lu
  let s := t.reverse
  let s' : Route K e a c l := {
    atIdx := s.atIdx
    start := s.start
    finish := s.finish
    unique := s.unique
    avoid := s.avoid
    step := fun i hi => (s.step i hi).1
  }
  have ss (i : ℕ) (hi : i≤l) : s'.atIdx i∉O := by
    cases i with
    | zero => change s.atIdx 0∉O; rw [s.start]; simpa only [p.start] using pm 0 (by omega)
    | succ i => exact mem_compl.mp (s.step i (by omega)).2.2
  have apart (i : ℕ) (hi : i≤l) (j : ℕ) (hj : j≤m) : s'.atIdx i≠q.atIdx j :=
    fun eq => ss i hi (om.mpr ⟨j,hj,eq.symm⟩)
  have fail := failure_opposite_parity G bad zz dz one ea eb zc zd s' q apart
  omega

/-- The last edge must have a triangle witness even after both terminals are
deleted. Its witness therefore occurs strictly before the other arm's end. -/
theorem failure_crossed_terminal (bad : bound G<gamma G) {e z a b c d : V}
    (zz : trianglesAt G z=0) (dz : G.degree z=2) (one : trianglesAt G e=1)
    (ea : (patch G {z}).Adj e a) (eb : (patch G {z}).Adj e b)
    (zc : (patch G {z}).Adj z c) (zd : (patch G {z}).Adj z d) {n m : ℕ}
    (p : Route (inside (patch G {z}) ({e,z}ᶜ)) e a c n)
    (q : Route (inside (patch G {z}) ({e,z}ᶜ)) e b d m)
    (sep : ∀i≤n,∀j≤m,p.atIdx i≠q.atIdx j) (len : 0<n) :
    let K := inside (patch G {z}) ({e,z}ᶜ)
    ∃j<m,K.Adj c (q.atIdx j) ∧ K.Adj (p.atIdx (n-1)) (q.atIdx j) := by
  classical
  let J := patch G {z}
  let K := inside J ({e,z}ᶜ)
  let u := p.atIdx (n-1)
  have uc : K.Adj u c := by
    have h := p.step (n-1) (by omega)
    rwa [show n-1+1=n by omega,p.finish] at h
  have cd : c≠d := by simpa only [p.finish,q.finish] using sep n le_rfl m le_rfl
  have pair : G.neighborFinset z={c,d} := (eq_of_subset_of_card_le
    (insert_subset ((G.mem_neighborFinset ..).mpr zc.1) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr zd.1)))
    (by rw [card_pair cd,card_neighborFinset_eq_degree,dz])).symm
  have uz : u≠z := fun eq => mem_compl.mp uc.2.1 (by simp [eq])
  obtain ⟨w,uw,cw⟩ := OddStars.supported_away G (S:={z}) Subset.rfl uz zc.ne.symm uc.1
  have we : w≠e := fun eq => disjoint_zero_ear G bad zz dz one zc.1 (eq ▸ cw.1.symm)
  have wz : w≠z := by
    rintro rfl
    have um := (G.mem_neighborFinset ..).mpr uw.1.symm
    rw [pair,mem_insert,mem_singleton] at um
    rcases um with h|h
    · exact uc.1.1.ne h
    · exact sep (n-1) (by omega) m le_rfl (h.trans q.finish.symm)
  have wm : w∈({e,z}:Finset V)ᶜ := by simp [we,wz]
  have kwc : K.Adj c w := ⟨cw,uc.2.2,wm⟩
  have kwu : K.Adj u w := ⟨uw,uc.2.1,wm⟩
  obtain ⟨j,hj,jw⟩ := failure_terminal_hit G bad zz dz one ea eb zc zd p q sep len kwc kwu
  have wd : w≠d := by
    rintro rfl
    have pos := (TrianglePrune.triangle_iff G z).mpr ⟨c,_,zc.1,zd.1,cw.1⟩
    omega
  exact ⟨j,lt_of_le_of_ne hj (fun eq => wd (jw.symm.trans (eq ▸ q.finish))),by rwa [jw],by rwa [jw]⟩

end Graffiti384b.OddStars.HallArms
#print axioms Graffiti384b.OddStars.HallArms.failure_terminal_hit
#print axioms Graffiti384b.OddStars.HallArms.failure_crossed_terminal