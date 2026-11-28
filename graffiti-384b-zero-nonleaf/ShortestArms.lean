import TerminalArms

namespace Graffiti384b.OddStars.HallArms
open Finset SimpleGraph PositivePalette OneEar
variable {V : Type*} {J : SimpleGraph V} {e a b : V} {n : ℕ}

/-- Follow the prefix through index i, then use a fresh final vertex. -/
def truncate_append (p : Route J e a b n) {i : ℕ} (hi : i≤n) {d : V}
    (edge : J.Adj (p.atIdx i) d) (de : d≠e) (fresh : ∀k≤i,p.atIdx k≠d) : Route J e a d (i+1) where
  atIdx k := if k≤i then p.atIdx k else d
  start := by simp [p.start]
  finish := by simp
  step k hk := by
    by_cases eq : k=i
    · subst k; simpa using edge
    · simpa only [if_pos (show k≤i by omega),if_pos (show k+1≤i by omega)] using p.step k (by omega)
  unique k hk l hl h := by
    by_cases k₁ : k≤i <;> by_cases l₁ : l≤i <;> simp only [k₁,l₁,if_true,if_false] at h
    · exact p.unique k (by omega) l (by omega) h
    · exact (fresh _ k₁ h).elim
    · exact (fresh _ l₁ h.symm).elim
    · omega
  avoid k hk := by
    split <;> rename_i side
    · exact p.avoid _ (by omega)
    · exact de

structure Link (J : SimpleGraph V) [Fintype V] [DecidableEq V] (e z a b : V) where
  c : V
  d : V
  zc : J.Adj z c
  zd : J.Adj z d
  n : ℕ
  m : ℕ
  p : Route (inside J ({e,z}ᶜ)) e a c n
  q : Route (inside J ({e,z}ᶜ)) e b d m
  sep : ∀i≤n,∀j≤m,p.atIdx i≠q.atIdx j

variable [Fintype V] [DecidableEq V]

private def cross_link {J : SimpleGraph V} {e z a b : V} (L : Link J e z a b) {i j : ℕ}
    (hi : i<L.n) (hj : j<L.m) (id' : (inside J ({e,z}ᶜ)).Adj (L.p.atIdx i) L.d)
    (jc : (inside J ({e,z}ᶜ)).Adj (L.q.atIdx j) L.c) : Link J e z a b := by
  let P := truncate_append L.p hi.le id' (by simpa only [L.q.finish] using L.q.avoid L.m le_rfl)
    (fun k hk eq => L.sep k (by omega) _ le_rfl (eq.trans L.q.finish.symm))
  let Q := truncate_append L.q hj.le jc (by simpa only [L.p.finish] using L.p.avoid L.n le_rfl)
    (fun k hk eq => L.sep _ le_rfl k (by omega) (L.p.finish.trans eq.symm))
  refine ⟨L.d,L.c,L.zd,L.zc,i+1,j+1,P,Q,?_⟩
  intro k hk l hl eq
  change (if k≤i then L.p.atIdx k else L.d)=(if l≤j then L.q.atIdx l else L.c) at eq
  by_cases kp : k≤i <;> by_cases lp : l≤j <;> simp only [kp,lp,if_true,if_false] at eq
  · exact L.sep _ (by omega) _ (by omega) eq
  · have h := L.p.unique k (by omega) L.n le_rfl (eq.trans L.p.finish.symm)
    omega
  · have h := L.q.unique L.m le_rfl l (by omega) (L.q.finish.trans eq)
    omega
  · exact L.sep _ le_rfl _ le_rfl (L.p.finish.trans (eq.symm.trans L.q.finish.symm))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A minimum-total-length linkage has a terminal diamond: the penultimate
vertices are adjacent, and both join both final vertices. -/
theorem minimum_diamond (bad : bound G<gamma G) {e z a b : V}
    (zz : trianglesAt G z=0) (dz : G.degree z=2) (one : trianglesAt G e=1)
    (ea : (patch G {z}).Adj e a) (eb : (patch G {z}).Adj e b)
    (someLink : Nonempty (Link (patch G {z}) e z a b)) :
    let J := patch G {z}
    let K := inside J ({e,z}ᶜ)
    ∃L : Link J e z a b, 0<L.n ∧ 0<L.m ∧ (L.n+L.m)%2=1 ∧
      K.Adj (L.p.atIdx (L.n-1)) (L.q.atIdx (L.m-1)) ∧
      K.Adj L.c (L.q.atIdx (L.m-1)) ∧ K.Adj L.d (L.p.atIdx (L.n-1)) := by
  classical
  let J := patch G {z}
  let P (k : ℕ) := ∃L : Link J e z a b,L.n+L.m=k
  obtain ⟨seed⟩ := someLink
  have ex : ∃k,P k := ⟨_,seed,rfl⟩
  obtain ⟨L,chosen⟩ := Nat.find_spec ex
  have npos : 0<L.n := by
    apply Nat.pos_of_ne_zero
    intro zero
    have ac := L.p.start.symm.trans ((congrArg L.p.atIdx zero.symm).trans L.p.finish)
    exact disjoint_zero_ear G bad zz dz one L.zc.1 (ac ▸ ea.1)
  have mpos : 0<L.m := by
    apply Nat.pos_of_ne_zero
    intro zero
    have bd := L.q.start.symm.trans ((congrArg L.q.atIdx zero.symm).trans L.q.finish)
    exact disjoint_zero_ear G bad zz dz one L.zd.1 (bd ▸ eb.1)
  have odd := failure_opposite_parity G bad zz dz one ea eb L.zc L.zd L.p L.q L.sep
  obtain ⟨j,jm,cj,uj⟩ := failure_crossed_terminal G bad zz dz one ea eb L.zc L.zd L.p L.q L.sep npos
  obtain ⟨i,inn,di,_⟩ := failure_crossed_terminal G bad zz dz one eb ea L.zd L.zc L.q L.p
    (fun k hk l hl eq => L.sep l hl k hk eq.symm) mpos
  let shorter := cross_link L inn jm di.symm cj.symm
  have poss : P (i+1+(j+1)) := ⟨shorter,rfl⟩
  have best := Nat.find_min' ex poss
  have ik : i=L.n-1 := by omega
  have jk : j=L.m-1 := by omega
  exact ⟨L,npos,mpos,odd,jk ▸ uj,jk ▸ cj,ik ▸ di⟩

end Graffiti384b.OddStars.HallArms
#print axioms Graffiti384b.OddStars.HallArms.minimum_diamond