import MarkedWing60Cert189
import MarkedWing62Cert189
import MarkedWing70Cert189
import MarkedWing72Cert189
import MarkedWing80Cert189
import MarkedWing82Cert189

open Finset SimpleGraph SimpleGraph.Walk
namespace Graffiti189LongestPath.MarkedWingPath

private theorem fixed {n : ℕ} [NeZero n] (h : 6≤n ∧ n≤8) {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (z : Fin n) (zz : z=0 ∨ z=2) (degrees : ∀ i,(if i=z then 2 else 4)≤G.degree i) :
    ∃ p : G.Walk 0 1,p.IsPath ∧ 4≤p.length := by
  have nn : n=6 ∨ n=7 ∨ n=8 := by omega
  rcases nn with rfl|rfl|rfl <;> rcases zz with rfl|rfl
  · exact MarkedWingSat.Core60.fixed degrees
  · exact MarkedWingSat.Core62.fixed degrees
  · exact MarkedWingSat.Core70.fixed degrees
  · exact MarkedWingSat.Core72.fixed degrees
  · exact MarkedWingSat.Core80.fixed degrees
  · exact MarkedWingSat.Core82.fixed degrees

private theorem labels {W : Type*} [DecidableEq W] (x y w : W) (xy : x≠y)
    (h : 6≤n) [NeZero n] (e : Fin n ≃ W) (wne : w≠y) :
    ∃ (f : Fin n ≃ W) (z : Fin n), f 0=x ∧ f 1=y ∧ f z=w ∧ (z=0 ∨ z=2) := by
  let e0 := e.trans (Equiv.swap (e 0) x)
  have x0 : e0 0=x := Equiv.swap_apply_left _ _
  let e1 := e0.trans (Equiv.swap (e0 1) y)
  have y1 : e1 1=y := Equiv.swap_apply_left _ _
  have x1 : e1 0=x := by
    change (Equiv.swap (e0 1) y) (e0 0)=x
    rw [Equiv.swap_apply_of_ne_of_ne (fun e => by
      have q := congrArg Fin.val (e0.injective e)
      simp [Nat.mod_eq_of_lt (show 0<n by omega),Nat.mod_eq_of_lt (show 1<n by omega)] at q)
      (by rwa [x0])]
    exact x0
  by_cases wx : w=x
  · exact ⟨e1,0,x1,y1,x1.trans wx.symm,Or.inl rfl⟩
  let e2 := e1.trans (Equiv.swap (e1 2) w)
  have p0 : (0:Fin n)≠2 := by
    intro e
    have q := congrArg Fin.val e
    change 0%n=2%n at q
    rw [Nat.mod_eq_of_lt (show 0<n by omega),Nat.mod_eq_of_lt (show 2<n by omega)] at q
    omega
  have p1 : (1:Fin n)≠2 := by
    intro e
    have q := congrArg Fin.val e
    change 1%n=2%n at q
    rw [Nat.mod_eq_of_lt (show 1<n by omega),Nat.mod_eq_of_lt (show 2<n by omega)] at q
    omega
  refine ⟨e2,2,?_,?_,Equiv.swap_apply_left _ _,Or.inr rfl⟩
  · change (Equiv.swap (e1 2) w) (e1 0)=x
    rw [Equiv.swap_apply_of_ne_of_ne (fun h => p0 (e1.injective h)) (by rwa [x1,ne_comm])]
    exact x1
  · change (Equiv.swap (e1 2) w) (e1 1)=y
    rw [Equiv.swap_apply_of_ne_of_ne (fun h => p1 (e1.injective h)) (by rwa [y1,ne_comm])]
    exact y1

variable {W : Type*} [Fintype W] [DecidableEq W] {D : SimpleGraph W} [DecidableRel D.Adj]

private theorem with_exception (n : ℕ) (hn : 6≤n ∧ n≤8) (card : Fintype.card W=n)
    (z x y : W) (xy : x≠y) (zy : z≠y)
    (lo : 2≤D.degree z) (hi : ∀ u,u≠z→4≤D.degree u) :
    ∃ p : D.Walk x y,p.IsPath ∧ 4≤p.length := by
  classical
  letI : NeZero n := ⟨by have := hn.1; omega⟩
  obtain ⟨f,j,x0,y1,jz,jn⟩ := labels x y z xy hn.1 (Fintype.equivFinOfCardEq card).symm zy
  let G : SimpleGraph (Fin n) := D.comap f
  letI : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (D.Adj (f u) (f v)))
  have deg (i : Fin n) : G.degree i=D.degree (f i) := by
    rw [←G.card_neighborFinset_eq_degree,←D.card_neighborFinset_eq_degree]
    apply card_bij' (fun a _ => f a) (fun b _ => f.symm b)
    · intro a aa
      exact (D.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp aa)
    · intro a aa
      exact (G.mem_neighborFinset _ _).mpr (by
        change D.Adj (f i) (f (f.symm a))
        rw [f.apply_symm_apply]
        exact (D.mem_neighborFinset _ _).mp aa)
    · intro u hu; exact f.symm_apply_apply u
    · intro u hu; exact f.apply_symm_apply u
  have d (i : Fin n) : (if i=j then 2 else 4)≤G.degree i := by
    rw [deg]
    by_cases h : i=j
    · subst i
      rw [if_pos rfl,jz]
      exact lo
    · rw [if_neg h]
      exact hi _ (fun e => h (f.injective (e.trans jz.symm)))
  obtain ⟨q,qp,ql⟩ := fixed hn j jn d
  let h : G →g D := ⟨f,fun e => e⟩
  let p := q.map h
  have pp := map_isPath_of_injective (show Function.Injective h from f.injective) qp
  have pl : 4≤p.length := by simpa [p] using ql
  exact ⟨p.copy x0 y1,by simpa [p] using pp,by simpa [p] using pl⟩

/-- A core of six through eight vertices, with internal degree at least
four except for at most one vertex of degree at least two, admits a
five-vertex-or-longer route between every prescribed distinct pair. -/
theorem long_marked_path (hn : 6≤Fintype.card W ∧ Fintype.card W≤8)
    (floor : ∀ u,2≤D.degree u)
    (high : ∀ u v,u≠v→4≤D.degree u ∨ 4≤D.degree v) {x y : W} (xy : x≠y) :
    ∃ q : D.Walk x y,q.IsPath ∧ 4≤q.length := by
  classical
  by_cases he : ∃ z,D.degree z<4
  · obtain ⟨z,zl⟩ := he
    have hz (u : W) (uz : u≠z) : 4≤D.degree u :=
      (high u z uz).resolve_right (Nat.not_le_of_lt zl)
    by_cases zy : z=y
    · obtain ⟨p,pp,pl⟩ := with_exception _ hn rfl z y x xy.symm
        (fun zx => xy (zx.symm.trans zy)) (floor z) hz
      exact ⟨p.reverse,pp.reverse,by simpa using pl⟩
    · exact with_exception _ hn rfl z x y xy zy (floor z) hz
  · exact with_exception _ hn rfl x x y xy xy (floor x)
      (fun u _ => Nat.le_of_not_gt (fun e => he ⟨u,e⟩))

#print axioms long_marked_path
end Graffiti189LongestPath.MarkedWingPath
