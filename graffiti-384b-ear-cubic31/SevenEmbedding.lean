import SevenContact
import Mathlib.Data.Fin.VecNotation

namespace Graffiti384b.Seven
open SimpleGraph Finset
open private third from SevenContact
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

set_option maxHeartbeats 4000000 in
theorem extract_pattern {e u x : V} (de : H.degree e=2) (du : H.degree u=3) (dx : H.degree x=4)
    (sx : trianglesAt H x=5) (eu : H.Adj e u) (pos : ∀ v,0<trianglesAt H v)
    (fi : Function.Injective (trianglesAt H)) (rest : ∀ v,v≠e → 3≤H.degree v)
    (half : Fintype.card V≤2*gamma H) :
    ∃ M : Pattern H,M.f 0=e ∧ M.f 1=u ∧ M.f 2=x := by
  classical
  obtain ⟨r,t,p,q,en,un,xn,_,er,ur,ut,rt,xe,xu,pr,pt,qr,qt,pq,npq,et⟩ :=
    contact H de du dx sx eu pos fi rest half
  have xrel (z : V) : H.Adj x z ↔ z=r ∨ z=t ∨ z=p ∨ z=q := by
    rw [←H.mem_neighborFinset,xn]; simp
  have erel (z : V) : H.Adj e z ↔ z=u ∨ z=r := by rw [←H.mem_neighborFinset,en]; simp
  have urel (z : V) : H.Adj u z ↔ z=e ∨ z=r ∨ z=t := by rw [←H.mem_neighborFinset,un]; simp
  have xr := (xrel r).2 (Or.inl rfl)
  have xt := (xrel t).2 (Or.inr (Or.inl rfl))
  have xp := (xrel p).2 (Or.inr (Or.inr (Or.inl rfl)))
  have xq := (xrel q).2 (Or.inr (Or.inr (Or.inr rfl)))
  have ex : e≠x := fun eq => by subst x; omega
  have ux : u≠x := fun eq => by subst x; omega
  have ep : e≠p := fun eq => xe (eq ▸ xp)
  have eq' : e≠q := fun eq => xe (eq ▸ xq)
  have up : u≠p := fun eq => xu (eq ▸ xp)
  have uq : u≠q := fun eq => xu (eq ▸ xq)
  have net : ¬H.Adj e t := fun h => ((erel t).mp h).elim ut.ne.symm rt.ne.symm
  have nep : ¬H.Adj e p := fun h => ((erel p).mp h).elim up.symm pr.ne
  have neq : ¬H.Adj e q := fun h => ((erel q).mp h).elim uq.symm qr.ne
  have nup : ¬H.Adj u p := fun h => ((urel p).mp h).elim ep.symm (fun h => h.elim pr.ne pt.ne)
  have nuq : ¬H.Adj u q := fun h => ((urel q).mp h).elim eq'.symm (fun h => h.elim qr.ne qt.ne)
  let f : Id→V := ![e,u,x,r,t,p,q]
  have inj : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact absurd h (by first | assumption | exact Ne.symm (by assumption) | exact SimpleGraph.Adj.ne (by assumption) | exact Ne.symm (SimpleGraph.Adj.ne (by assumption)))
  let F : Id ↪ V := ⟨f,inj⟩
  have edge (i j : Id) : H.Adj (F i) (F j) ↔ K.Adj i j := by
    fin_cases i <;> fin_cases j <;> first
      | exact iff_of_true (by first | assumption | exact SimpleGraph.Adj.symm (by assumption)) (by decide)
      | exact iff_of_false (by first | exact H.loopless _ | assumption | exact mt SimpleGraph.Adj.symm (by assumption)) (by decide)
  have mem (i : Id) : F i∈univ.map F := mem_map.mpr ⟨i,mem_univ _,rfl⟩
  have closed (i : Id) (im : i∈inner) (w : V) (adj : H.Adj (F i) w) : w∈univ.map F := by
    have choices : i=0 ∨ i=1 ∨ i=2 := by simpa [inner] using im
    rcases choices with rfl|rfl|rfl
    · rcases (erel w).mp adj with h|h
      · exact h ▸ mem 1
      · exact h ▸ mem 3
    · rcases (urel w).mp adj with h|h|h
      · exact h ▸ mem 0
      · exact h ▸ mem 3
      · exact h ▸ mem 4
    · rcases (xrel w).mp adj with h|h|h|h
      · exact h ▸ mem 3
      · exact h ▸ mem 4
      · exact h ▸ mem 5
      · exact h ▸ mem 6
  exact ⟨⟨F,edge,closed⟩,rfl,rfl,rfl⟩

theorem adjacent_bound {e u x : V} (n : Fintype.card V=30) (free : H.CliqueFree 5)
    (pos : ∀ v,0<trianglesAt H v) (fi : Function.Injective (trianglesAt H))
    (de : H.degree e=2) (du : H.degree u=3) (dx : H.degree x=4)
    (sx : trianglesAt H x=5) (eu : H.Adj e u) (rest : ∀ v,v≠e → 3≤H.degree v) : gamma H≤14 := by
  by_contra! bad
  have half : Fintype.card V≤2*gamma H := by omega
  obtain ⟨M,h0,h1,h2⟩ := extract_pattern H de du dx sx eu pos fi rest half
  obtain ⟨r,er,ur⟩ := third H de eu (pos e)
  obtain ⟨_,_,_,_,_,_,se,su⟩ := EarAnchor.diamond H de du eu er ur pos fi
  have z := M.pattern_bound n free pos fi (h0 ▸ se) (h1 ▸ su) (h2 ▸ sx)
  omega

end Graffiti384b.Seven
#print axioms Graffiti384b.Seven.extract_pattern
#print axioms Graffiti384b.Seven.adjacent_bound
