import RootedOreExceptPair189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

/-- Completing missing high-high edges suffices for a rooted spanning
path with just two candidate roots, when there is at most one low. -/
theorem rooted_Ore_from_two_candidates
    (hc : J.Connected) (K : Finset V) (two : 2≤K.card)
    (high : V→Prop) (oneLow : ∀ u v,u≠v → high u ∨ high v)
    (cap : ∀ u v,high u → high v → u≠v → ¬J.Adj u v →
      Fintype.card V≤J.degree u+J.degree v) :
    ∃ r∈K,RootedSpan J r := by
  classical
  let A := univ.filter high
  let H := completeWith J A
  have sub : J≤H := completeWith_mono J A
  have cl : CompleteOn H A := completeWith_of_mem J A
  have ok (u v : V) (uv : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card V≤J.degree u+J.degree v := by
    change J.Adj u v ∨ _ at uv
    obtain ⟨ua,va,n⟩ := uv.resolve_left no
    exact cap u v (mem_filter.mp ua).2 (mem_filter.mp va).2 n no
  have pull {r t : V} (p : RouteOn H univ r t) : RootedSpan J r := by
    obtain ⟨q,qp,qs⟩ := p
    exact Graffiti189Ore.rooted_closure sub r ok ⟨t,q,qp,fun v=>(qs v).mpr (mem_univ _)⟩
  have other (w : V) : ∃ r∈K,r≠w := by
    apply Classical.byContradiction
    intro h
    have range : K⊆{w} := fun r rk=>mem_singleton.mpr
      (Classical.byContradiction (fun n=>h ⟨r,rk,n⟩))
    have c := card_le_card range
    rw [card_singleton] at c
    omega
  by_cases low : ∃ z,¬high z
  · obtain ⟨z,zlow⟩ := low
    have aEq : A=univ.erase z := by
      ext u
      change u∈univ.filter high ↔ _
      by_cases uz : u=z
      · simp [uz,zlow]
      have h := (oneLow u z uz).resolve_right zlow
      simp [h,uz]
    obtain ⟨b,_,bz⟩ := other z
    obtain ⟨p⟩ := hc.preconnected z b
    have meet : ∃ w,J.Adj z w := by
      cases p with
      | nil => exact (bz rfl).elim
      | cons e p => exact ⟨_,e⟩
    obtain ⟨w,zw⟩ := meet
    have wa : w∈A := by simp [aEq,zw.ne.symm]
    have zs : z∉A := by simp [aEq]
    have eq : insert z A=(univ : Finset V) := by rw [aEq,insert_erase (mem_univ _)]
    by_cases zk : z∈K
    · obtain ⟨t,p,pp,ps⟩ := rooted_path_in_clique A cl wa
      have r : RouteOn H A w t := ⟨p,pp,ps⟩
      exact ⟨z,zk,pull (eq ▸ r.prefix (sub zw) zs)⟩
    obtain ⟨r,rk,rw⟩ := other w
    have rz : r≠z := fun e=>zk (e ▸ rk)
    have ra : r∈A := by simp [aEq,rz]
    obtain ⟨p,pp,ps⟩ := path_between_in_clique A cl ra wa rw
    have route : RouteOn H A r w := ⟨p,pp,ps⟩
    exact ⟨r,rk,pull (eq ▸ route.suffix (sub zw.symm) zs)⟩
  obtain ⟨r,rk⟩ := card_pos.mp (show 0<K.card by omega)
  have aEq : A=(univ : Finset V) := by
    ext u
    have hu : high u := Classical.byContradiction (fun n=>low ⟨u,n⟩)
    simp [A,hu]
  have ra : r∈A := by simp [aEq]
  obtain ⟨t,p,pp,ps⟩ := rooted_path_in_clique A cl ra
  have route : RouteOn H A r t := ⟨p,pp,ps⟩
  exact ⟨r,rk,pull (aEq ▸ route)⟩

#print axioms rooted_Ore_from_two_candidates
end Graffiti189LongestPath.CrossSaturation
