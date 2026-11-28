import OreClosure189
import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

theorem rooted_Ore_with_two_roots
    (hc : J.Connected) (K : Finset V) (roots : 2≤K.card)
    (high : V→Prop) (oneLow : ∀ u v,u≠v → high u ∨ high v)
    (cap : ∀ u v,high u → high v → u≠v → Fintype.card V≤J.degree u+J.degree v) :
    ∃ r∈K,RootedSpan J r := by
  classical
  let A : Finset V := univ.filter high
  let H := completeWith J A
  have sub : J≤H := completeWith_mono J A
  have C : CompleteOn H A := completeWith_of_mem J A
  have ae (x : V) : x∈A ↔ high x := by simp [A]
  have ok (u v : V) (uv : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card V≤J.degree u+J.degree v := by
    change J.Adj u v ∨ _ at uv
    obtain ⟨ua,va,ne⟩ := uv.resolve_left no
    exact cap u v ((ae u).mp ua) ((ae v).mp va) ne
  have lift {r t : V} (path : RouteOn H univ r t) : RootedSpan J r := by
    obtain ⟨p,pp,ps⟩ := path
    exact Graffiti189Ore.rooted_closure sub r ok ⟨t,p,pp,fun z=>(ps z).mpr (mem_univ _)⟩
  obtain ⟨u,uk,v,vk,uv⟩ := one_lt_card.mp roots
  by_cases low : ∃ z, ¬high z
  · obtain ⟨z,zlow⟩ := low
    have aEq : A = univ.erase z := by
      ext w
      rw [ae]
      by_cases wz : w=z
      · simp [wz,zlow]
      have wh := (oneLow w z wz).resolve_right zlow
      simp [wz,wh]
    have full : insert z A=(univ:Finset V) := by rw [aEq,insert_erase (mem_univ _)]
    have zA : z∉A := fun h=>zlow ((ae z).mp h)
    have meet : ∃ w, J.Adj z w := by
      have exists_ne : ∃ q, z≠q := by
        by_cases ez : z=u
        · exact ⟨v,ez ▸ uv⟩
        · exact ⟨u,ez⟩
      obtain ⟨q,zq⟩ := exists_ne
      obtain ⟨p⟩ := hc.preconnected z q
      cases p with
      | nil => exact (zq rfl).elim
      | @cons _ w _ zw _ => exact ⟨w,zw⟩
    obtain ⟨w,zw⟩ := meet
    have wA : w∈A := (ae w).mpr ((oneLow w z zw.ne.symm).resolve_right zlow)
    by_cases zk : z∈K
    · obtain ⟨t,p,pp,ps⟩ := rooted_path_in_clique A C wA
      have route : RouteOn H A w t := ⟨p,pp,ps⟩
      exact ⟨z,zk,lift (full ▸ route.prefix (sub zw) zA)⟩
    have pick : ∃ r∈K,r≠z ∧ r≠w := by
      by_cases uw : u=w
      · exact ⟨v,vk,fun vz=>zk (vz ▸ vk),fun vw=>uv (uw.trans vw.symm)⟩
      · exact ⟨u,uk,fun uz=>zk (uz ▸ uk),uw⟩
    obtain ⟨r,rk,rz,rw⟩ := pick
    have rA := (ae r).mpr ((oneLow r z rz).resolve_right zlow)
    obtain ⟨p,pp,ps⟩ := path_between_in_clique A C rA wA rw
    have route : RouteOn H A r w := ⟨p,pp,ps⟩
    exact ⟨r,rk,lift (full ▸ route.suffix (sub zw.symm) zA)⟩
  have aEq : A=(univ:Finset V) := by
    ext w
    rw [ae]
    simp only [mem_univ,iff_true]
    exact Classical.byContradiction (fun h=>low ⟨w,h⟩)
  obtain ⟨p,pp,ps⟩ := path_between_in_clique A C
    (show u∈A by simp [aEq]) (show v∈A by simp [aEq]) uv
  exact ⟨u,uk,lift (aEq ▸ (show RouteOn H A u v from ⟨p,pp,ps⟩))⟩

#print axioms rooted_Ore_with_two_roots
end Graffiti189LongestPath.CrossSaturation
