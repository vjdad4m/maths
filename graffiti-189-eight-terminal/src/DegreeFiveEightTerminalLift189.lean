import DegreeFiveEightTerminalTable189
import DegreeFiveRouteBasic189

namespace Graffiti189EightTerminal
open SimpleGraph SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V}

private theorem recover_list_walk (a : V) (L : List V)
    (cl : List.Chain' G.Adj (a::L)) : ∃ b,∃ q : G.Walk a b,q.support=a::L := by
  induction L generalizing a with
  | nil => exact ⟨a,.nil,rfl⟩
  | cons b L ih =>
    obtain ⟨c,q,eq⟩ := ih b cl.tail
    exact ⟨c,.cons cl.rel_head q,by simp [eq]⟩

/-- Lift the eight-point route along a labelling of a completed shore. -/
theorem walk_of_completed_route (e : Fin 8 ≃ V) (i j : Fin 8)
    (hi : i.val < 5) (hj : j.val < 5) (ne : i ≠ j)
    (edges : ∀ u v, allowed i j u v → G.Adj (e u) (e v)) :
    ∃ u v : Fin 8, u.val < 2 ∧ 2 ≤ v.val ∧ v.val < 5 ∧
      ∃ p : G.Walk (e u) (e v), p.IsPath ∧ ∀ z, z ∈ p.support := by
  obtain ⟨L,nd,all,chain,⟨u,um,uh⟩,⟨v,vm,vt⟩⟩ := completed_route i j hi hj ne
  have u2 : u.val < 2 := by
    have q : u=0 ∨ u=1 := by simpa using um
    rcases q with q|q <;> rw [q] <;> decide
  have v2 : 2 ≤ v.val ∧ v.val < 5 := by
    have q : v=2 ∨ v=3 ∨ v=4 := by simpa using vm
    rcases q with q|q|q <;> rw [q] <;> decide
  refine ⟨u,v,u2,v2.1,v2.2,?_⟩
  let M := L.map (e : Fin 8 → V)
  have mChain : List.Chain' G.Adj M := List.chain'_map_of_chain' e edges chain
  have mNd : M.Nodup := nd.map e.injective
  have mAll (z : V) : z ∈ M :=
    List.mem_map.mpr ⟨e.symm z,all _,e.apply_symm_apply z⟩
  have mHead : M.head? = some (e u) := by simp [M,List.head?_map,uh]
  have mTail : M.getLast? = some (e v) := by simp [M,List.getLast?_map,vt]
  cases hm : M with
  | nil => simp [hm] at mHead
  | cons x xs =>
    rw [hm] at mHead
    have ex : x = e u := Option.some.inj mHead
    obtain ⟨z,p,ps⟩ := recover_list_walk x xs (hm ▸ mChain)
    have ez : z = e v := by
      rw [hm,←ps] at mTail
      rw [List.getLast?_eq_getLast_of_ne_nil (by simp), p.getLast_support] at mTail
      exact Option.some.inj mTail
    subst x
    subst z
    exact ⟨p,IsPath.mk' (ps.symm ▸ (hm ▸ mNd)),fun w => ps.symm ▸ (hm ▸ mAll w)⟩

#print axioms walk_of_completed_route
end Graffiti189EightTerminal
