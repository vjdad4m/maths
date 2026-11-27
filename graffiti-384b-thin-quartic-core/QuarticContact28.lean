import FourFrontier28

namespace Graffiti384b.Four28
open Finset SimpleGraph HighEar
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Different triangle counts distinguish the two endpoints somewhere outside
the ear triangle. The witness is adjacent to exactly one endpoint. -/
theorem distinguishing_contact {e p q : V} (en : H.neighborFinset e={p,q})
    (pq : H.Adj p q) (different : trianglesAt H p≠trianglesAt H q) :
    ∃ t,t≠e ∧ t≠p ∧ t≠q ∧ ¬(H.Adj p t ↔ H.Adj q t) := by
  classical
  have ep := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eq' := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have nen : H.neighborFinset e={q,p} := en.trans (pair_comm ..)
  have l := (exact_count H en ep eq' pq).2
  have r := (exact_count H nen eq' ep pq.symm).2
  by_contra! no
  have ex : exterior H e p q=exterior H e q p := by
    ext v
    by_cases ve : v=e
    · subst v; simp [exterior]
    by_cases vp : v=p
    · subst v; simp [exterior]
    by_cases vq : v=q
    · subst v; simp [exterior]
    simpa [exterior,ve,vp,vq] using no v ve vp vq
  have both : additional H e p q=additional H e q p := by simp [additional,inter_comm]
  exact different (by rw [l,r,ex,both])

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.distinguishing_contact
