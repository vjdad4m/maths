import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace CazenaveRank
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)

/-- Project walks onto the induced graph by replacing one twin by the other. -/
theorem connected_remove_twins (hc : G.Connected) {u v : V} (hvu : v ≠ u)
    (ht : ∀ j, G.Adj u j ↔ G.Adj v j) :
    (G.induce {i | i ≠ u}).Connected := by
  classical
  let W := {i : V // i ≠ u}
  let q (i : V) : W := if h : i = u then ⟨v,hvu⟩ else ⟨i,h⟩
  have stay (i : W) : q i.val = i := by simp [q,i.property]
  let f : G →g G.induce {i | i ≠ u} :=
    { toFun := q
      map_rel' := by
        intro a b h
        change G.Adj (q a).val (q b).val
        by_cases ha : a = u <;> by_cases hb : b = u
        · subst a; subst b
          exact (G.loopless _ h).elim
        · subst a
          simpa [q,hb] using (ht b).mp h
        · subst b
          simpa [q,ha] using ((ht a).mp h.symm).symm
        · simpa [q,ha,hb] using h }
  exact hc.map f (fun i => ⟨i.val,stay i⟩)

#print axioms CazenaveRank.connected_remove_twins
end CazenaveRank
