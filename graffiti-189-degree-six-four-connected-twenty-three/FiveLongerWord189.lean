import FiveCheapBudget189

open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.FiveCheapBudget
set_option linter.unusedSectionVars false
namespace Graffiti189LongestPath.FiveLongerWord
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b x y : V} {p : G.Walk a b} {H : Finset V} {i j s t : ℕ}

def embed (p : G.Walk a b) (x : V) (m : Fin 19) : V :=
  if m.val=18 then x else p.getVert m.val

private theorem walk_of_chain (u : V) (L : List V)
    (cl : List.Chain' G.Adj (u::L)) : ∃ b,∃ q : G.Walk u b,q.support=u::L := by
  induction L generalizing u with
  | nil => exact ⟨u,.nil,rfl⟩
  | cons v L ih =>
    obtain ⟨c,q,eq⟩ := ih v cl.tail
    exact ⟨c,.cons cl.rel_head q,by simp [eq]⟩

theorem impossible (A : PairData p H x y i j s t) (hp : IsLongest p)
    (w : List (Fin 19)) (nd : w.Nodup) (length : w.length=19)
    (chain : (w.map (embed p x)).Chain' G.Adj) : False := by
  have inj : Function.Injective (embed p x) := by
    intro m n e
    have ml := m.isLt
    have nl := n.isLt
    by_cases me : m.val=18 <;> by_cases ne : n.val=18
    · exact Fin.ext (by omega)
    · exact (A.off _ A.xH (by rw [show x=p.getVert n.val by simpa [embed,me,ne] using e]; exact p.getVert_mem_support _)).elim
    · exact (A.off _ A.xH (by rw [←show p.getVert m.val=x by simpa [embed,me,ne] using e]; exact p.getVert_mem_support _)).elim
    · apply Fin.ext
      have ll := A.pathLen
      apply hp.1.getVert_injOn (show m.val≤p.length by omega) (show n.val≤p.length by omega)
      simpa [embed,me,ne] using e
  have nd' := nd.map inj
  have eqL : (w.map (embed p x)).length=19 := by simpa using length
  cases eq : w.map (embed p x) with
  | nil => simp [eq] at eqL
  | cons u L =>
    rw [eq] at chain nd' eqL
    obtain ⟨v,q,qs⟩ := walk_of_chain u L chain
    have pp : q.IsPath := by rwa [isPath_def,qs]
    have lq := q.length_support
    rw [qs,eqL] at lq
    have ll := A.pathLen
    have le := hp.2 _ _ q pp
    omega

#print axioms impossible
end Graffiti189LongestPath.FiveLongerWord
