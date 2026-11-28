import SixThree20LowRotation189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.lengths_take_drop Graffiti189LongestPath.Rigidity.split_path_edge
  from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem getVert_take_local {a b : V} (p : G.Walk a b) (n i : ℕ) (hi : i≤n) :
    (p.take n).getVert i=p.getVert i := by
  induction p generalizing n i with
  | nil => cases n <;> cases i <;> rfl
  | @cons a b c e p ih =>
    cases n with
    | zero =>
      have q : i=0 := by omega
      subst i
      simp
    | succ n =>
      cases i with
      | zero => simp
      | succ i => exact ih n i (by omega)

theorem rotate_start_indexed_prefix {a b : V} {p : G.Walk a b} (hp : IsLongest p) (j : ℕ)
    (jl : j<p.length) (jump : G.Adj a (p.getVert (j+1))) :
    ∃ q : G.Walk (p.getVert j) b, IsLongest q ∧
      (∀ z,z∈p.support ↔ z∈q.support) ∧
      ∀ t,t≤j → q.getVert t=p.getVert (j-t) := by
  let l := p.take j
  let r := p.drop (j+1)
  let q := l.reverse.append (.cons jump r)
  have split := Graffiti189LongestPath.Rigidity.split_path_edge p j jl
  have ps : p.support=l.support++r.support := by
    conv_lhs => rw [←split]
    simp only [support_append,support_cons,List.tail_cons,l,r]
  have qs : q.support=l.support.reverse++r.support := by
    simp only [q,support_append,support_reverse,support_cons,List.tail_cons]
  have qpath : q.IsPath := by
    rw [isPath_def,qs,List.nodup_append]
    have nd := hp.1.support_nodup
    rw [ps,List.nodup_append] at nd
    exact ⟨List.nodup_reverse.mpr nd.1,nd.2.1,fun _ u v=>nd.2.2 (List.mem_reverse.mp u) v⟩
  have llen : l.length=j := (Graffiti189LongestPath.Rigidity.lengths_take_drop p j (by omega)).1
  have rlen : r.length=p.length-(j+1) :=
    (Graffiti189LongestPath.Rigidity.lengths_take_drop p (j+1) (by omega)).2
  have len : q.length=p.length := by
    simp only [q,length_append,length_reverse,length_cons,llen,rlen]
    omega
  refine ⟨q,⟨qpath,fun u v w hw=>len.symm ▸ hp.2 u v w hw⟩,
    fun z=>by simp [ps,qs],?_⟩
  intro t tj
  by_cases eq : t=j
  · subst t
    rw [show q=l.reverse.append (Walk.cons jump r) from rfl,getVert_append,length_reverse,llen,if_neg (by omega)]
    simp
  have lt : t<l.reverse.length := by rw [length_reverse,llen]; omega
  rw [show q=l.reverse.append (Walk.cons jump r) from rfl,getVert_append,if_pos lt,getVert_reverse,llen]
  exact getVert_take_local p j (j-t) (by omega)

#print axioms rotate_start_indexed_prefix
end Graffiti189LongestPath.SixThreeTwenty
