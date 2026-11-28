import SixThree19LowRotation189

namespace Graffiti189LongestPath.SixThreeNineteen
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

private theorem getVert_drop_local {a b : V} (p : G.Walk a b) (n i : ℕ) :
    (p.drop n).getVert i=p.getVert (n+i) := by
  induction p generalizing n i with
  | nil => cases n <;> cases i <;> rfl
  | @cons a b c e p ih =>
    cases n with
    | zero => simp [Walk.drop]
    | succ n =>
      rw [show n+1+i=n+i+1 by omega]
      exact ih n i

theorem rotate_start_both_extreme_indices {a b : V} {p : G.Walk a b} (hp : IsLongest p) (j : ℕ)
    (j0 : 0<j) (jh : j+1<p.length) (jump : G.Adj a (p.getVert (j+1))) :
    ∃ q : G.Walk (p.getVert j) b, IsLongest q ∧
      (∀ z,z∈p.support ↔ z∈q.support) ∧ q.getVert 1=p.getVert (j-1) ∧
      q.getVert (q.length-1)=p.getVert (p.length-1) := by
  have jl : j<p.length := by omega
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
  have qLv : q.getVert 1=p.getVert (j-1) := by
    by_cases eq : j=1
    · have a0 : p.getVert (j-1)=a := by simp [eq]
      have j' : 1-l.reverse.length=0 := by simp [llen,eq]
      rw [show q=l.reverse.append (Walk.cons jump r) from rfl,getVert_append,
        if_neg (by simp [llen,eq]),j',getVert_zero,a0]
    have m : 1<l.reverse.length := by simp [llen]; omega
    rw [show q=l.reverse.append (Walk.cons jump r) from rfl,getVert_append,if_pos m,getVert_reverse,llen]
    exact getVert_take_local p j (j-1) (by omega)
  have qLast : q.getVert (q.length-1)=p.getVert (p.length-1) := by
    rw [len,show q=l.reverse.append (Walk.cons jump r) from rfl,getVert_append,length_reverse,llen,
      if_neg (by omega)]
    have e : p.length-1-j=(p.length-1-(j+1))+1 := by omega
    rw [e]
    change r.getVert (p.length-1-(j+1))=p.getVert (p.length-1)
    rw [show r=p.drop (j+1) from rfl,getVert_drop_local,show j+1+(p.length-1-(j+1))=p.length-1 by omega]
  exact ⟨q,⟨qpath,fun u v w hw=>len.symm ▸ hp.2 u v w hw⟩,
    fun z=>by simp [ps,qs],qLv,qLast⟩

#print axioms rotate_start_both_extreme_indices
end Graffiti189LongestPath.SixThreeNineteen

