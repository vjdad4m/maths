import OffSix17CoreLift189

namespace Graffiti189LongestPath.TwoCut
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open private range_path_chain range_path_head offSix_walk_of_chain from OffSix17CoreLift189

private theorem range_path_last_17 {a b : V} (p : G.Walk a b) (s n : ℕ) (nn : 0<n) :
    ((List.range' s n).map p.getVert).getLast?=some (p.getVert (s+n-1)) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [List.range'_succ]
    | succ n =>
      rw [List.range'_succ,List.map_cons,List.getLast?_cons,ih (s+1) (by omega)]
      simp only [Option.getD_some]
      congr 2 <;> omega

/-- The usual forward replacement of the interval between two pins is
strictly longer when the omitted path has more vertices than the interval
it replaces. -/
theorem no_longest_with_forward_omitted_splice
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (q : G.Walk x y) (qp : q.IsPath)
    (off : ∀ z∈q.support,z∉p.support)
    {i j : ℕ} (lo : i<j) (hi : j ≤ p.length) (enough : j  ≤  i+q.length+1)
    (left : G.Adj x (p.getVert i)) (right : G.Adj y (p.getVert j)) : False := by
  classical
  let I := List.range' 0 (i+1)
  let J := List.range' j (p.length+1-j)
  let A := I.map p.getVert
  let B := J.map p.getVert
  have ir (k : ℕ) (im : k∈I) : k ≤ i ∧ k<j := by
    have q := List.mem_range'_1.mp im
    omega
  have jr (i : ℕ) (im : i∈J) : j ≤ i ∧ i ≤ p.length := by
    have q := List.mem_range'_1.mp im
    omega
  have ndA : A.Nodup := List.Nodup.map_on
    (fun u um v vm e => hp.1.getVert_injOn (show u ≤ p.length by have q := ir u um; omega)
      (show v ≤ p.length by have q := ir v vm; omega) e)
    (List.nodup_range' (s:=0) (n:=i+1))
  have ndB : B.Nodup := List.Nodup.map_on
    (fun u um v vm e => hp.1.getVert_injOn (jr u um).2 (jr v vm).2 e)
    (List.nodup_range' (s:=j) (n:=p.length+1-j))
  have ima (z : V) (zm : z∈A) : ∃ i∈I,p.getVert i=z := List.mem_map.mp zm
  have imb (z : V) (zm : z∈B) : ∃ i∈J,p.getVert i=z := List.mem_map.mp zm
  have onA {z : V} (zm : z∈A) : z∈p.support := by
    obtain ⟨i,_,rfl⟩ := ima z zm
    exact p.getVert_mem_support i
  have onB {z : V} (zm : z∈B) : z∈p.support := by
    obtain ⟨i,_,rfl⟩ := imb z zm
    exact p.getVert_mem_support i
  have ab : A.Disjoint B := by
    intro z zm zn
    obtain ⟨i,im,ie⟩ := ima _ zm
    obtain ⟨k,km,ke⟩ := imb _ zn
    have il := ir i im
    have kl := jr k km
    have e := hp.1.getVert_injOn (show i ≤ p.length by omega) kl.2 (ie.trans ke.symm)
    omega
  have da : A.Disjoint q.support := fun _ h r=>off _ r (onA h)
  have db : q.support.Disjoint B := fun _ h r=>off _ h (onB r)
  have nd : ((A++q.support)++B).Nodup := by
    refine (ndA.append qp.support_nodup da).append ndB ?_
    intro z zm zn
    exact (List.mem_append.mp zm).elim (fun h=>ab h zn) (fun h=>db h zn)
  have ca : List.Chain' G.Adj A := range_path_chain p 0 (i+1) (by omega)
  have cb : List.Chain' G.Adj B := range_path_chain p j (p.length+1-j) (by omega)
  have headA : A.getLast?=some (p.getVert i) := by
    simpa [A,I] using range_path_last_17 p 0 (i+1) (by omega)
  have headB : B.head?=some (p.getVert j) := range_path_head p j (p.length+1-j) (by omega)
  have ca' : List.Chain' G.Adj (A++q.support) := ca.append q.chain'_adj_support (by
    intro u um v vm
    have u1 : p.getVert i=u := by simpa [headA] using um
    have first : q.support.head?=some x := by cases q <;> rfl
    have r : x=v := by simpa [first] using vm
    subst u
    subst v
    exact left.symm)
  have last : (A++q.support).getLast?=some y := by
    rw [List.getLast?_append, List.getLast?_eq_getLast q.support_ne_nil]
    simp [q.getLast_support]
  have cl : List.Chain' G.Adj ((A++q.support)++B) := ca'.append cb (by
    intro u um v vm
    have q : y=u := by simpa [last] using um
    have r : p.getVert j=v := by simpa [headB] using vm
    subst u
    subst v
    exact right)
  let L := (A++q.support)++B
  have ln : L.length+j=p.length+i+q.length+3 := by simp [L,A,B,I,J,length_support]; omega
  change List.Chain' G.Adj L at cl
  cases e : L with
  | nil => simp [e] at ln; omega
  | cons r R =>
    obtain ⟨s,qqq,su⟩ := offSix_walk_of_chain r R (e ▸ cl)
    have qq : qqq.IsPath := IsPath.mk' (su.symm ▸ (e ▸ nd))
    have c := hp.2 _ _ qqq qq
    have d := congrArg List.length su
    rw [length_support,←e] at d
    omega



#print axioms no_longest_with_forward_omitted_splice
end Graffiti189LongestPath.TwoCut
