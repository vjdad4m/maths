import OreClosure189
import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset Graffiti189Ore
open private unliftCap from OreClosure189
variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

private theorem cap_path_fragment {P : V→Prop} {b : Option V}
    (p : (cap J P).Walk none b) (hp : p.IsPath) :
    p.support=[none] ∨ ∃ x y, P x ∧ ∃ q : J.Walk x y,
      q.IsPath ∧ p.support=none::q.support.map some := by
  generalize h : (none : Option V)=a at p
  cases p with
  | nil => exact .inl (by simp [←h])
  | @cons a b c e p =>
    subst a
    cases b with
    | none => exact ((cap J P).loopless _ e).elim
    | some b =>
      have hnot : none∉p.support := (List.nodup_cons.mp hp.support_nodup).1
      obtain ⟨z,h,q,qs⟩ := unliftCap p hnot
      have pp : q.IsPath := by
        apply IsPath.mk'
        have orig := (List.nodup_cons.mp hp.support_nodup).2
        rw [qs] at orig
        exact orig.of_map _
      exact .inr ⟨b,z,e,q,pp,by simp [qs]⟩

/-- Delete the cap vertex of a spanning path. One obtains a rooted full
shore route, or two disjoint rooted routes whose union covers the shore. -/
theorem split_of_traceable_cap {P : V→Prop}
    (positive : Nonempty V) (h : Graffiti189Ore.Traceable (cap J P)) :
    (∃ x y,P x ∧ RouteOn J univ x y) ∨
    ∃ x y u v A B, P x ∧ P u ∧ x≠u ∧ Disjoint A B ∧ A∪B=univ ∧
      RouteOn J A x y ∧ RouteOn J B u v := by
  classical
  obtain ⟨e,f,p,hp,all⟩ := h
  let L := p.takeUntil none (all none)
  let R := p.dropUntil none (all none)
  have sp : p.support=L.support++R.support.tail := by
    rw [←support_append]
    exact congrArg Walk.support (take_spec p (all none)).symm
  have fragL := cap_path_fragment L.reverse (hp.takeUntil (all none)).reverse
  have fragR := cap_path_fragment R (hp.dropUntil (all none))
  have rev (l : List (Option V)) (eq : L.reverse.support=l) : L.support=l.reverse := by
    have z := congrArg List.reverse eq
    simpa using z
  rcases fragL with noL|⟨x,y,hx,q,qp,qs⟩ <;>
    rcases fragR with noR|⟨u,v,hu,r,rp,rs⟩
  · have e := rev _ noL
    rw [e,noR] at sp
    let ⟨z⟩ := positive
    have hz := all (.some z)
    simp [sp] at hz
  · have l := rev _ noL
    rw [l,rs] at sp
    apply Or.inl
    refine ⟨u,v,hu,r,rp,?_⟩
    intro z
    simp only [mem_univ,iff_true]
    have q := all (.some z)
    simpa [sp] using q
  · have l := rev _ qs
    rw [l,noR] at sp
    apply Or.inl
    refine ⟨x,y,hx,q,qp,?_⟩
    intro z
    simp only [mem_univ,iff_true]
    have h := all (.some z)
    simpa [sp] using h
  have l := rev _ qs
  rw [l,rs] at sp
  let A := q.support.toFinset
  let B := r.support.toFinset
  have apart : Disjoint A B := by
    apply disjoint_left.mpr
    intro z za zb
    have h := hp.support_nodup
    rw [sp,List.nodup_append] at h
    have zl : some z ∈ (none::q.support.map some).reverse := by
      have zq : z∈q.support := by simpa [A] using za
      simp [zq]
    have zr : some z ∈ (none::r.support.map some).tail := by
      have zp : z∈r.support := by simpa [B] using zb
      simp [zp]
    exact h.2.2 zl zr
  have cover : A∪B=univ := by
    ext z
    have h := all (.some z)
    simpa [sp,A,B] using h
  have xu : x≠u := fun e=>disjoint_left.mp apart
    (show x∈A by simp [A,q.start_mem_support])
    (show x∈B by rw [e]; simp [B,r.start_mem_support])
  exact .inr ⟨x,y,u,v,A,B,hx,hu,xu,apart,cover,
    ⟨q,qp,fun z=>by simp [A]⟩,⟨r,rp,fun z=>by simp [B]⟩⟩

#print axioms split_of_traceable_cap
end Graffiti189LongestPath.CrossSaturation
