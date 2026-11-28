import EJHubRoutes189

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
open private unliftCap from OreClosure189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem traceable_of_single_apex_switch (hc : G.Connected) {x y : V}
    (p : (cap G (fun _=>True)).Walk (some x) (some y))
    (hp : p.IsPath) (all : ∀ v,v∈p.support)
    (prefixMarks : ∀ i,i<(p.takeUntil none (all none)).length →
      (cap G (fun _=>True)).Adj (some x) (p.getVert (i+1)))
    (suffixMarks : ∀ i,(p.takeUntil none (all none)).length ≤ i → i<p.length →
      (cap G (fun _=>True)).Adj (some y) (p.getVert i)) :
    Traceable G := by
  classical
  let K := cap G (fun _=>True)
  let q := p.takeUntil none (all none)
  let r := p.dropUntil none (all none)
  have eq : q.append r=p := p.take_spec (all none)
  have nq : ¬q.reverse.Nil := by
    intro h
    exact Option.some_ne_none _ (Walk.Nil.eq h).symm
  have nr : ¬r.Nil := by
    intro h
    exact Option.some_ne_none _ (Walk.Nil.eq h).symm
  let L := q.reverse.tail.reverse
  let R := r.tail.reverse
  have LPath : L.IsPath := ((hp.takeUntil (all none)).reverse.tail).reverse
  have RPath : R.IsPath := ((hp.dropUntil (all none)).tail).reverse
  have leftSupport : q.support=L.support++[none] := by
    have seq := congrArg List.reverse (cons_support_tail q.reverse nq)
    simpa only [support_reverse,List.reverse_cons,List.reverse_reverse,L] using seq.symm
  have rightSupport : r.support=none::R.support.reverse := by
    have f := cons_support_tail r nr
    simpa only [R,support_reverse,List.reverse_reverse] using f.symm
  have supports : p.support=L.support++none::R.support.reverse := by
    simp only [←eq,support_append,leftSupport,rightSupport,List.tail_cons,List.append_assoc,
      List.singleton_append]
  have nd : (L.support++none::R.support.reverse).Nodup := supports ▸ hp.support_nodup
  have d := List.nodup_append.mp nd
  have lOff : none∉L.support := fun h=>d.2.2 h List.mem_cons_self
  have rOff : none∉R.support := fun h=>
    (List.nodup_cons.mp d.2.1).1 (List.mem_reverse.mpr h)
  obtain ⟨lt,_,l,ls⟩ := unliftCap L lOff
  obtain ⟨rt,_,w,ws⟩ := unliftCap R rOff
  have lp : l.IsPath := Walk.IsPath.mk' (List.Nodup.of_map _ (ls ▸ LPath.support_nodup))
  have wp : w.IsPath := Walk.IsPath.mk' (List.Nodup.of_map _ (ws ▸ RPath.support_nodup))
  have Lmem (v : V) (m : v∈l.support) : (some v : Option V)∈L.support :=
    ls.symm ▸ List.mem_map.mpr ⟨v,m,rfl⟩
  have Rmem (v : V) (m : v∈w.support) : (some v : Option V)∈R.support :=
    ws.symm ▸ List.mem_map.mpr ⟨v,m,rfl⟩
  have leftHub (v : V) (vl : v∈l.support) (vx : v≠x) : G.Adj x v := by
    have qm : (some v : Option V)∈q.support := leftSupport.symm ▸
      List.mem_append_left _ (Lmem v vl)
    obtain ⟨j,ji,jl⟩ := mem_support_iff_exists_getVert.mp qm
    have ne : j≠q.length := by
      intro e
      subst j
      simp at ji
    have j0 : j≠0 := by
      intro e
      have h : (some x : Option V)=some v := by simpa [e] using ji
      exact vx (Option.some.inj h).symm
    have idx : j-1+1=j := by omega
    have pval : p.getVert j=some v := (getVert_takeUntil (all none) jl).symm.trans ji
    have h := prefixMarks (j-1) (by change j-1<q.length; omega)
    rw [idx,pval] at h
    exact h
  have rightHub (v : V) (vr : v∈w.support) (vy : v≠y) : G.Adj y v := by
    have rm : (some v : Option V)∈r.support := rightSupport.symm ▸
      List.mem_cons_of_mem _ (List.mem_reverse.mpr (Rmem v vr))
    obtain ⟨j,ji,jl⟩ := mem_support_iff_exists_getVert.mp rm
    have ne : j≠r.length := by
      intro e
      have h : (some y : Option V)=some v := by simpa [e] using ji
      exact vy (Option.some.inj h).symm
    have pos : q.length+j<p.length := by have c := congrArg Walk.length eq; rw [length_append] at c; omega
    have pval : p.getVert (q.length+j)=some v := by
      rw [←eq,getVert_append]
      rw [if_neg (by omega : ¬q.length+j<q.length)]
      have h : q.length+j-q.length=j := by omega
      rwa [h]
    have h := suffixMarks (q.length+j) (by change q.length ≤ q.length+j; omega) pos
    rw [pval] at h
    exact h
  have dis : List.Disjoint l.support w.support := fun {v} vl vr=>
    d.2.2 (Lmem v vl) (List.mem_cons_of_mem _ (List.mem_reverse.mpr (Rmem v vr)))
  have both (v : V) : v∈l.support ∨ v∈w.support := by
    have m := all (some v)
    rw [supports,List.mem_append,List.mem_cons] at m
    rcases m with ml|bad|mr
    · obtain ⟨z,zm,e⟩ := List.mem_map.mp (ls ▸ ml)
      exact .inl (Option.some.inj e ▸ zm)
    · exact (Option.some_ne_none _ bad).elim
    obtain ⟨z,zm,e⟩ := List.mem_map.mp (ws ▸ List.mem_reverse.mp mr)
    exact .inr (Option.some.inj e ▸ zm)
  exact traceable_of_two_hub_paths hc l w lp wp leftHub rightHub dis both

#print axioms traceable_of_single_apex_switch
end Graffiti189Ore
