import OreClosure189
import ArticulationClique189
import ArticulationClosure189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset Graffiti189Ore
open private unliftCap liftCap_support leaf_cap_neighbor leaf_cap_degree_ge from OreClosure189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem cap_path_known_end {x y : V}
    (p : (cap G (fun v=>v=y)).Walk (some x) none)
    (pp : p.IsPath) (all : ∀ v,v∈p.support) :
    ∃ q : G.Walk x y, q.IsPath ∧ ∀ v,v∈q.support := by
  have qa : ∀ v,v∈p.reverse.support := by simpa only [support_reverse,List.mem_reverse] using all
  generalize e : p.reverse = r at qa ⊢
  have rp : r.IsPath := e ▸ pp.reverse
  cases r with
  | cons h q =>
    have na := leaf_cap_neighbor h
    subst_vars
    have no := ((cons_isPath_iff h q).mp rp).2
    obtain ⟨z,zz,t,ts⟩ := unliftCap q no
    have zx := Option.some.inj zz.symm
    subst z
    have tp : t.IsPath := IsPath.mk' (List.Nodup.of_map some
        (ts ▸ ((cons_isPath_iff h q).mp rp).1.support_nodup))
    refine ⟨t.reverse,tp.reverse,?_⟩
    intro v
    have vm := qa (some v)
    simp only [support_cons,List.mem_cons,reduceCtorEq,false_or,ts,List.mem_map] at vm
    obtain ⟨w,wm,eq⟩ := vm
    have ve : v∈t.support := Option.some.inj eq ▸ wm
    simpa only [support_reverse,List.mem_reverse] using ve

private theorem cap_path_forces_end {x y : V}
    (h : Graffiti189Ore.Rooted (cap G (fun v=>v=y)) (some x)) :
    ∃ q : G.Walk x y,q.IsPath ∧ ∀ v,v∈q.support := by
  obtain ⟨b,p,pp,all⟩ := h
  obtain ⟨i,e,hi⟩ := mem_support_iff_exists_getVert.mp (all none)
  have positive : 0 < i := by
    by_contra bad
    have i0 : i=0 := by omega
    simp [i0] at e
  have last : i=p.length := by
    apply Classical.byContradiction
    intro no
    have near : i < p.length := by omega
    have ep := p.adj_getVert_succ (i:=i-1) (by omega)
    have en := p.adj_getVert_succ near
    rw [show i-1+1=i by omega,e] at ep
    rw [e] at en
    have eq := (leaf_cap_neighbor ep.symm).trans (leaf_cap_neighbor en).symm
    have bad := pp.getVert_injOn (by simp; omega : i-1∈{j | j≤p.length})
      (by simp; omega : i+1∈{j | j≤p.length}) eq
    omega
  have ben : b=none := by simpa [last] using e
  subst b
  exact cap_path_known_end p pp all

/-- The two-terminal Ore condition, derived from rooted closure by attaching
a pendant leaf at the prescribed last vertex. -/
theorem hamilton_connected_of_ore
    (deg : ∀ u v : V,u≠v → ¬ G.Adj u v → Fintype.card V+1≤G.degree u+G.degree v)
    {x y : V} (xy : x≠y) : ∃ q : G.Walk x y,q.IsPath ∧ ∀ v,v∈q.support := by
  classical
  let H := completeWith G (univ : Finset V)
  let P (v : V) := v=y
  have hm : cap G P ≤ cap H P := by
    intro i j e
    cases i <;> cases j <;> try exact e
    exact completeWith_mono G univ e
  have hw : Graffiti189Ore.Rooted (cap H P) (some x) := by
    obtain ⟨p,pp,ps⟩ := path_between_in_clique univ (completeWith_of_mem G univ)
      (mem_univ x) (mem_univ y) xy
    let q := p.map (liftCap H P)
    have qp : q.IsPath := IsPath.mk'
      (liftCap_support p ▸ pp.support_nodup.map (liftCap_injective H P))
    have off : (none : Option V)∉q.support := by
      change (none : Option V)∉(p.map (liftCap H P)).support
      rw [liftCap_support]
      simp
    let e : (cap H P).Adj (some y) none := rfl
    refine ⟨none,q.concat e,path_concat_new q qp e off,?_⟩
    intro z
    cases z with
    | none => exact (q.concat e).end_mem_support
    | some v =>
      rw [support_concat,List.concat_eq_append]
      exact List.mem_append_left _ (liftCap_support p ▸ List.mem_map.mpr ⟨v,(ps v).mpr (mem_univ _),rfl⟩)
  apply cap_path_forces_end
  apply Graffiti189Ore.rooted_closure hm (some x) _ hw
  intro i j hij no
  cases i <;> cases j
  · exact (no hij).elim
  · exact (no hij).elim
  · exact (no hij).elim
  rename_i u v
  have uv : ¬G.Adj u v := no
  have ne : u≠v := fun e=>hij.ne (congrArg some e)
  have b := deg u v ne uv
  have zu := leaf_cap_degree_ge (G:=G) y u
  have zv := leaf_cap_degree_ge (G:=G) y v
  change G.degree u≤(cap G P).degree (some u) at zu
  change G.degree v≤(cap G P).degree (some v) at zv
  rw [Fintype.card_option]
  omega

#print axioms hamilton_connected_of_ore
end Graffiti189LongestPath.CrossSaturation
