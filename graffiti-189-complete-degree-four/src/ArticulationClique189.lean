import CutExtraction189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false

/-- The graph is complete on a specified set. -/
def CompleteOn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ u∈A,∀ v∈A,u≠v → G.Adj u v

private theorem clique_chain (A : Finset V) (clique : CompleteOn G A)
    (L : List V) (nd : L.Nodup) (mem : ∀ z∈L,z∈A) : List.Chain' G.Adj L := by
  have h : L.Pairwise G.Adj := by
    induction L with
    | nil => exact .nil
    | cons a t ih =>
      rw [List.pairwise_cons]
      have nt := List.nodup_cons.mp nd
      refine ⟨?_,ih nt.2 (fun z zt=>mem _ (List.mem_cons_of_mem _ zt))⟩
      intro z zt
      exact clique a (mem _ (by simp)) z (mem _ (by simp [zt]))
        (fun h=>nt.1 (h.symm ▸ zt))
  exact h.chain'

private theorem walk_of_chain (a : V) (L : List V)
    (cl : List.Chain' G.Adj (a::L)) : ∃ b,∃ q : G.Walk a b,q.support=a::L := by
  induction L generalizing a with
  | nil => exact ⟨a,.nil,rfl⟩
  | cons b L ih =>
    obtain ⟨c,q,eq⟩ := ih b cl.tail
    exact ⟨c,.cons cl.rel_head q,by simp [eq]⟩

theorem rooted_path_in_clique (A : Finset V) (clique : CompleteOn G A)
    {x : V} (xa : x∈A) :
    ∃ y,∃ q : G.Walk x y,q.IsPath ∧ ∀ v,v∈q.support ↔ v∈A := by
  classical
  let L := (A.erase x).toList
  have nd : (x::L).Nodup := by simp [L,(A.erase x).nodup_toList]
  have lm (v : V) : v∈x::L ↔ v∈A := by
    by_cases e : v=x <;> simp [L,e,xa]
  obtain ⟨y,q,ql⟩ := walk_of_chain x L
    (clique_chain A clique (x::L) nd (fun v hv=>(lm v).mp hv))
  exact ⟨y,q,(by rw [isPath_def,ql];exact nd),fun v=>by rw [ql,lm]⟩

theorem path_between_in_clique (A : Finset V) (clique : CompleteOn G A)
    {x y : V} (xa : x∈A) (ya : y∈A) (xy : x≠y) :
    ∃ q : G.Walk x y,q.IsPath ∧ ∀ v,v∈q.support ↔ v∈A := by
  classical
  let M := ((A.erase x).erase y).toList
  let L := M++[y]
  have ndM : M.Nodup := Finset.nodup_toList _
  have yM : y∉M := by simp [M]
  have xM : x∉M := by simp [M]
  have nd : (x::L).Nodup := by
    rw [List.nodup_cons]
    refine ⟨by simp [L,xM,xy],?_⟩
    rw [List.nodup_append]
    refine ⟨ndM,by simp,?_⟩
    intro u um uy
    have uy' : u=y := by simpa using uy
    exact yM (uy' ▸ um)
  have lm (v : V) : v∈x::L ↔ v∈A := by
    by_cases hx : v=x
    · simp [hx,xa]
    by_cases hy : v=y
    · simp [L,hy,ya]
    · simp [L,M,hx,hy]
  obtain ⟨z,q,ql⟩ := walk_of_chain x L
    (clique_chain A clique (x::L) nd (fun v hv=>(lm v).mp hv))
  have zy : z=y := by
    have last : q.support.getLast? = some z := by
      rw [List.getLast?_eq_getLast (by simp),q.getLast_support]
    rw [ql,show x::L=(x::M)++[y] by rfl,List.getLast?_concat] at last
    simpa using last.symm
  subst z
  exact ⟨q,(by rw [isPath_def,ql];exact nd),fun v=>by rw [ql,lm]⟩

theorem path_concat_new {x y z : V} (p : G.Walk x y) (pp : p.IsPath)
    (yz : G.Adj y z) (new : z∉p.support) : (p.concat yz).IsPath := by
  rw [isPath_def,support_concat,List.concat_eq_append,List.nodup_append]
  refine ⟨pp.support_nodup,by simp,?_⟩
  intro w wp wz
  have e : w=z := by simpa using wz
  exact new (e ▸ wp)

theorem rooted_path_of_clique_and_outlier (G : SimpleGraph V)
    {root z v : V} (rz : root≠z) (vz : v≠z) (rv : root≠v)
    (edge : G.Adj v z)
    (clique : CompleteOn G ((univ : Finset V).erase z)) :
    ∃ y,∃ p : G.Walk root y,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  let A := (univ : Finset V).erase z
  have rA : root∈A := mem_erase.mpr ⟨rz,mem_univ _⟩
  have vA : v∈A := mem_erase.mpr ⟨vz,mem_univ _⟩
  obtain ⟨p,pp,ps⟩ := path_between_in_clique A clique rA vA rv
  have fresh : z∉p.support := fun h=>by simpa [A] using (ps z).mp h
  refine ⟨z,p.concat edge,path_concat_new p pp edge fresh,?_⟩
  intro u
  by_cases uz : u=z
  · rw [uz]
    exact (p.concat edge).end_mem_support
  rw [support_concat,List.concat_eq_append]
  exact List.mem_append_left _ ((ps _).mpr (mem_erase.mpr ⟨uz,mem_univ _⟩))


/-- Build a full rooted path starting with an edge from the root into
a clique containing every other vertex. -/
theorem rooted_path_from_root_into_clique (G : SimpleGraph V)
    {root x : V} (edge : G.Adj root x)
    (clique : CompleteOn G ((univ : Finset V).erase root)) :
    ∃ y,∃ p : G.Walk root y,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  let A := (univ : Finset V).erase root
  obtain ⟨y,p,pp,ps⟩ := rooted_path_in_clique A clique (mem_erase.mpr ⟨edge.ne.symm,mem_univ _⟩)
  have fresh : root∉p.support := fun h=>by simpa [A] using (ps root).mp h
  refine ⟨y,.cons edge p,pp.cons fresh,?_⟩
  intro v
  by_cases h : v=root
  · simp [h]
  exact List.mem_cons_of_mem _ ((ps _).mpr (mem_erase.mpr ⟨h,mem_univ _⟩))

/-- When the exceptional vertex follows the root, it can enter the
completed clique at any one of its high neighbors. -/
theorem rooted_path_through_outlier_into_clique (G : SimpleGraph V)
    {root z x : V} (rz : G.Adj root z) (zx : G.Adj z x) (xr : x≠root)
    (clique : CompleteOn G (((univ : Finset V).erase root).erase z)) :
    ∃ y,∃ p : G.Walk root y,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  let A := ((univ : Finset V).erase root).erase z
  obtain ⟨y,p,pp,ps⟩ := rooted_path_in_clique A clique
    (mem_erase.mpr ⟨zx.ne.symm,mem_erase.mpr ⟨xr,mem_univ _⟩⟩)
  have fo : z∉p.support := fun h=>by simpa [A] using (ps z).mp h
  have fr : root∉p.support := fun h=>by simpa [A] using (ps root).mp h
  have rootOff : root∉(Walk.cons zx p).support := by
    simp [support_cons,rz.ne,fr]
  refine ⟨y,.cons rz (.cons zx p),(pp.cons fo).cons rootOff,?_⟩
  intro v
  by_cases vr : v=root
  · simp [vr]
  by_cases vz : v=z
  · simp [vz]
  simp only [support_cons,List.mem_cons]
  exact Or.inr (Or.inr ((ps _).mpr (mem_erase.mpr ⟨vz,mem_erase.mpr ⟨vr,mem_univ _⟩⟩)))

/-- The exceptional vertex can be last when there are distinct entry and
exit vertices available in the completed clique. -/
theorem rooted_path_from_clique_to_outlier (G : SimpleGraph V)
    {root z x y : V} (rx : G.Adj root x) (yz : G.Adj y z)
    (rz : root≠z) (xz : x≠z) (yr : y≠root) (xy : x≠y)
    (clique : CompleteOn G (((univ : Finset V).erase root).erase z)) :
    ∃ o,∃ q : G.Walk root o,q.IsPath ∧ ∀ u,u∈q.support := by
  classical
  let A := ((univ : Finset V).erase root).erase z
  have xa : x∈A := mem_erase.mpr ⟨xz,mem_erase.mpr ⟨rx.ne.symm,mem_univ _⟩⟩
  have ya : y∈A := mem_erase.mpr ⟨yz.ne,mem_erase.mpr ⟨yr,mem_univ _⟩⟩
  obtain ⟨p,pp,ps⟩ := path_between_in_clique A clique xa ya xy
  have fz : z∉p.support := fun h=>by simpa [A] using (ps z).mp h
  have fr : root∉p.support := fun h=>by simpa [A] using (ps root).mp h
  have rootOff : root∉(p.concat yz).support := by
    simp [support_concat,rz,fr]
  refine ⟨z,.cons rx (p.concat yz),(path_concat_new p pp yz fz).cons rootOff,?_⟩
  intro v
  by_cases vr : v=root
  · simp [vr]
  by_cases vz : v=z
  · simp [vz,support_concat]
  simp only [support_cons,support_concat,List.concat_eq_append,List.mem_cons,List.mem_append]
  exact Or.inr (Or.inl ((ps _).mpr (mem_erase.mpr ⟨vz,mem_erase.mpr ⟨vr,mem_univ _⟩⟩)))

#print axioms rooted_path_from_root_into_clique
#print axioms rooted_path_through_outlier_into_clique
#print axioms rooted_path_from_clique_to_outlier
#print axioms rooted_path_in_clique
#print axioms path_between_in_clique
#print axioms rooted_path_of_clique_and_outlier
end Graffiti189LongestPath.CrossSaturation
