import FanWeighted189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.FanRoutable
open scoped BigOperators
set_option warningAsError true
namespace Graffiti189LongestPath.DefectiveFanPorts

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem walk_hits_boundary (A B : Finset V)
    (closed : ∀ u∈A,∀ v∉A,G.Adj u v → v∈B) {u v : V} (w : G.Walk u v)
    (ua : u∈A) (va : v∉A) : ∃ x∈B,x∈w.support := by
  induction w with
  | nil => exact (va ua).elim
  | @cons a b c e q ih =>
    by_cases hb : b∈A
    · obtain ⟨x,xb,xq⟩ := ih hb va
      exact ⟨x,xb,List.mem_cons_of_mem _ xq⟩
    · exact ⟨b,closed a ua b hb e,List.mem_cons_of_mem _ q.start_mem_support⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every vertex of an exact cut is used by the disjoint hooks. Each
off-path cut port is charged to a distinct hook of positive length. -/
theorem defective_off_path_ports_le_total_hook_length (A B : Finset V) (k : Nat)
    (bc : B.card≤k+1) (ab : Disjoint A B)
    (closed : ∀ u∈A,∀ v∉A,G.Adj u v → v∈B)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (F : HookFamily p A k)
    (off : ∀ z∈A,z∉p.support) :
    (B\p.support.toFinset).card≤(∑ i : Fin k,(F.path i).length)+1 := by
  classical
  let dst (i : Fin k) := p.getVert (F.idx i)
  have dstP (i : Fin k) : dst i∈p.support := p.getVert_mem_support _
  let q (i : Fin k) := (F.path i).append (.cons (F.adjLast i) .nil)
  have term (i : Fin k) :
      ∃ z∈B,z∈(F.path i).support ∨ z=dst i := by
    obtain ⟨z,zb,hz⟩ := walk_hits_boundary A B closed (q i) (F.firstIn i)
      (fun za => off (dst i) za (dstP i))
    refine ⟨z,zb,?_⟩
    have f : z∈(F.path i).support ∨ z=F.last i ∨ z=dst i := by
      simpa [q,dst] using hz
    rcases f with s|eq|eq
    · exact Or.inl s
    · exact Or.inl (eq.symm ▸ (F.path i).end_mem_support)
    · exact Or.inr eq
  choose port pb wherePort using term
  have pinj : Function.Injective port := by
    intro i j e
    apply Classical.byContradiction
    intro ne
    rcases wherePort i with si|hi
    · rcases wherePort j with sj|hj
      · exact F.disj ne si (e.symm ▸ sj)
      · exact F.off i _ si (e.symm ▸ (hj.symm ▸ dstP j))
    · rcases wherePort j with sj|hj
      · exact F.off j _ sj (e ▸ (hi.symm ▸ dstP i))
      · exact ne (F.idx.injective
          (hp.1.getVert_injOn (Nat.le_of_lt (F.idxLt i)) (Nat.le_of_lt (F.idxLt j))
            (hi.symm.trans (e.trans hj))))
  let E : Fin k ↪ V := ⟨port,pinj⟩
  let I := (univ : Finset (Fin k)).map E
  have sub : I⊆B := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := mem_map.mp hz
    exact pb i
  have size : I.card=k := by simp [I]
  have comp : (B\I).card≤1 := by
    have c := card_sdiff_add_card_eq_card sub
    omega
  let T := (univ : Finset (Fin k)).filter (fun i => port i∉p.support)
  have sdiff_eq : T.map E=I\p.support.toFinset := by
    ext z
    simp [I,T,E,mem_map,mem_sdiff,List.mem_toFinset]
    aesop
  have covering : B\p.support.toFinset⊆(I\p.support.toFinset)∪(B\I) := by
    intro z hz
    obtain ⟨zb,zp⟩ := mem_sdiff.mp hz
    by_cases zi : z∈I
    · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨zi,zp⟩))
    · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨zb,zi⟩))
  have each (i : Fin k) (hi : i∈T) : 1≤(F.path i).length := by
    have no := (mem_filter.mp hi).2
    rcases wherePort i with si|hj
    · have ne : port i≠F.root i := fun eq =>
        disjoint_left.mp ab (F.firstIn i) (eq ▸ pb i)
      apply Classical.byContradiction
      intro h
      obtain ⟨n,eq,le⟩ := mem_support_iff_exists_getVert.mp si
      have zero : n=0 := by omega
      rw [zero,getVert_zero] at eq
      exact ne eq.symm
    · exact (no (hj.symm ▸ dstP i)).elim
  have cv := (card_le_card covering).trans (card_union_le _ _)
  rw [←sdiff_eq,card_map] at cv
  have t : T.card≤∑ i : Fin k,(F.path i).length := by
    calc
      T.card = ∑ i∈T,(1:Nat) := by simp
      _ ≤ ∑ i∈T,(F.path i).length := sum_le_sum each
      _ ≤ ∑ i : Fin k,(F.path i).length := sum_le_sum_of_subset (subset_univ _)
  omega

#print axioms defective_off_path_ports_le_total_hook_length
end Graffiti189LongestPath.DefectiveFanPorts
