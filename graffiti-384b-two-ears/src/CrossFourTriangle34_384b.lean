import LowSample384b

namespace Graffiti384b.CrossFour34
open Finset SimpleGraph LowSample
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def triangleFreeOn (W : Finset V) : Prop := ∀ w∈W,∀ x∈W,∀ j∈W,G.Adj w x → G.Adj w j → ¬G.Adj x j

/-- If a misses the other pair, any anchor triangle consists of b and
the whole other pair. -/
theorem triangle_covers {e z a b : V} (ears : twos G={e,z})
    (ear : G.neighborFinset e={a,b}) (dz : G.degree z=2)
    (sep : Disjoint (G.neighborFinset e) (G.neighborFinset z)) (ab : G.Adj a b)
    (miss : ∀ j∈G.neighborFinset z,¬G.Adj a j)
    (non : ¬triangleFreeOn G ((twos G).biUnion (G.neighborFinset ·))) :
    ∀ j∈G.neighborFinset z,G.Adj b j := by
  classical
  let W := (twos G).biUnion (G.neighborFinset ·)
  have eq : W=({a,b} : Finset V)∪G.neighborFinset z := by simp [W,ears,ear]
  change ¬∀ i∈W,∀ j∈W,∀ k∈W,G.Adj i j → G.Adj i k → ¬G.Adj j k at non
  push_neg at non
  obtain ⟨i,iw,j,jw,k,kw,ij,ik,jk⟩ := non
  let T : Finset V := {i,j,k}
  have tw : T⊆W := insert_subset iw (insert_subset jw (singleton_subset_iff.mpr kw))
  have tc : T.card=3 := by simp [T,ij.ne,ik.ne,jk.ne]
  have cl (u : V) (um : u∈T) (v : V) (vm : v∈T) (uv : u≠v) : G.Adj u v := by
    simp only [T,mem_insert,mem_singleton] at um vm
    rcases um with rfl|rfl|rfl <;> rcases vm with rv|rv|rv <;> subst_vars <;>
      first | exact (uv rfl).elim | assumption | apply Adj.symm; assumption
  have only (v : V) (vw : v∈W) (av : G.Adj a v) : v=b := by
    rw [eq,mem_union,mem_insert,mem_singleton] at vw
    exact vw.elim (fun p => p.resolve_left av.ne.symm) (fun m => (miss v m av).elim)
  have out : a∉T := by
    intro am
    have sub : T⊆{a,b} := by
      intro u um; by_cases ua : u=a
      · exact mem_insert.mpr (Or.inl ua)
      · exact mem_insert_of_mem (mem_singleton.mpr (only u (tw um) (cl a am u um (Ne.symm ua))))
    have le := card_le_card sub
    rw [card_pair ab.ne,tc] at le; omega
  have sub : T⊆insert b (G.neighborFinset z) := by
    intro v vm
    have vw := tw vm
    rw [eq,mem_union,mem_insert,mem_singleton] at vw
    exact vw.elim (fun p => mem_insert.mpr (Or.inl (p.resolve_left (fun va => out (va ▸ vm))))) mem_insert_of_mem
  have bc : b∉G.neighborFinset z := fun bm => disjoint_left.mp sep (ear ▸ mem_insert_of_mem (mem_singleton_self _)) bm
  have all := eq_of_subset_of_card_le sub (by rw [card_insert_of_not_mem bc,card_neighborFinset_eq_degree,dz,tc])
  intro v vz
  exact cl b (all ▸ mem_insert_self ..) v (all ▸ mem_insert_of_mem vz) (fun bv => bc (bv ▸ vz))

end Graffiti384b.CrossFour34
#print axioms Graffiti384b.CrossFour34.triangle_covers

