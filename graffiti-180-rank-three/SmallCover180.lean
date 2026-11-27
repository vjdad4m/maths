import Proof177
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- A family covering t more objects than the number of sets used has
a subfamily of at most t sets with the same surplus threshold. -/
theorem small_surplus (B : Finset V) (g : V→Finset W) (t : ℕ)
    (hit : t+B.card≤(B.biUnion g).card) :
    ∃ C⊆B,C.card≤t ∧ t+C.card≤(C.biUnion g).card := by
  classical
  let K := B.powerset.filter (fun C => t+C.card≤(C.biUnion g).card)
  have bk : B∈K := mem_filter.mpr ⟨mem_powerset.mpr (Subset.rfl),hit⟩
  obtain ⟨M,mk,mini⟩ := exists_min_image K card ⟨B,bk⟩
  obtain ⟨mb,paid⟩ := mem_filter.mp mk
  have sub := mem_powerset.mp mb
  by_cases done : M.card≤t
  · exact ⟨M,sub,done,paid⟩
  let U := M.biUnion g
  let priv (v : V) := U\((M.erase v).biUnion g)
  have inside {v : V} (x : W) (hx : x∈priv v) : x∈g v := by
    obtain ⟨hu,no⟩ := mem_sdiff.mp hx
    obtain ⟨y,ym,xy⟩ := mem_biUnion.mp hu
    by_cases same : y=v
    · exact same ▸ xy
    · exact (no (mem_biUnion.mpr ⟨y,mem_erase.mpr ⟨same,ym⟩,xy⟩)).elim
  have twice (v : V) (vm : v∈M) : 2≤(priv v).card := by
    have smaller := card_erase_add_one vm
    have notpaid : ¬t+(M.erase v).card≤((M.erase v).biUnion g).card := by
      intro yes
      have e : M.erase v∈K := mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset ..).trans sub),yes⟩
      have := mini _ e
      omega
    have inc : (M.erase v).biUnion g⊆U := by
      intro x hx
      obtain ⟨y,hy,xy⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨y,mem_of_mem_erase hy,xy⟩
    have count := card_sdiff_add_card_eq_card inc
    change (priv v).card+((M.erase v).biUnion g).card=(M.biUnion g).card at count
    omega
  obtain ⟨C,cm,ct⟩ := exists_subset_card_eq (s:=M) (show t≤M.card by omega)
  have dis : (↑C : Set V).PairwiseDisjoint priv := by
    intro u hu v hv ne
    apply disjoint_left.mpr
    intro x xu xv
    exact (mem_sdiff.mp xu).2 (mem_biUnion.mpr ⟨v,mem_erase.mpr ⟨ne.symm,cm hv⟩,inside x xv⟩)
  have bound : C.biUnion priv⊆C.biUnion g := by
    intro x hx
    obtain ⟨v,hv,z⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨v,hv,inside x z⟩
  have cc := card_le_card bound
  rw [card_biUnion dis] at cc
  have large : ∑ _v∈C, 2 ≤ ∑ v∈C, (priv v).card := sum_le_sum (fun v hv => twice v (cm hv))
  simp only [sum_const,smul_eq_mul] at large
  exact ⟨C,cm.trans sub,ct.le,by omega⟩

#print axioms small_surplus
end Minimal180.HigherRank
