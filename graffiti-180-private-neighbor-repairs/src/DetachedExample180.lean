import DetachedScore180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
namespace Minimal180.DetachedExample
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 PrivateCore

theorem fails : ∀ z∈(U\C).erase 0, ¬SingleWorks J C 3 0 z := by
  intro z hz
  apply (single_failure_iff J C 3 0 z (by decide) tip (mem_sdiff.mp (mem_of_mem_erase hz)).2 (mem_erase.mp hz).1).mpr
  right
  exact (show ∀ i∈(U\C).erase 0, ∃ q∈C.erase 3, ¬J.Adj q 3 ∧ J.Adj q i ∧ ∀ a∈S,J.Adj q a → a=i by decide) z hz

theorem unique_return (b : V) (bc : b∈C.erase 3) : PairWorks J C {1,2} 3 0 b ↔ b=6 := by
  have p : privateLeaves J C 3 1={7} := by
    ext q
    rw [private_iff,mem_singleton]
    exact (show ∀ a : V,(a∈C.erase 3 ∧ J.Adj a 1 ∧ ∀ i∈S,J.Adj a i → i=1) ↔ a=7 by decide) q
  have t : privateLeaves J C 3 2={8} := by
    ext q
    rw [private_iff,mem_singleton]
    exact (show ∀ a : V,(a∈C.erase 3 ∧ J.Adj a 2 ∧ ∀ i∈S,J.Adj a i → i=2) ↔ a=8 by decide) q
  have free : ({1,2}:Finset V)=(U\C).erase 0 := by decide
  have conn : Con J (S\{1,2}) :=
    Case14.con 0 (fun i => ([0,88,88,88,88,88,88,88,88,1,1,2,88,88]:List ℕ)[i.val]!) (by decide) (by decide)
  have safe (z : V) (hz : z∈({1,2}:Finset V)) : Con J (S.erase z) :=
    old_core_no_cut.2.2 z ((show ({1,2}:Finset V)⊆S by decide) hz)
  have count : C.card=weightedLeaves J U+1 := by rw [old_score]; decide
  have iff := detached_pair_iff J root_data.1.1 (by decide) U C 3 0 1 2 7 8 b (by decide) (by decide) count tip
    (by decide) safe (fun z hz => fails z (free ▸ hz)) p t conn (by unfold Dominates; decide)
    (by unfold Dominates; decide) bc
  apply iff.trans
  exact (show ∀ a∈C.erase 3,(¬J.Adj 3 a ∧ J.Adj a 7 ∧ J.Adj a 8 ∧ Dominates J (S\{1,2}) a) ↔ a=6 by
    unfold Dominates; decide) b bc

theorem first : FirstForm J U 3 0 4 := by
  have count : C.card=weightedLeaves J U+1 := by rw [old_score]; decide
  apply (second_split_iff J root_data.1.1 (by decide) 3 0 4 (by decide) (by decide) (by decide) (by decide)
    U C (by decide) count tip).mpr
  refine ⟨{6},by decide,{1,2},by decide,by decide,?_⟩
  simpa only [sdiff_singleton_eq_erase,PairWorks] using (unique_return 6 (by decide)).mpr rfl

/-- The sharpened attached-return conjecture already fails for a genuine
rooted eligible set, a horizontal triangle, rank increase on deletion, a
two-connected lower core and the exact second score. Lower equality fails. -/
theorem detached_obstruction :
    NoCut G ∧ (3≤S.card ∧ Con J S ∧ ∀ z∈S,Con J (S.erase z)) ∧
    J⊔SimpleGraph.edge 3 0=G ∧ ¬J.Adj 3 0 ∧ J.Adj 3 4 ∧ J.Adj 4 0 ∧
    Indep G A ∧ parity G 11 false=P ∧ eligible A P 11=U ∧ G.dist 3 11=G.dist 0 11 ∧
    bipartiteNum J=bipartiteNum G+1 ∧ weightedLeaves J U=7 ∧ C⊆U ∧
    C.card=weightedLeaves J U+1 ∧ NeedsTip J C S 3 0 ∧ J.degree 3=3 ∧ J.degree 0=5 ∧
    (U\C).erase 0={1,2} ∧ (∀ z∈(U\C).erase 0, ¬SingleWorks J C 3 0 z) ∧
    (∀ b∈C.erase 3, PairWorks J C {1,2} 3 0 b ↔ b=6) ∧
    ¬J.Adj 3 6 ∧ FirstForm J U 3 0 4 ∧
    weightedLeaves J U+bipartiteNum J=(1+A.card+P.card)+8 := by
  refine ⟨block,old_core_no_cut,add_eq,by decide,by decide,by decide,marks.1,marks.2.1,marks.2.2.1,
    marks.2.2.2.1,by rw [ranks.1,ranks.2],old_score,by decide,by rw [old_score]; decide,tip,by decide,
    by decide,by decide,fails,unique_return,by decide,first,?_⟩
  rw [old_score,ranks.1]
  decide

#print axioms fails
#print axioms unique_return
#print axioms first
#print axioms detached_obstruction
end Minimal180.DetachedExample
