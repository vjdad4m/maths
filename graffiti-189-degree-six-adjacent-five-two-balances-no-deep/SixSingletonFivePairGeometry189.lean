import SixSingletonFiveOneLow189
import SixSingletonFivePortPairCert189
import SixSingletonPortScore189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair PortCertificates
open private d8 k3 p5 from SixSingletonFiveShallowRoute189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

def cTag (i : Fin 3) : V := ![5,6,7] i
private theorem cTag_mem : ∀ i,cTag i∈K := by decide
private theorem kTag : ∀ v∈K,∃ i,cTag i=v := by decide
private theorem cTag_inj : Function.Injective cTag := by decide
private theorem finite_plan : ∀ i j k : Fin 3,ThreeOrder i j k →
    ({cTag i,cTag j,cTag k}:Finset V)=K := by decide
private theorem sepKD : Disjoint K D := by decide

private theorem triple_score (u : V) :
    (inside G K u).card=marks (decide (G.Adj u 5))+marks (decide (G.Adj u 6))+marks (decide (G.Adj u 7)) := by
  have a := inside_insert_score (G:=G) (P:=({6,7}:Finset V)) (x:=5) (c:=u) (by decide)
  have b := inside_insert_score (G:=G) (P:=({7}:Finset V)) (x:=6) (c:=u) (by decide)
  have c := inside_insert_score (G:=G) (P:=(∅:Finset V)) (x:=7) (c:=u) (by decide)
  rw [show insert (7:V) (∅:Finset V)=({(7:V)}:Finset V) by decide] at c
  have zero : (inside G (∅:Finset V) u).card=0 := by simp [inside]
  rw [zero] at c
  change (inside G K u).card=_ at a
  rw [b,c] at a
  omega

private theorem board_two {L R S : Finset V} (F : ProfileTwo G L R S)
    {z w : V} (zW : z∈D\S) (wW : w∈D\S) (zw : z≠w) : D\S={z,w} := by
  have h : ({z,w}:Finset V)⊆D\S := insert_subset zW (singleton_subset_iff.mpr wW)
  exact (eq_of_subset_of_card_le h (by rw [F.balance,card_insert_of_not_mem (by simpa using zw),card_singleton])).symm

private theorem actual_pair_model {L R S : Finset V} (F : ProfileTwo G L R S)
    {z w : V} (zW : z∈D\S) (wW : w∈D\S) (zw : z≠w)
    (noBoth : ∀ c∈K,¬(G.Adj c x ∧ G.Adj c y)) :
    CommonPairModel (fun i j=>decide (G.Adj (cTag i) (cTag j)))
      (fun i=>decide (G.Adj (cTag i) z)) (fun i=>decide (G.Adj (cTag i) w)) := by
  classical
  have same := board_two F zW wW zw
  have zK : z∉K := fun zK=>disjoint_left.mp sepKD zK (mem_sdiff.mp zW).1
  have wK : w∉K := fun wK=>disjoint_left.mp sepKD wK (mem_sdiff.mp wW).1
  intro i
  let c := cTag i
  let t := if G.Adj c x then x else y
  let U := insert z (insert w K)
  have cm : c∈K := cTag_mem i
  have sub : G.neighborFinset c⊆insert a (insert b (insert t (inside G U c))) := by
    intro v vm
    have e := (mem_neighborFinset _ _ _).mp vm
    rcases mem_insert.mp (F.commonBounds c cm v e) with h|h
    · exact mem_insert.mpr (.inl h)
    rcases mem_insert.mp h with h|h
    · exact mem_insert_of_mem (mem_insert.mpr (.inl h))
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    rcases mem_union.mp h with p|p
    · rcases mem_insert.mp p with p|p
      · exact mem_insert.mpr (.inl (p.trans (if_pos (p ▸ e)).symm))
      rcases mem_insert.mp p with p|p
      · have nx : ¬G.Adj c x := fun xx=>noBoth c cm ⟨xx,p ▸ e⟩
        exact mem_insert.mpr (.inl (p.trans (if_neg nx).symm))
      exact mem_insert_of_mem (mem_filter.mpr ⟨mem_insert_of_mem (mem_insert_of_mem p),e⟩)
    rw [same] at p
    rcases mem_insert.mp p with p|p
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_insert.mpr (.inl p),e⟩)
    exact mem_insert_of_mem (mem_filter.mpr ⟨mem_insert_of_mem (mem_insert.mpr (.inl (mem_singleton.mp p))),e⟩)
  have h := card_le_card sub
  rw [card_neighborFinset_eq_degree] at h
  have m := F.commonHigh c cm
  have ha := card_insert_le a (insert b (insert t (inside G U c)))
  have hb := card_insert_le b (insert t (inside G U c))
  have ht := card_insert_le t (inside G U c)
  have hc : 3≤(inside G U c).card := by omega
  have hZ := inside_insert_score (G:=G) (P:=insert w K) (x:=z) (c:=c) (by simp [zw,zK])
  have hW := inside_insert_score (G:=G) (P:=K) (x:=w) (c:=c) wK
  change 3≤(inside G (insert z (insert w K)) c).card at hc
  rw [hZ,hW,triple_score] at hc
  change 3≤marks (decide (G.Adj c 5))+marks (decide (G.Adj c 6))+marks (decide (G.Adj c 7))+
      marks (decide (G.Adj c z))+marks (decide (G.Adj c w))
  omega

private theorem low_common_counts {L R S : Finset V} (F : ProfileTwo G L R S)
    {z : V} (zD : z∈D) (low : (inside G D z).card≤3) :
    1≤(inside G K z).card ∧
      (¬G.Adj z x → 2≤(inside G K z).card) ∧ (¬G.Adj z y → 2≤(inside G K z).card) := by
  have sub : G.neighborFinset z⊆(inside G D z)∪(inside G P z) := by
    intro u um
    have j := (mem_neighborFinset _ _ _).mp um
    exact (mem_union.mp (F.darkBounds z zD u j)).elim
      (fun m=>mem_union_left _ (mem_filter.mpr ⟨m,j⟩))
      (fun m=>mem_union_right _ (mem_filter.mpr ⟨m,j⟩))
  have k := card_le_card sub
  rw [card_neighborFinset_eq_degree] at k
  have p := card_union_le (inside G D z) (inside G P z)
  have q := F.darkHigh z zD
  have mx := inside_insert_score (G:=G) (P:=insert y K) (x:=x) (c:=z) (by decide)
  have my := inside_insert_score (G:=G) (P:=K) (x:=y) (c:=z) (by decide)
  change (inside G P z).card=_ at mx
  rw [my] at mx
  have mark_le (j : Bool) : marks j≤1 := by cases j <;> decide
  have a := mark_le (decide (G.Adj z x))
  have b := mark_le (decide (G.Adj z y))
  refine ⟨by omega,?_,?_⟩
  · intro nx
    have zero : marks (decide (G.Adj z x))=0 := by simp [nx,marks]
    rw [zero] at mx
    omega
  · intro ny
    have zero : marks (decide (G.Adj z y))=0 := by simp [ny,marks]
    rw [zero] at mx
    omega

#print axioms actual_pair_model
#print axioms low_common_counts
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
