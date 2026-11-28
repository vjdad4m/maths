import SixSingletonFiveTinyTailCert189
import SixSingletonFiveThreeNonadjacentTinyCore189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair PortCertificates
open private cmBits hitBits cm_repr hit_repr hit_counts perm_four_left perm_four_right from SixSingletonFivePairPlans189
open private cTag_mem kTag cTag_inj finite_plan sepKD from SixSingletonFivePairGeometry189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

private theorem tiny_two_common {L R S : Finset V} {T : V} (F : ProfileThree G L R S T)
    {z : V} (zD : z∈D) (low : (inside G D z).card≤2) :
    2≤(inside G K z).card := by
  have sub : G.neighborFinset z⊆inside G D z∪inside G P z := by
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
  omega

private theorem three_common_model (noniso : ∀ c∈K,∃ w∈K,G.Adj c w) :
    (cmBits G 0 1=true ∨ cmBits G 0 2=true) ∧
    (cmBits G 0 1=true ∨ cmBits G 1 2=true) ∧
    (cmBits G 0 2=true ∨ cmBits G 1 2=true) := by
  have shape : ∀ u∈K,u=5 ∨ u=6 ∨ u=7 := by decide
  obtain ⟨u,um,eu⟩ := noniso 5 (by decide)
  obtain ⟨v,vm,ev⟩ := noniso 6 (by decide)
  obtain ⟨w,wm,ew⟩ := noniso 7 (by decide)
  refine ⟨?_,?_,?_⟩
  · rcases shape u um with q|q|q
    · exact (eu.ne q.symm).elim
    · exact .inl (decide_eq_true (show G.Adj 5 6 from q ▸ eu))
    exact .inr (decide_eq_true (show G.Adj 5 7 from q ▸ eu))
  · rcases shape v vm with q|q|q
    · exact .inl (decide_eq_true (show G.Adj 5 6 from q ▸ ev.symm))
    · exact (ev.ne q.symm).elim
    exact .inr (decide_eq_true (show G.Adj 6 7 from q ▸ ev))
  rcases shape w wm with q|q|q
  · exact .inl (decide_eq_true (show G.Adj 5 7 from q ▸ ew.symm))
  · exact .inr (decide_eq_true (show G.Adj 6 7 from q ▸ ew.symm))
  exact (ew.ne q.symm).elim

theorem tiny_common_route {L R S : Finset V} {T z w : V} (F : ProfileThree G L R S T)
    (hc : G.Connected) (even : ∀ u,(EvenFrom G u).card≤7)
    (zD : z∈D) (wD : w∈D) (zl : (inside G D z).card≤2) (wl : (inside G D w).card≤2) :
    ∃ c∈K,∃ t∈K,G.Adj z c ∧ RouteOn G (insert w K) c t := by
  classical
  have nz := tiny_two_common F zD zl
  have nw := tiny_two_common F wD wl
  rw [hit_counts] at nz nw
  have shape := three_common_model (common_three_balances_nonisolated F hc even)
  have h := tiny_common_exit_certificate (cmBits G 0 1) (cmBits G 0 2) (cmBits G 1 2)
    (hitBits G z 0) (hitBits G z 1) (hitBits G z 2)
    (hitBits G w 0) (hitBits G w 1) (hitBits G w 2)
  rw [cm_repr,hit_repr,hit_repr] at h
  obtain ⟨i,j,k,ord,iz,sol⟩ := h shape nz nw
  have mk := finite_plan i j k ord
  have wK : w∉K := fun h=>disjoint_left.mp sepKD h wD
  have wi : w≠cTag i := fun e=>wK (e.symm ▸ cTag_mem i)
  have wk : w≠cTag k := fun e=>wK (e.symm ▸ cTag_mem k)
  have ik : cTag i≠cTag k := fun e=>ord.2.1 (cTag_inj e)
  refine ⟨cTag i,cTag_mem i,?_⟩
  rcases sol with ⟨iw,jw,jk⟩|⟨ij,jw,kw⟩
  · have p := RouteOn.three (show G.Adj (cTag i) w from of_decide_eq_true iw)
      (show G.Adj (cTag j) w from of_decide_eq_true jw).symm (fun e=>ord.1 (cTag_inj e))
    have off : cTag k∉({cTag i,w,cTag j}:Finset V) := by
      intro hm
      rcases mem_insert.mp hm with e|e
      · exact ik.symm e
      rcases mem_insert.mp e with e|e
      · exact wk.symm e
      exact ord.2.2 (cTag_inj (mem_singleton.mp e).symm)
    have p := p.suffix (show G.Adj (cTag j) (cTag k) from of_decide_eq_true jk) off
    have set : insert (cTag k) ({cTag i,w,cTag j}:Finset V)=insert w K :=
      (perm_four_left (cTag i) (cTag j) (cTag k) w).trans (congrArg (insert w) mk)
    rw [set] at p
    exact ⟨_,cTag_mem k,(show G.Adj (cTag i) z from of_decide_eq_true iz).symm,p⟩
  · have p := RouteOn.three (show G.Adj (cTag i) (cTag j) from of_decide_eq_true ij)
      (show G.Adj (cTag j) w from of_decide_eq_true jw) wi.symm
    have off : cTag k∉({cTag i,cTag j,w}:Finset V) := by
      intro hm
      rcases mem_insert.mp hm with e|e
      · exact ik.symm e
      rcases mem_insert.mp e with e|e
      · exact ord.2.2 (cTag_inj e.symm)
      exact wk.symm (mem_singleton.mp e)
    have p := p.suffix (show G.Adj (cTag k) w from of_decide_eq_true kw).symm off
    have set : insert (cTag k) ({cTag i,cTag j,w}:Finset V)=insert w K :=
      (perm_four_right (cTag i) (cTag j) (cTag k) w).trans (congrArg (insert w) mk)
    rw [set] at p
    exact ⟨_,cTag_mem k,(show G.Adj (cTag i) z from of_decide_eq_true iz).symm,p⟩

#print axioms tiny_common_route
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
