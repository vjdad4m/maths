import SixSingletonFiveTwoDeepLowGeom189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair PortCertificates
open private cTag_mem kTag cTag_inj finite_plan sepKD triple_score 
  from SixSingletonFivePairGeometry189
open private actual_deep_pair_model deep_low_common_counts from SixSingletonFiveTwoDeepLowGeom189
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

private def cmBits (G : SimpleGraph V) [DecidableRel G.Adj] (i j : Fin 3) :=
  decide (G.Adj (cTag i) (cTag j))
private def hitBits (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) (i : Fin 3) :=
  decide (G.Adj (cTag i) z)

private theorem cm_repr :
    rows33 (cmBits G 0 1) (cmBits G 0 2) (cmBits G 1 2)=cmBits G := by
  have cs (u v : Fin 3) : decide (G.Adj (cTag u) (cTag v))=decide (G.Adj (cTag v) (cTag u)) := by
    congr 1
    exact propext ⟨Adj.symm,Adj.symm⟩
  have cn (u : Fin 3) : decide (G.Adj (cTag u) (cTag u))=false := decide_eq_false_iff_not.mpr (G.loopless _)
  funext i j
  fin_cases i <;> fin_cases j
  · exact (cn _).symm
  · rfl
  · rfl
  · exact cs _ _
  · exact (cn _).symm
  · rfl
  · exact cs _ _
  · exact cs _ _
  · exact (cn _).symm

private theorem hit_repr (z : V) :
    row3 (hitBits G z 0) (hitBits G z 1) (hitBits G z 2)=hitBits G z := by
  funext i
  fin_cases i <;> rfl

private theorem hit_counts (z : V) :
    (inside G K z).card=marks (hitBits G z 0)+marks (hitBits G z 1)+marks (hitBits G z 2) := by
  have symm (u : V) : decide (G.Adj z u)=decide (G.Adj u z) := by
    congr 1
    exact propext ⟨Adj.symm,Adj.symm⟩
  rw [triple_score,symm 5,symm 6,symm 7]
  rfl

private theorem some_hit (z : V) (n : 1≤(inside G K z).card) :
    hitBits G z 0=true ∨ hitBits G z 1=true ∨ hitBits G z 2=true := by
  by_contra no
  push_neg at no
  have eq v : v≠true → v=false := by cases v <;> simp
  rw [hit_counts,eq _ no.1,eq _ no.2.1,eq _ no.2.2] at n
  simp [marks] at n

theorem deep_early_common_plan {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
    {z w : V} (zW : z∈D\S) (wW : w∈D\S) (zw : z≠w)
    (low : (inside G D z).card≤3) (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤7) :
    ∃ c∈K,∃ t∈K,RouteOn G K c t ∧ G.Adj z c := by
  have model := actual_deep_pair_model F zW wW zw hc even low
  have nz := (deep_low_common_counts F (mem_sdiff.mp zW).1 low).1
  have h := common_early_certificate (cmBits G 0 1) (cmBits G 0 2) (cmBits G 1 2)
    (hitBits G z 0) (hitBits G z 1) (hitBits G z 2)
    (hitBits G w 0) (hitBits G w 1) (hitBits G w 2)
  rw [cm_repr,hit_repr,hit_repr] at h
  obtain ⟨i,j,k,ord,iz,ij,jk⟩ := h model (some_hit z nz)
  have p := RouteOn.three (show G.Adj (cTag i) (cTag j) from of_decide_eq_true ij)
    (show G.Adj (cTag j) (cTag k) from of_decide_eq_true jk) (fun e=>ord.2.1 (cTag_inj e))
  rw [finite_plan i j k ord] at p
  exact ⟨cTag i,cTag_mem i,cTag k,cTag_mem k,p,(show G.Adj (cTag i) z from of_decide_eq_true iz).symm⟩

private theorem perm_four_left (i j k w : V) :
    insert k ({i,w,j}:Finset V)=insert w ({i,j,k}:Finset V) := by
  ext u
  simp only [mem_insert,mem_singleton]
  tauto

private theorem perm_four_right (i j k w : V) :
    insert k ({i,j,w}:Finset V)=insert w ({i,j,k}:Finset V) := by
  ext u
  simp only [mem_insert,mem_singleton]
  tauto

/-- When the two low balances are nonadjacent, the second can be covered in
the common-port tail instead of requiring a second prescribed dark endpoint. -/
theorem deep_interleaved_common_plan {L R S : Finset V} {T : V} (F : ProfileTwoDeep G L R S T)
    {z w u : V} (zW : z∈D\S) (wW : w∈D\S) (zw : z≠w) (hu : u=x ∨ u=y)
    (zl : (inside G D z).card≤3) (wl : (inside G D w).card≤3)
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤7) :
    ∃ c∈K, G.Adj z c ∧
      ((∃ t∈K,RouteOn G (insert w K) c t) ∨ (RouteOn G (insert w K) c w ∧ G.Adj w u)) := by
  classical
  have model := actual_deep_pair_model F zW wW zw hc even zl
  have nz := (deep_low_common_counts F (mem_sdiff.mp zW).1 zl).1
  have nw := deep_low_common_counts F (mem_sdiff.mp wW).1 wl
  have req : 2≤(inside G K w).card ∨ G.Adj w u := by
    by_cases h : G.Adj w u
    · exact .inr h
    left
    rcases hu with rfl|rfl
    · exact nw.2.1 h
    exact nw.2.2 h
  have wK : w∉K := fun h=>disjoint_left.mp sepKD h (mem_sdiff.mp wW).1
  let flag := decide (G.Adj w u)
  have h := common_finish_certificate (cmBits G 0 1) (cmBits G 0 2) (cmBits G 1 2)
    (hitBits G z 0) (hitBits G z 1) (hitBits G z 2)
    (hitBits G w 0) (hitBits G w 1) (hitBits G w 2) flag
  rw [cm_repr,hit_repr,hit_repr] at h
  have m := nw.1
  rw [hit_counts] at m req
  have rn : 2≤marks (hitBits G w 0)+marks (hitBits G w 1)+marks (hitBits G w 2) ∨ flag=true :=
    req.imp id decide_eq_true
  obtain ⟨i,j,k,ord,iz,sol⟩ := h model (some_hit z nz) m rn
  have mk := finite_plan i j k ord
  have wi : w≠cTag i := fun e=>wK (e.symm ▸ cTag_mem i)
  have wj : w≠cTag j := fun e=>wK (e.symm ▸ cTag_mem j)
  have wk : w≠cTag k := fun e=>wK (e.symm ▸ cTag_mem k)
  have ik : cTag i≠cTag k := fun e=>ord.2.1 (cTag_inj e)
  refine ⟨cTag i,cTag_mem i,(show G.Adj (cTag i) z from of_decide_eq_true iz).symm,?_⟩
  rcases sol with ⟨ij,jk,kw,wu⟩|⟨iw,jw,jk⟩|⟨ij,jw,kw⟩
  · have p := RouteOn.three (show G.Adj (cTag i) (cTag j) from of_decide_eq_true ij)
      (show G.Adj (cTag j) (cTag k) from of_decide_eq_true jk) ik
    rw [mk] at p
    exact .inr ⟨p.suffix (of_decide_eq_true kw) wK,of_decide_eq_true wu⟩
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
    exact .inl ⟨_,cTag_mem k,p⟩
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
    exact .inl ⟨_,cTag_mem k,p⟩

#print axioms deep_early_common_plan
#print axioms deep_interleaved_common_plan
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.SingletonFive16
