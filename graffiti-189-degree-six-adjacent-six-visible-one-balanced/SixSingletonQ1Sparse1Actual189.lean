import SixSingletonQ1Sparse1Walk189
import SixSingletonQ1PortBoard189
import SixSingletonQ1Splice189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair Graffiti189Ore PortCertificates
open private Cmp from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common strictA strictB from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s z : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
set_option maxRecDepth 8192

namespace Q1Sparse1Actual

def bits (f : Fin 6→V) (z : V) (j : ℕ) : Bool :=
  if j<15 then Q1Pairs (G:=G) f j else
    if h : j-15<6 then decide (G.Adj (f ⟨j-15,h⟩) z) else false

theorem run (F : SixVisibleData G D s) (P : Q1PortBoard D s 1)
    (n : Fintype.card V=16) (ab : G.Adj a b) (bal : nearBal D={z})
    (ea : (EA D).card=1) (eb : (EB D).card=2)
    (la : (strictA D).card=2) (rb : (strictB D).card=4)
    (low : (inside G (Dark D) z).card≤3)
    {w : V} (core : w∈(Dark D).erase z) (wz : G.Adj w z)
    (ordinary : ¬ Q1Sparse1.Bad (bits (G:=G) (fun i : Fin 6=>P.label (widenQ1 (by decide : 6≤9) i)) z))
    : Traceable G := by
  classical
  let f (i : Fin 6) := P.label (widenQ1 (by decide : 6≤9) i)
  let bts := bits (G:=G) f z
  let tag := addQ1 P.label z
  obtain ⟨ext,inj⟩ := q1_exterior_coverage F n P.label P.aEq P.bEq P.sEq P.portImage
  obtain ⟨ext10,inj10⟩ := q1_exterior_add_balance F bal P.label ext inj
  have fi : Function.Injective f := inj.comp (widenQ1_injective (by decide : 6≤9))
  obtain ⟨sc0,sc1,sc2,sc3,sc4,sc5⟩ := q1_port_scores (G:=G) f fi (Vis D) P.portImage
  have bz := six_q1_balance_port_slots F bal
  have zs := q1_z_score (G:=G) f fi (Vis D) P.portImage z
  have h0 := six_q1_left_slots F bal (P.left 0 (by decide))
  have h1 := six_q1_right_slots F bal (P.right 1 (by decide) (by decide))
  have h2 := six_q1_right_slots F bal (P.right 2 (by decide) (by decide))
  have h3 := six_q1_common_slots F bal (P.common 3 (by decide))
  have h4 := six_q1_common_slots F bal (P.common 4 (by decide))
  have h5 := six_q1_common_slots F bal (P.common 5 (by decide))
  change _ ≤ (inside G (Vis D) (f 0)).card + marks (decide (G.Adj (f 0) z)) at h0
  change _ ≤ (inside G (Vis D) (f 1)).card + marks (decide (G.Adj (f 1) z)) at h1
  change _ ≤ (inside G (Vis D) (f 2)).card + marks (decide (G.Adj (f 2) z)) at h2
  change _ ≤ (inside G (Vis D) (f 3)).card + marks (decide (G.Adj (f 3) z)) at h3
  change _ ≤ (inside G (Vis D) (f 4)).card + marks (decide (G.Adj (f 4) z)) at h4
  change _ ≤ (inside G (Vis D) (f 5)).card + marks (decide (G.Adj (f 5) z)) at h5
  have model : Q1Sparse1.Model bts := by
    rw [sc0] at h0; rw [sc1] at h1; rw [sc2] at h2
    rw [sc3] at h3; rw [sc4] at h4; rw [sc5] at h5
    rw [zs] at bz
    constructor
    all_goals dsimp [bts,bits]
    all_goals omega
  have base : ∀ u v,(u,v)∈Q1Sparse1.fixed → G.Adj (tag u) (tag v) := by
    intro u v h
    simp only [Q1Sparse1.fixed,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h|h|h|h|h|h|h|h
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 6) (P.label 7)
      simpa only [P.aEq,P.bEq,P.sEq] using ab
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 6) (P.label 8)
      simpa only [P.aEq,P.bEq,P.sEq] using F.sa.symm
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 7) (P.label 8)
      simpa only [P.aEq,P.bEq,P.sEq] using F.sb.symm
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 6) (P.label 0)
      simpa only [P.aEq,P.bEq,P.sEq] using (F.eA _ (P.left 0 (by decide))).1
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 6) (P.label 3)
      simpa only [P.aEq,P.bEq,P.sEq] using (F.common _ (P.common 3 (by decide))).1
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 6) (P.label 4)
      simpa only [P.aEq,P.bEq,P.sEq] using (F.common _ (P.common 4 (by decide))).1
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 6) (P.label 5)
      simpa only [P.aEq,P.bEq,P.sEq] using (F.common _ (P.common 5 (by decide))).1
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 7) (P.label 1)
      simpa only [P.aEq,P.bEq,P.sEq] using (F.eB _ (P.right 1 (by decide) (by decide))).1
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 7) (P.label 2)
      simpa only [P.aEq,P.bEq,P.sEq] using (F.eB _ (P.right 2 (by decide) (by decide))).1
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 7) (P.label 3)
      simpa only [P.aEq,P.bEq,P.sEq] using (F.common _ (P.common 3 (by decide))).2
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 7) (P.label 4)
      simpa only [P.aEq,P.bEq,P.sEq] using (F.common _ (P.common 4 (by decide))).2
    · rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      change G.Adj (P.label 7) (P.label 5)
      simpa only [P.aEq,P.bEq,P.sEq] using (F.common _ (P.common 5 (by decide))).2
  have edge : ∀ k u v,Q1Sparse1.ends k=some (u,v) → bts k.val=true → G.Adj (tag u) (tag v) := by
    intro k u v eq ht
    fin_cases k
    all_goals simp [Q1Sparse1.ends] at eq
    all_goals rcases eq with ⟨rfl,rfl⟩
    all_goals exact of_decide_eq_true ht
  obtain ⟨i,t,route⟩ := Q1Sparse1.from_template tag inj10 base bts edge (Q1Sparse1.has_template bts model ordinary)
  have startEq : tag (Q1Sparse1.start i)=z := rfl
  rw [startEq] at route
  change RouteOn G (univ.image (addQ1 P.label z)) z t at route
  rw [ext10] at route
  exact six_q1_splice_core F bal (by omega) (by omega) core wz route

#print axioms run
end Q1Sparse1Actual
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
