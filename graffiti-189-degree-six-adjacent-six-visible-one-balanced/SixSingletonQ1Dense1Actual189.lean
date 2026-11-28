import SixSingletonQ1Dense1Walk189
import SixSingletonQ1ActiveBits189
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

namespace Q1Dense1Actual

noncomputable def bits (J : Finset V) (f : Fin 6→V) (j : ℕ) : Bool :=
  if j<15 then Q1Pairs (G:=G) f j else
    if h : j-15<6 then q1Active (G:=G) J (f ⟨j-15,h⟩) else false

private theorem marks_le_one (p : Bool) : marks p≤1 := by cases p <;> decide

theorem run (F : SixVisibleData G D s) (P : Q1PortBoard D s 1)
    (n : Fintype.card V=16) (ab : G.Adj a b) (bal : nearBal D={z})
    (ea : (EA D).card=1) (eb : (EB D).card=2)
    (la : (strictA D).card=2) (rb : (strictB D).card=4)
    (k : 4≤(inside G (Dark D) z).card)
    (ordinary : ¬ Q1Dense1.Bad (bits (G:=G) (Dark D) (fun i : Fin 6=>P.label (widenQ1 (by decide : 6≤9) i))))
    : Traceable G := by
  classical
  let f (i : Fin 6) := P.label (widenQ1 (by decide : 6≤9) i)
  let J := Dark D
  let bts := bits (G:=G) J f
  let tag := P.label
  obtain ⟨ext,inj⟩ := q1_exterior_coverage F n P.label P.aEq P.bEq P.sEq P.portImage
  have fi : Function.Injective f := inj.comp (widenQ1_injective (by decide : 6≤9))
  obtain ⟨sc0,sc1,sc2,sc3,sc4,sc5⟩ := q1_port_scores (G:=G) f fi (Vis D) P.portImage
  have zD : z∈Dark D := by rw [←F.darkPart,bal]; simp
  have Jmax : (Dark D).erase z⊆J := erase_subset _ _
  have la' : (strictA D).Nonempty := card_pos.mp (by omega)
  have rb' : (strictB D).Nonempty := card_pos.mp (by omega)
  have ⟨⟨li,liL,liA⟩,⟨ri,riL,riR,riA⟩⟩ := q1_ports_active F bal P Jmax la' rb'
  have row0 : 2 ≤ (inside G (Vis D) (f 0)).card := by
    have h := six_q1_left_slots F bal (P.left 0 (by decide))
    change _ ≤ (inside G (Vis D) (f 0)).card+marks (decide (G.Adj (f 0) z)) at h
    have u := marks_le_one (decide (G.Adj (f 0) z))
    omega
  have inact0 (off : ¬ q1Active (G:=G) J (f 0)=true) : 5 ≤ (inside G (Vis D) (f 0)).card := by
    have no : ¬∃ w∈J,G.Adj (f 0) w := fun a=>off ((q1Active_iff _ _).mpr a)
    have h := q1_inactive_left F bal Jmax (P.left 0 (by decide)) no
    change _ ≤ (inside G (Vis D) (f 0)).card+marks (decide (G.Adj (f 0) z)) at h
    have bad : ¬G.Adj (f 0) z := fun e=>off ((q1Active_iff _ _).mpr ⟨z,zD,e⟩)
    simpa [marks,bad] using h
  have inact1 (off : ¬ q1Active (G:=G) J (f 1)=true) : 5 ≤ (inside G (Vis D) (f 1)).card := by
    have no : ¬∃ w∈J,G.Adj (f 1) w := fun a=>off ((q1Active_iff _ _).mpr a)
    have h := q1_inactive_right F bal Jmax (P.right 1 (by decide) (by decide)) no
    change _ ≤ (inside G (Vis D) (f 1)).card+marks (decide (G.Adj (f 1) z)) at h
    have bad : ¬G.Adj (f 1) z := fun e=>off ((q1Active_iff _ _).mpr ⟨z,zD,e⟩)
    simpa [marks,bad] using h
  have inact2 (off : ¬ q1Active (G:=G) J (f 2)=true) : 5 ≤ (inside G (Vis D) (f 2)).card := by
    have no : ¬∃ w∈J,G.Adj (f 2) w := fun a=>off ((q1Active_iff _ _).mpr a)
    have h := q1_inactive_right F bal Jmax (P.right 2 (by decide) (by decide)) no
    change _ ≤ (inside G (Vis D) (f 2)).card+marks (decide (G.Adj (f 2) z)) at h
    have bad : ¬G.Adj (f 2) z := fun e=>off ((q1Active_iff _ _).mpr ⟨z,zD,e⟩)
    simpa [marks,bad] using h
  have row3 : 3 ≤ (inside G (Vis D) (f 3)).card := by
    have h := six_q1_common_slots F bal (P.common 3 (by decide))
    change _ ≤ (inside G (Vis D) (f 3)).card+marks (decide (G.Adj (f 3) z)) at h
    have u := marks_le_one (decide (G.Adj (f 3) z))
    omega
  have inact3 (off : ¬ q1Active (G:=G) J (f 3)=true) : 4 ≤ (inside G (Vis D) (f 3)).card := by
    have h := six_q1_common_slots F bal (P.common 3 (by decide))
    change _ ≤ (inside G (Vis D) (f 3)).card+marks (decide (G.Adj (f 3) z)) at h
    have bad : ¬G.Adj (f 3) z := fun e=>off ((q1Active_iff _ _).mpr ⟨z,zD,e⟩)
    simpa [marks,bad] using h
  have row4 : 3 ≤ (inside G (Vis D) (f 4)).card := by
    have h := six_q1_common_slots F bal (P.common 4 (by decide))
    change _ ≤ (inside G (Vis D) (f 4)).card+marks (decide (G.Adj (f 4) z)) at h
    have u := marks_le_one (decide (G.Adj (f 4) z))
    omega
  have inact4 (off : ¬ q1Active (G:=G) J (f 4)=true) : 4 ≤ (inside G (Vis D) (f 4)).card := by
    have h := six_q1_common_slots F bal (P.common 4 (by decide))
    change _ ≤ (inside G (Vis D) (f 4)).card+marks (decide (G.Adj (f 4) z)) at h
    have bad : ¬G.Adj (f 4) z := fun e=>off ((q1Active_iff _ _).mpr ⟨z,zD,e⟩)
    simpa [marks,bad] using h
  have row5 : 3 ≤ (inside G (Vis D) (f 5)).card := by
    have h := six_q1_common_slots F bal (P.common 5 (by decide))
    change _ ≤ (inside G (Vis D) (f 5)).card+marks (decide (G.Adj (f 5) z)) at h
    have u := marks_le_one (decide (G.Adj (f 5) z))
    omega
  have inact5 (off : ¬ q1Active (G:=G) J (f 5)=true) : 4 ≤ (inside G (Vis D) (f 5)).card := by
    have h := six_q1_common_slots F bal (P.common 5 (by decide))
    change _ ≤ (inside G (Vis D) (f 5)).card+marks (decide (G.Adj (f 5) z)) at h
    have bad : ¬G.Adj (f 5) z := fun e=>off ((q1Active_iff _ _).mpr ⟨z,zD,e⟩)
    simpa [marks,bad] using h

  have model : Q1Dense1.Model bts := by
    constructor
    · exact sc0 ▸ row0
    · intro h
      exact sc0 ▸ inact0 h
    · intro h
      exact sc1 ▸ inact1 h
    · intro h
      exact sc2 ▸ inact2 h
    · exact sc3 ▸ row3
    · intro h
      exact sc3 ▸ inact3 h
    · exact sc4 ▸ row4
    · intro h
      exact sc4 ▸ inact4 h
    · exact sc5 ▸ row5
    · intro h
      exact sc5 ▸ inact5 h
    · fin_cases li
      · have h : bts 15=true := liA
        simp only [h,marks,if_true]
        omega
      · dsimp at liL; omega
      · dsimp at liL; omega
      · dsimp at liL; omega
      · dsimp at liL; omega
      · dsimp at liL; omega
    · fin_cases ri
      · dsimp at riL riR; omega
      · have h : bts 16=true := riA
        simp only [h,marks,if_true]
        omega
      · have h : bts 17=true := riA
        simp only [h,marks,if_true]
        omega
      · dsimp at riL riR; omega
      · dsimp at riL riR; omega
      · dsimp at riL riR; omega
  have base : ∀ u v,(u,v)∈Q1Dense1.fixed → G.Adj (tag u) (tag v) := by
    intro u v h
    simp only [Q1Dense1.fixed,List.mem_cons,List.not_mem_nil,or_false] at h
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
  have edge : ∀ i u v,Q1Dense1.ends i=some (u,v) → bts i.val=true → G.Adj (tag u) (tag v) := by
    intro i u v e ht
    fin_cases i
    all_goals simp [Q1Dense1.ends] at e
    all_goals rcases e with ⟨rfl,rfl⟩
    all_goals exact of_decide_eq_true ht
  obtain ⟨i,t,route,active⟩ := Q1Dense1.from_template tag inj base bts edge (Q1Dense1.has_template bts model ordinary)
  let ii := Q1Dense1.start i
  have q : ii.val<6 := Q1Dense1.start_port i
  let j : Fin 6 := ⟨ii.val,q⟩
  have eq : bts (15+ii.val)=q1Active (G:=G) J (f j) := by
    have b : ¬15+ii.val<15 := by omega
    have a : 15+ii.val-15=ii.val := by omega
    simp [bts,bits,b,a,q,j]
  change bts (15+ii.val)=true at active
  rw [eq] at active
  obtain ⟨w,wm,fw⟩ := (q1Active_iff _ _).mp active
  have til : tag ii = f j := by apply congrArg P.label; apply Fin.ext; rfl
  change RouteOn G (univ.image P.label) (tag ii) t at route
  rw [til,ext] at route
  exact six_q1_splice_dense F bal (by omega) (by omega) k wm fw.symm route

#print axioms run
end Q1Dense1Actual
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
