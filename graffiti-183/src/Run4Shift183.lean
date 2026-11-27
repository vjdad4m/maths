import DoubleShift183
import Run4Model183
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti183.Exceptional
open Finset SimpleGraph
set_option maxHeartbeats 3500000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def Run4At (G : SimpleGraph V) (f : Fin 7 ↪ V) (a : Fin 7) : Prop :=
  ∃ z ∉ indexSet f, ∀ i : Fin 7, G.Adj z (f (rot a i)) ↔ i.val ≤ 3

instance {m : ℕ} (i j : Fin m) : Decidable (CycleAdj i j) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

private def leftDel : Finset (Fin 7) := {6,0,1,2}
private def rightDel : Finset (Fin 7) := {1,2,3,4}

private def mask4 (i j k l : Fin 7) (a b c d : Bool) : Finset (Fin 7) :=
  (if a then {i} else ∅) ∪ (if b then {j} else ∅) ∪ (if c then {k} else ∅) ∪ (if d then {l} else ∅)

private lemma mask_of_subset (P : Finset (Fin 7)) (i j k l : Fin 7)
    (sub : P ⊆ {i,j,k,l}) :
    P = mask4 i j k l (decide (i ∈ P)) (decide (j ∈ P)) (decide (k ∈ P)) (decide (l ∈ P)) := by
  ext x
  have hxif (y : Fin 7) : x ∈ (if y ∈ P then ({y} : Finset (Fin 7)) else ∅) ↔ y ∈ P ∧ x = y := by
    by_cases h : y ∈ P <;> simp [h]
  simp only [mask4,Finset.mem_union,decide_eq_true_eq,hxif]
  constructor
  · intro hx
    have hp := sub hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [hx]
  · rintro (((⟨hi,rfl⟩ | ⟨hj,rfl⟩) | ⟨hk,rfl⟩) | ⟨hl,rfl⟩) <;> assumption

private lemma right_filter_static (a b c d : Bool) :
    let P := mask4 1 2 3 4 a b c d
    3 ≤ P.card → (∀ i ∈ P, ∃ j ∈ P, CycleAdj i j) →
    P = {1,2,3} ∨ (∀ i : Fin 7, i ∈ P ↔ (2 ≤ i.val ∧ i.val ≤ 4) ∨ (1 ∈ P ∧ i.val = 1)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private lemma left_filter_static (a b c d : Bool) :
    let P := mask4 6 0 1 2 a b c d
    3 ≤ P.card → (∀ i ∈ P, ∃ j ∈ P, CycleAdj i j) →
    P = {0,1,2} ∨ (∀ i : Fin 7, i ∈ P ↔ i.val = 6 ∨ i.val ≤ 1 ∨ (2 ∈ P ∧ i.val = 2)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

private lemma right_filter_model (P : Finset (Fin 7)) (sub : P ⊆ rightDel)
    (h3 : 3 ≤ P.card) (hn : ∀ i ∈ P, ∃ j ∈ P, CycleAdj i j) :
    P = {1,2,3} ∨ (∀ i : Fin 7, i ∈ P ↔ (2 ≤ i.val ∧ i.val ≤ 4) ∨ (1 ∈ P ∧ i.val = 1)) := by
  let a := decide (1 ∈ P)
  let b := decide (2 ∈ P)
  let c := decide (3 ∈ P)
  let d := decide (4 ∈ P)
  have hP : P = mask4 1 2 3 4 a b c d := mask_of_subset P 1 2 3 4 sub
  rw [hP] at h3 hn ⊢
  exact right_filter_static a b c d h3 hn

private lemma left_filter_model (P : Finset (Fin 7)) (sub : P ⊆ leftDel)
    (h3 : 3 ≤ P.card) (hn : ∀ i ∈ P, ∃ j ∈ P, CycleAdj i j) :
    P = {0,1,2} ∨ (∀ i : Fin 7, i ∈ P ↔ i.val = 6 ∨ i.val ≤ 1 ∨ (2 ∈ P ∧ i.val = 2)) := by
  let a := decide (6 ∈ P)
  let b := decide (0 ∈ P)
  let c := decide (1 ∈ P)
  let d := decide (2 ∈ P)
  have hP : P = mask4 6 0 1 2 a b c d := mask_of_subset P 6 0 1 2 sub
  rw [hP] at h3 hn ⊢
  exact left_filter_static a b c d h3 hn

lemma run4_shift_normal (f : Fin 7 ↪ V) (hc : ClawFree G)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hprof : ContactConditions G f) (hcore : NoSmallCore G 7)
    {v w : Fin 7} (hfar : 2 < G.dist (f v) (f w))
    (hmax : NoLargeMarked G (f v) (f w) 7)
    {z : V} (hz : z ∉ indexSet f) (hzr : ∀ i : Fin 7, G.Adj z (f i) ↔ i.val ≤ 3) :
    ∃ r ∉ indexSet f, ∀ i : Fin 7, G.Adj r (f i) ↔ 1 ≤ i.val ∧ i.val ≤ 4 := by
  have rEq : clipped f z rightDel = {z, f 0, f 6, f 5} := by
    ext x
    constructor
    · intro hx
      rcases clipped_member_cases hx with h | ⟨i,hi,he⟩
      · simp [h]
      · fin_cases i <;> simp_all [rightDel]
    · intro hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact clipped_root
      · exact clipped_index (by decide : (0 : Fin 7) ∉ rightDel)
      · exact clipped_index (by decide : (6 : Fin 7) ∉ rightDel)
      · exact clipped_index (by decide : (5 : Fin 7) ∉ rightDel)
  have lEq : clipped f z leftDel = {z, f 3, f 4, f 5} := by
    ext x
    constructor
    · intro hx
      rcases clipped_member_cases hx with h | ⟨i,hi,he⟩
      · simp [h]
      · fin_cases i <;> simp_all [leftDel]
    · intro hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact clipped_root
      · exact clipped_index (by decide : (3 : Fin 7) ∉ leftDel)
      · exact clipped_index (by decide : (4 : Fin 7) ∉ leftDel)
      · exact clipped_index (by decide : (5 : Fin 7) ∉ leftDel)
  have h45 : G.Adj (f 4) (f 5) := (hcyc _ _).mpr (by decide)
  have h65 : G.Adj (f 6) (f 5) := (hcyc _ _).mpr (by decide)
  have h34 : G.Adj (f 3) (f 4) := (hcyc _ _).mpr (by decide)
  have h06 : G.Adj (f 0) (f 6) := (hcyc _ _).mpr (by decide)
  have rcon : Graffiti177.Con G (clipped f z rightDel) := by
    rw [rEq]
    have h1 := Graffiti177.con_insert G (Graffiti177.con_single G (f 5)) (by simp) h65
    have h2 := Graffiti177.con_insert G h1 (by simp) h06
    exact Graffiti177.con_insert G h2 (by simp) ((hzr _).mpr (by decide : (0 : Fin 7).val ≤ 3))
  have lcon : Graffiti177.Con G (clipped f z leftDel) := by
    rw [lEq]
    have h1 := Graffiti177.con_insert G (Graffiti177.con_single G (f 5)) (by simp) h45
    have h2 := Graffiti177.con_insert G h1 (by simp) h34
    exact Graffiti177.con_insert G h2 (by simp) ((hzr _).mpr (by decide : (3 : Fin 7).val ≤ 3))
  have rco (i : Fin 7) : f i ∈ clipped f z rightDel ∨ Graffiti177.Dominates G (clipped f z rightDel) (f i) := by
    rw [rEq]
    fin_cases i
    · exact Or.inl (by simp)
    · exact Or.inr ⟨z,by simp,((hzr _).mpr (by decide : (1 : Fin 7).val ≤ 3)).symm⟩
    · exact Or.inr ⟨z,by simp,((hzr _).mpr (by decide : (2 : Fin 7).val ≤ 3)).symm⟩
    · exact Or.inr ⟨z,by simp,((hzr _).mpr (by decide : (3 : Fin 7).val ≤ 3)).symm⟩
    · exact Or.inr ⟨f 5,by simp,h45⟩
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
  have lco (i : Fin 7) : f i ∈ clipped f z leftDel ∨ Graffiti177.Dominates G (clipped f z leftDel) (f i) := by
    rw [lEq]
    fin_cases i
    · exact Or.inr ⟨z,by simp,((hzr _).mpr (by decide : (0 : Fin 7).val ≤ 3)).symm⟩
    · exact Or.inr ⟨z,by simp,((hzr _).mpr (by decide : (1 : Fin 7).val ≤ 3)).symm⟩
    · exact Or.inr ⟨z,by simp,((hzr _).mpr (by decide : (2 : Fin 7).val ≤ 3)).symm⟩
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inr ⟨f 5,by simp,h65⟩
  obtain ⟨r,hr,hrz,hrs⟩ := exists_clipped_contact (by decide) hcore hz rightDel (by decide) rcon rco
  obtain ⟨l,hl,hlz,hls⟩ := exists_clipped_contact (by decide) hcore hz leftDel (by decide) lcon lco
  have hrmodel := right_filter_model (contacts G f r) hrs (hprof.big r hr) (hprof.no_isolated r hr)
  have hlmodel := left_filter_model (contacts G f l) hls (hprof.big l hl) (hprof.no_isolated l hl)
  have rl (i : Fin 7) : G.Adj r (f i) ↔ (2 ≤ i.val ∧ i.val ≤ 4) ∨ (G.Adj r (f 1) ∧ i.val = 1) := by
    rcases hrmodel with he|he
    · have e3 : G.Adj r (f 3) := mem_contacts.mp (he.symm ▸ (by decide : (3 : Fin 7) ∈ ({1,2,3} : Finset _)))
      have e0 : G.Adj z (f 3) := (hzr _).mpr (by decide : (3 : Fin 7).val ≤ 3)
      have e4 : G.Adj (f 3) (f 4) := (hcyc _ _).mpr (by decide)
      have x4 : ¬G.Adj z (f 4) := fun h => (by decide : ¬(4 : Fin 7).val ≤ 3) ((hzr _).mp h)
      have y4 : ¬G.Adj r (f 4) := by
        rw [←mem_contacts,he]
        decide
      -- Distinctness follows from the different contacts at index 0.
      have nzr' : z ≠ r := by
        intro e
        subst r
        have hh : (0 : Fin 7) ∈ contacts G f z := mem_contacts.mpr ((hzr _).mpr (by decide : (0 : Fin 7).val ≤ 3))
        rw [he] at hh
        exact (by decide : (0 : Fin 7) ∉ ({1,2,3} : Finset _)) hh
      exact (y4 (hc e0.symm e3.symm e4 nzr' (fun h => hz (mem_indexSet.mpr ⟨4,h.symm⟩))
        (fun h => hr (mem_indexSet.mpr ⟨4,h.symm⟩)) (fun h => hrz h.symm) x4)).elim
    · simpa only [mem_contacts] using he i
  have ll (i : Fin 7) : G.Adj l (f i) ↔ i.val = 6 ∨ i.val ≤ 1 ∨ (G.Adj l (f 2) ∧ i.val = 2) := by
    rcases hlmodel with he|he
    · have e0 : G.Adj l (f 0) := mem_contacts.mp (he.symm ▸ (by decide : (0 : Fin 7) ∈ ({0,1,2} : Finset _)))
      have e0' : G.Adj z (f 0) := (hzr _).mpr (by decide : (0 : Fin 7).val ≤ 3)
      have e6 : G.Adj (f 0) (f 6) := (hcyc _ _).mpr (by decide)
      have x6 : ¬G.Adj z (f 6) := fun h => (by decide : ¬(6 : Fin 7).val ≤ 3) ((hzr _).mp h)
      have y6 : ¬G.Adj l (f 6) := by
        rw [←mem_contacts,he]
        decide
      have nzl : z ≠ l := by
        intro e
        subst l
        have hh : (3 : Fin 7) ∈ contacts G f z := mem_contacts.mpr ((hzr _).mpr (by decide : (3 : Fin 7).val ≤ 3))
        rw [he] at hh
        exact (by decide : (3 : Fin 7) ∉ ({0,1,2} : Finset _)) hh
      exact (y6 (hc e0'.symm e0.symm e6 nzl (fun h => hz (mem_indexSet.mpr ⟨6,h.symm⟩))
        (fun h => hl (mem_indexSet.mpr ⟨6,h.symm⟩)) (fun h => hlz h.symm) x6)).elim
    · simpa only [mem_contacts] using he i
  have zlr : z ≠ l ∧ z ≠ r := by
    constructor
    · intro e
      subst l
      have ee := (ll 6).mpr (Or.inl rfl)
      exact (by decide : ¬(6 : Fin 7).val ≤ 3) ((hzr _).mp ee)
    · intro e
      subst r
      have ee := (rl 4).mpr (Or.inl (by decide : 2≤(4:Fin 7).val ∧ (4:Fin 7).val≤4))
      exact (by decide : ¬(4 : Fin 7).val ≤ 3) ((hzr _).mp ee)
  have hlr : l ≠ r := by
    intro e
    subst r
    have hh := (ll 6).mpr (Or.inl rfl)
    have he := (rl 6).mp hh
    exact he.elim (fun h => (by decide : ¬ (6 : Fin 7).val ≤ 4) h.2)
      (fun h => (by decide : (6 : Fin 7).val ≠ 1) h.2)
  obtain ⟨F,model,withC⟩ := Graffiti183.ExampleRun4.attach_model f z l r hcyc hz hl hr
    zlr.1 zlr.2 hlr (fun h => hlz h.symm) (fun h => hrz h.symm) hzr ll rl
  have far : 2 < G.dist (F (Graffiti183.Run4Cert.cyc v)) (F (Graffiti183.Run4Cert.cyc w)) := by
    simpa only [withC] using hfar
  rcases Graffiti183.Run4Cert.lift G F (decide (G.Adj l (f 2))) (decide (G.Adj r (f 1)))
    (decide (G.Adj l r)) model hc v w far with ⟨_,hrup,_⟩ | ⟨p,hp,hv,hw⟩
  · have hR : G.Adj r (f 1) := of_decide_eq_true hrup
    refine ⟨r,hr,fun i => ?_⟩
    rw [rl i]
    simp only [hR,true_and]
    omega
  · exact (no_large_path hmax p (by decide) hp
      (by simpa only [withC] using hv) (by simpa only [withC] using hw)).elim

#print axioms run4_shift_normal

lemma run4_at_next (f : Fin 7 ↪ V) (hc : ClawFree G)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hprof : ContactConditions G f) (hcore : NoSmallCore G 7)
    {v w a : Fin 7} (hfar : 2 < G.dist (f v) (f w))
    (hmax : NoLargeMarked G (f v) (f w) 7) (h : Run4At G f a) :
    Run4At G f (rot a 1) := by
  let F := (rotEmb a).trans f
  have Fcyc (i j : Fin 7) : G.Adj (F i) (F j) ↔ CycleAdj i j :=
    (hcyc _ _).trans (cycleAdj_rotate (by decide) a i j)
  obtain ⟨z,hz,hzr⟩ := h
  have hz' : z ∉ indexSet F := by simpa only [F,indexSet_rot] using hz
  obtain ⟨i,hi⟩ := rot_surjective a v
  obtain ⟨j,hj⟩ := rot_surjective a w
  have vi : F i = f v := congrArg f hi
  have wj : F j = f w := congrArg f hj
  have hfar' : 2 < G.dist (F i) (F j) := by simpa only [vi,wj] using hfar
  have hmax' : NoLargeMarked G (F i) (F j) 7 := by simpa only [vi,wj] using hmax
  obtain ⟨r,hr,hhh⟩ := run4_shift_normal F hc Fcyc
    (contact_conditions_rotate (by decide) f hprof a) hcore hfar' hmax' hz' hzr
  refine ⟨r,by simpa only [F,indexSet_rot] using hr,?_⟩
  intro k
  rw [rot_assoc]
  change G.Adj r (F (rot 1 k)) ↔ _
  rw [hhh]
  fin_cases k <;> decide

theorem no_run_four_seven (f : Fin 7 ↪ V) (hc : ClawFree G)
    (hcyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (hprof : ContactConditions G f) (hcore : NoSmallCore G 7)
    {v w : Fin 7} (hfar : 2 < G.dist (f v) (f w))
    (hmax : NoLargeMarked G (f v) (f w) 7) :
    ∀ a : Fin 7, ¬ Run4At G f a := by
  intro a ha
  have allr (k : ℕ) (hk : k < 7) : Run4At G f (rot a ⟨k,hk⟩) := by
    induction k with
    | zero => simpa only [rot_zero a hk] using ha
    | succ k ih =>
      have hh : k<7 := by omega
      have e := run4_at_next f hc hcyc hprof hcore hfar hmax (ih hh)
      rw [rot_assoc] at e
      have ht : rot (⟨k,hh⟩ : Fin 7) 1 = ⟨k+1,hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)
      rwa [ht] at e
  have hAll (i : Fin 7) : Run4At G f i := by
    obtain ⟨k,hk⟩ := rot_surjective a i
    simpa only [hk] using allr k.val k.isLt
  obtain ⟨d,h3,h4,hd⟩ := separated_index_of_dist f hcyc (by decide) hfar
  have hD : d = 3 ∨ d = 4 := by
    have h0 : d.val = 3 ∨ d.val=4 := by omega
    exact h0.imp Fin.ext Fin.ext
  have notpair {z : V} (e : G.Adj z (f v)) (e' : G.Adj z (f w)) : False := by
    have ht : G.dist (f v) (f w) ≤ 2 := G.dist_le (Walk.cons e.symm e'.toWalk)
    omega
  have rot0 (q : Fin 7) : rot q 0 = q := rot_zero q (by decide)
  rcases hD with rfl | rfl
  · obtain ⟨z,_,hz⟩ := hAll v
    have e := (hz 0).mpr (by decide)
    have e' := (hz 3).mpr (by decide)
    rw [rot0] at e
    rw [hd] at e'
    exact notpair e e'
  · obtain ⟨z,_,hz⟩ := hAll w
    have eq : rot w 3 = v := by
      rw [←hd,rot_assoc]
      have h : rot (4 : Fin 7) 3 = 0 := by decide
      rw [h,rot0]
    have e := (hz 3).mpr (by decide)
    have e' := (hz 0).mpr (by decide)
    rw [eq] at e
    rw [rot0] at e'
    exact notpair e e'

#print axioms no_run_four_seven
end Graffiti183.Exceptional
