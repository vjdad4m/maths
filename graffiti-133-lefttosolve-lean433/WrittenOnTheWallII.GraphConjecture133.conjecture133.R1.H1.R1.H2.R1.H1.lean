import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

section OMA133_Partial133

namespace Graffiti133

open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
def FourCycleFree (G : SimpleGraph V) : Prop :=
  ∀ a b x y, a ≠ b → G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → x = y

variable [Fintype V]

open scoped BigOperators

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
noncomputable def localIndependentSets (G : SimpleGraph V) (v : V) : Finset (Finset V) := by
  classical
  exact ((Finset.univ.filter (G.Adj v)).powerset.filter
    (fun A => ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
noncomputable def localIndependence (G : SimpleGraph V) (v : V) : ℕ :=
  (localIndependentSets G v).sup Finset.card

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
noncomputable def averageLocal (G : SimpleGraph V) : ℚ :=
  (∑ v, (localIndependence G v : ℚ)) / Fintype.card V

open Finset

universe u

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
def InducedPath {W : Type*} (H : SimpleGraph W) {k : ℕ} (f : Fin k → W) : Prop :=
  Function.Injective f ∧
    ∀ i j : Fin k, i < j → (H.Adj (f i) (f j) ↔ (i : ℕ) + 1 = j)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
omit [Fintype V] in
theorem fourCycleFree_iff (G : SimpleGraph V) :
    FourCycleFree G ↔ ¬ ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
      b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a := by
  constructor
  · rintro h ⟨a,b,c,d,_,hac,_,_,hbd,_,hab,hbc,hcd,hda⟩
    exact hbd (h a c b d hac hab hbc.symm hda.symm hcd)
  · intro h a c b d hac hab hcb had hcd
    by_contra hbd
    exact h ⟨a,b,c,d,hab.ne,hac,had.ne,hcb.ne.symm,hbd,hcd.ne,hab,hcb.symm,hcd,had.symm⟩

section Bipartite

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
omit [Fintype V] in

private theorem oma133_Partial133_prepend_induced_with_positions {k : ℕ} (hk : 0 < k) {f : Fin k → V}
    (hf : InducedPath G f) (w : V) (hnew : ∀ i, w ≠ f i)
    (h₀ : G.Adj w (f ⟨0,hk⟩)) (h₁ : ∀ i : Fin k, 0 < i.val → ¬ G.Adj w (f i)) :
    ∃ ff : Fin (k+1) → V, InducedPath G ff ∧ ff ⟨0,by omega⟩ = w ∧
      ∀ i : Fin (k+1), ∀ hi : 0 < i.val, ff i = f ⟨i.val-1,by have := i.isLt; omega⟩ := by
  let F (i : Fin (k+1)) : V :=
    if h : i.val = 0 then w else f ⟨i.val-1,by omega⟩
  have head (i : Fin (k+1)) (hi : i.val = 0) : F i = w := dif_pos hi
  have tail (i : Fin (k+1)) (hi : i.val ≠ 0) :
      F i = f ⟨i.val-1,by have := i.isLt; omega⟩ := dif_neg hi
  refine ⟨F,⟨?_,?_⟩,head _ rfl, fun i hi => tail i (by omega)⟩
  · intro i j h
    apply Fin.ext
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · omega
    · rw [head _ hi,tail _ hj] at h
      exact (hnew _ h).elim
    · rw [tail _ hi,head _ hj] at h
      exact (hnew _ h.symm).elim
    · rw [tail _ hi,tail _ hj] at h
      have hh := congrArg Fin.val (hf.1 h)
      change i.val-1 = j.val-1 at hh
      omega
  · intro i j hij
    change i.val < j.val at hij
    have hji := j.isLt
    have hj : j.val ≠ 0 := by omega
    rw [tail _ hj]
    by_cases hi : i.val = 0
    · rw [head _ hi]
      by_cases h : j.val = 1
      · have hindex : (⟨j.val-1,by omega⟩ : Fin k) = ⟨0,hk⟩ :=
          Fin.ext (by change j.val-1=0; omega)
        rw [hindex]
        exact iff_of_true h₀ (by omega)
      · exact iff_of_false (h₁ _ (by change 0 < j.val-1; omega)) (by omega)
    · rw [tail _ hi,hf.2 _ _ (by change i.val-1 < j.val-1; omega)]
      change (i.val-1+1 = j.val-1) ↔ (i.val+1 = j.val)
      omega

end Bipartite

section Density

end Density

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
def NoSimpleFive133 (G : SimpleGraph V) : Prop :=
  ∀ a b c d e, [a,b,c,d,e].Nodup →
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e a → False

end Graffiti133

end OMA133_Partial133

section OMA133_PentagonRead133

namespace Graffiti133Pentagon
open SimpleGraph Graffiti133 Finset
open scoped BigOperators

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
def pent (i j : Fin 5) : Prop := i + 1 = j ∨ j + 1 = i
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private instance : DecidableRel pent := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private lemma oma133_PentagonRead133_pent_alt : ∀ i j : Fin 5, i ≠ j → ¬pent i j →
    ∃ a b, a ≠ j ∧ b ≠ i ∧ pent i a ∧ pent a b ∧ pent b j := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private def oma133_PentagonRead133_reserved (b : Fin 5 → Bool) (i j : Fin 6) : Prop :=
  if hi : i.val < 5 then
    if hj : j.val < 5 then pent ⟨i.val,hi⟩ ⟨j.val,hj⟩
    else b ⟨i.val,hi⟩ = true
  else if hj : j.val < 5 then b ⟨j.val,hj⟩ = true else False
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private instance (b : Fin 5 → Bool) : DecidableRel (oma133_PentagonRead133_reserved b) := by
  intro i j
  unfold oma133_PentagonRead133_reserved
  split <;> split <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private def oma133_PentagonRead133_spokePath (i : Fin 5) (positive : Bool) : Fin 5 → Fin 6 :=
  ![5, i.castSucc, (i + (if positive then 1 else 4)).castSucc,
    (i + (if positive then 2 else 3)).castSucc, (i + (if positive then 3 else 2)).castSucc]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private lemma oma133_PentagonRead133_computed_spokePath : ∀ b : Fin 5 → Bool,
    (∀ i, b i = true → b (i+2) = false) → (∃ i, b i = true) →
    ∃ i pos,
      (∀ u v : Fin 5, oma133_PentagonRead133_spokePath i pos u = oma133_PentagonRead133_spokePath i pos v → u = v) ∧
      ∀ u v : Fin 5, u < v → (oma133_PentagonRead133_reserved b (oma133_PentagonRead133_spokePath i pos u) (oma133_PentagonRead133_spokePath i pos v) ↔
        u.val + 1 = v.val) := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
theorem cycle_pentagon (h4 : FourCycleFree G) {c : Fin 5 → V}
    (inj : Function.Injective c) (sides : ∀ i, G.Adj (c i) (c (i+1))) :
    ∀ i j, G.Adj (c i) (c j) ↔ pent i j := by
  have forward (i j : Fin 5) (h : pent i j) : G.Adj (c i) (c j) := by
    rcases h with e | e
    · exact e ▸ sides i
    · exact e ▸ (sides j).symm
  intro i j
  refine ⟨?_,forward i j⟩
  intro e
  apply Classical.byContradiction
  intro no
  obtain ⟨a,b,ha,hb,e1,e2,e3⟩ := oma133_PentagonRead133_pent_alt i j (fun h => e.ne (congrArg c h)) no
  have eq := h4 (c i) (c b) (c a) (c j) (fun h => hb (inj h).symm)
    (forward _ _ e1) (forward _ _ e2).symm e (forward _ _ e3)
  exact ha (inj eq)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
theorem extend_pentagon (h4 : FourCycleFree G) {c : Fin 5 → V}
    (inj : Function.Injective c) (hcycle : ∀ i j, G.Adj (c i) (c j) ↔ pent i j)
    (x : V) (hx : ∀ i, x ≠ c i) (ha : ∃ i, G.Adj x (c i)) :
    ∃ f : Fin 5 → V, InducedPath G f ∧ f 0 = x ∧
      (∀ i : Fin 5, 0 < i.val → ∃ j : Fin 5, f i = c j) := by
  classical
  let b : Fin 5 → Bool := fun i => decide (G.Adj x (c i))
  have btrue (i : Fin 5) : b i = true ↔ G.Adj x (c i) := by simp [b]
  have d2 (i : Fin 5) (h : b i = true) : b (i+2) = false := by
    cases e : b (i+2)
    · rfl
    · have e1 : pent i (i+1) := Or.inl rfl
      have e2 : pent (i+1) (i+2) := Or.inl (by fin_cases i <;> decide)
      have eq := h4 (c i) (c (i+2)) x (c (i+1))
        (fun w => (show i ≠ i+2 by fin_cases i <;> decide) (inj w))
        ((btrue _).mp h).symm ((btrue _).mp e).symm
        ((hcycle _ _).mpr e1) ((hcycle _ _).mpr e2).symm
      exact False.elim (hx _ eq)
  obtain ⟨i,pos,hi,hs⟩ := oma133_PentagonRead133_computed_spokePath b d2 (by
    obtain ⟨i,he⟩ := ha
    exact ⟨i,(btrue _).mpr he⟩)
  let g (r : Fin 6) : V := if hr : r.val < 5 then c ⟨r.val,hr⟩ else x
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < 5 <;> by_cases hB : b.val < 5
    · have he := inj (show c ⟨a.val,hA⟩ = c ⟨b.val,hB⟩ by simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun t : Fin 5 => t.val) he)
    · exact False.elim (hx ⟨a.val,hA⟩ (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm))
    · exact False.elim (hx ⟨b.val,hB⟩ (by simpa only [g,dif_neg hA,dif_pos hB] using eq))
    · apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
  have hrel (a q : Fin 6) : G.Adj (g a) (g q) ↔ oma133_PentagonRead133_reserved b a q := by
    by_cases hA : a.val < 5 <;> by_cases hQ : q.val < 5
    · simpa only [g,oma133_PentagonRead133_reserved,dif_pos hA,dif_pos hQ] using hcycle ⟨a.val,hA⟩ ⟨q.val,hQ⟩
    · simpa only [g,oma133_PentagonRead133_reserved,dif_pos hA,dif_neg hQ,G.adj_comm] using (btrue ⟨a.val,hA⟩).symm
    · simpa only [g,oma133_PentagonRead133_reserved,dif_neg hA,dif_pos hQ] using (btrue ⟨q.val,hQ⟩).symm
    · simp [g,oma133_PentagonRead133_reserved,hA,hQ]
  refine ⟨g ∘ oma133_PentagonRead133_spokePath i pos,⟨ginj.comp hi,fun a q he => (hrel _ _).trans (hs a q he)⟩,rfl,?_⟩
  intro j hj
  have hbase : ∀ a pos (j : Fin 5), 0 < j.val → (oma133_PentagonRead133_spokePath a pos j).val < 5 := by decide
  have lt := hbase i pos j hj
  exact ⟨⟨_,lt⟩,dif_pos lt⟩

end Graffiti133Pentagon

end OMA133_PentagonRead133

section OMA133_LocalDensity133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Finset
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem memLocal {G : SimpleGraph V} {v : V} {A : Finset V} :
    A ∈ localIndependentSets G v ↔ (∀ x ∈ A, G.Adj v x) ∧
      (∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) := by
  classical
  simp only [localIndependentSets, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_iff, Finset.mem_univ, true_and]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem maxLocal (G : SimpleGraph V) (v : V) :
    ∃ A ∈ localIndependentSets G v, A.card = localIndependence G v := by
  classical
  obtain ⟨A,hA,hM⟩ := Finset.exists_max_image (localIndependentSets G v) Finset.card
    ⟨∅, memLocal.mpr (by simp)⟩
  exact ⟨A,hA,le_antisymm (Finset.le_sup (f := Finset.card) hA)
    (Finset.sup_le_iff.mpr hM)⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem liftLocal (G : SimpleGraph V) (v : V) (x : {y : V | y ≠ v})
    (A : Finset V) (hA : A ∈ localIndependentSets G x.val) (hv : v ∉ A) :
    A.card ≤ localIndependence (G.induce {y | y ≠ v}) x := by
  classical
  let K := A.subtype fun y => y ≠ v
  have hCard : K.card = A.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_eq_self.mpr (fun w hw e => hv (e ▸ hw))
  have hl : K ∈ localIndependentSets (G.induce {y | y ≠ v}) x := by
    obtain ⟨hn,hi⟩ := memLocal.mp hA
    apply memLocal.mpr
    exact ⟨fun y hy => hn _ (Finset.mem_subtype.mp hy),
      fun a ha b hb => hi _ (Finset.mem_subtype.mp ha) _ (Finset.mem_subtype.mp hb)⟩
  rw [← hCard]
  exact Finset.le_sup (f:=Finset.card) hl

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private noncomputable def lone (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x => G.Adj v x ∧ ¬ ∃ y, G.Adj v y ∧ G.Adj x y

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem lone_le_local (G : SimpleGraph V) (v : V) :
    (lone G v).card ≤ localIndependence G v := by
  classical
  have spec {x : V} (hx : x ∈ lone G v) := (Finset.mem_filter.mp hx).2
  exact Finset.le_sup (f:=Finset.card) (memLocal.mpr
    ⟨fun x hx => (spec hx).1,fun x hx y hy e => (spec hx).2 ⟨y,(spec hy).1,e⟩⟩)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private noncomputable def loneCost (G : SimpleGraph V) (v x : V) : ℕ := by
  classical
  exact if x ∈ lone G v then 1 else 0

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem one_loss (G : SimpleGraph V) (h4 : FourCycleFree G)
    (v : V) (x : {y : V | y ≠ v}) :
    localIndependence G x.val ≤ localIndependence (G.induce {y | y ≠ v}) x +
      loneCost G v x.val := by
  classical
  obtain ⟨A,hA,hc⟩ := maxLocal G x.val
  by_cases hv : v ∈ A
  · obtain ⟨hn,hi⟩ := memLocal.mp hA
    by_cases ht : x.val ∈ lone G v
    · have ha' : A.erase v ∈ localIndependentSets G x.val := by
        apply memLocal.mpr
        exact ⟨fun y hy => hn _ (Finset.mem_of_mem_erase hy),
          fun a ha b hb => hi _ (Finset.mem_of_mem_erase ha) _ (Finset.mem_of_mem_erase hb)⟩
      have hl := liftLocal G v x (A.erase v) ha' (Finset.notMem_erase _ _)
      rw [Finset.card_erase_of_mem hv,hc] at hl
      simp only [loneCost,if_pos ht]
      omega
    · have et : ∃ z, G.Adj v z ∧ G.Adj x.val z := by
        apply Classical.byContradiction
        intro no
        exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hn _ hv).symm,no⟩)
      obtain ⟨z,hvz,hxz⟩ := et
      have hz : z ∉ A := fun h => hi v hv z h hvz
      let B := insert z (A.erase v)
      have hB : B ∈ localIndependentSets G x.val := by
        dsimp only [B]
        have nochord (y : V) (hy : y ∈ A.erase v) : ¬G.Adj z y := by
          intro e
          have eq := h4 x.val z y v hxz.ne (hn _ (Finset.mem_of_mem_erase hy))
            e (hn _ hv) hvz.symm
          exact (Finset.ne_of_mem_erase hy) eq
        apply memLocal.mpr
        refine ⟨?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hxz
          · exact hn _ (Finset.mem_of_mem_erase hy)
        · intro a ha b hb
          rcases Finset.mem_insert.mp ha with ea | hax
          · rcases Finset.mem_insert.mp hb with eb | hbx
            · rw [ea,eb]
              exact G.loopless.irrefl _
            · rw [ea]
              exact nochord _ hbx
          · rcases Finset.mem_insert.mp hb with eb | hbx
            · rw [eb]
              exact fun e => nochord _ hax e.symm
            · exact hi _ (Finset.mem_of_mem_erase hax) _ (Finset.mem_of_mem_erase hbx)
      have hnv : v ∉ B := by simp [B,hvz.ne]
      have hl := liftLocal G v x B hB hnv
      unfold B at hl
      rw [Finset.card_insert_of_notMem (fun h => hz (Finset.mem_of_mem_erase h)),
        Finset.card_erase_add_one hv,hc] at hl
      simpa only [loneCost,if_neg ht,Nat.add_zero] using hl
  · rw [← hc]
    exact (liftLocal G v x A hA hv).trans (Nat.le_add_right _ _)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem local_sum_delete_bound (G : SimpleGraph V) (h4 : FourCycleFree G) (v : V) :
    (∑ y, localIndependence G y) ≤
      (∑ y : {y : V | y ≠ v}, localIndependence (G.induce {y | y ≠ v}) y) +
      2 * localIndependence G v := by
  classical
  let W := {y : V | y ≠ v}
  let H := G.induce W
  have hh (x : W) := one_loss G h4 v x
  have rhs := Finset.sum_le_sum (s := (Finset.univ : Finset W)) (fun x _ => hh x)
  rw [Finset.sum_add_distrib] at rhs
  have original : (∑ x : W, localIndependence G x.val) + localIndependence G v =
      ∑ x, localIndependence G x := by
    have h := (Finset.sum_erase_add (s := (Finset.univ : Finset V))
      (f := fun x => localIndependence G x) (Finset.mem_univ v))
    have hh := Finset.sum_subtype ((Finset.univ : Finset V).erase v) (p := fun x => x ≠ v) (F := inferInstanceAs (Fintype W)) (by simp) (localIndependence G)
    exact (congrArg (fun n => n + localIndependence G v) hh.symm).trans h
  have lonelyCard : (∑ x : W, loneCost G v x.val) = (lone G v).card := by
    have sub : (lone G v).filter (fun x => x ≠ v) = lone G v := by
      apply Finset.filter_eq_self.mpr
      intro x hx e
      subst x
      exact G.loopless.irrefl v (Finset.mem_filter.mp hx).2.1
    have hh := Finset.sum_subtype ((Finset.univ : Finset V).erase v) (p := fun x => x ≠ v) (F := inferInstanceAs (Fintype W)) (by simp) (loneCost G v)
    refine hh.symm.trans ?_
    have hF : ((Finset.univ : Finset V).erase v).filter (fun x => x ∈ lone G v) = lone G v := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true]
      exact ⟨And.right,fun hx => ⟨fun e => by subst x; exact G.loopless.irrefl v (Finset.mem_filter.mp hx).2.1,hx⟩⟩
    simp [loneCost,Finset.sum_ite,hF,Finset.erase_eq_of_notMem (show v ∉ lone G v by
      intro hv
      exact G.loopless.irrefl v (Finset.mem_filter.mp hv).2.1)]
  change (∑ x : W, localIndependence G x.val) ≤ (∑ x : W, localIndependence H x) +
    (∑ x : W, loneCost G v x.val) at rhs
  rw [lonelyCard] at rhs
  change (∑ y, localIndependence G y) ≤ (∑ y : W, localIndependence H y) + _
  rw [← original]
  have := lone_le_local G v
  omega

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem lift_local_density_path (k d t : ℕ) (hd : 1 ≤ d) (ht : 2*d ≤ t)
    (G : SimpleGraph V) [Nonempty V] (h4 : FourCycleFree G)
    (hD : t*Fintype.card V ≤ (∑ x, localIndependence G x))
    (witness : ∀ (W : Type u) [Fintype W] [Nonempty W] (J : SimpleGraph W) (e : W ↪ V),
      (∀ a b, J.Adj a b ↔ G.Adj (e a) (e b)) → FourCycleFree J →
      (∀ x, d+1 ≤ localIndependence J x) →
      t*Fintype.card W ≤ (∑ x, localIndependence J x) →
      ∃ f : Fin k → W, InducedPath J f) :
    ∃ f : Fin k → V, InducedPath G f := by
  classical
  let Claim (n : ℕ) := ∀ (W : Type u) [Fintype W] [DecidableEq W] [Nonempty W],
    Fintype.card W = n → ∀ (J : SimpleGraph W) (e : W ↪ V),
    (∀ a b, J.Adj a b ↔ G.Adj (e a) (e b)) → FourCycleFree J →
    t*Fintype.card W ≤ (∑ x, localIndependence J x) →
    ∃ f : Fin k → W, InducedPath J f
  have aux (n : ℕ) : Claim n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ hn G e hEmbed h4 dens
      by_cases hh : ∀ v, d+1 ≤ localIndependence G v
      · exact witness W G e hEmbed h4 hh dens
      push_neg at hh
      obtain ⟨v,hv⟩ := hh
      let S : Set W := {x | x ≠ v}
      let H := G.induce S
      have hpos : 0 < Fintype.card W := Fintype.card_pos
      have hS : Fintype.card S + 1 = Fintype.card W := by
        have hs : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card {x : W // ¬ x = v} = _
          rw [Fintype.card_subtype_compl]
          rw [show Fintype.card {x : W // x = v} = 1 from Fintype.card_unique]
        omega
      have hFree : FourCycleFree H := by
        intro a b x y hab hax hbx hay hby
        apply Subtype.ext
        exact h4 _ _ _ _ (fun h => hab (Subtype.ext h)) hax hbx hay hby
      have posSum := (Nat.mul_pos (show 0 < t by omega) hpos).trans_le dens
      have edg : ∃ a b, G.Adj a b := by
        apply Classical.byContradiction
        intro no
        have nn : ∀ x, localIndependence G x = 0 := by
          intro x
          obtain ⟨A,hA,hAC⟩ := maxLocal G x
          rw [← hAC,Finset.card_eq_zero]
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          obtain ⟨a,ha⟩ := hne
          exact no ⟨x,a,(memLocal.mp hA).1 a ha⟩
        simp [nn] at posSum
      obtain ⟨a,b,hab⟩ := edg
      haveI : Nonempty S := by
        by_cases eq : a = v
        · exact ⟨⟨b,(eq ▸ hab.ne).symm⟩⟩
        · exact ⟨⟨a,eq⟩⟩
      have hloss := local_sum_delete_bound G h4 v
      have hD' : t*Fintype.card S ≤ (∑ x, localIndependence H x) := by
        rw [← hS,Nat.mul_add,Nat.mul_one] at dens
        change (∑ x, localIndependence G x) ≤ (∑ x : S, localIndependence H x) +
          2*localIndependence G v at hloss
        omega
      have hsN : Fintype.card S < n := by omega
      obtain ⟨f,hf⟩ := ih _ hsN S rfl H ((Function.Embedding.subtype _).trans e)
        (fun a b => hEmbed a.val b.val) hFree hD'
      exact ⟨fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
  exact aux (Fintype.card V) V rfl G (Function.Embedding.refl V) (fun _ _ => Iff.rfl) h4 hD

end Graffiti133Revisit

end OMA133_LocalDensity133

section OMA133_FiveCycle133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Finset
open scoped BigOperators

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private def oma133_FiveCycle133_pent (i j : Fin 5) : Prop := i + 1 = j ∨ j + 1 = i
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private instance : DecidableRel oma133_FiveCycle133_pent := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private lemma oma133_FiveCycle133_pent_alt : ∀ i j : Fin 5, i ≠ j → ¬oma133_FiveCycle133_pent i j →
    ∃ a b, a ≠ j ∧ b ≠ i ∧ oma133_FiveCycle133_pent i a ∧ oma133_FiveCycle133_pent a b ∧ oma133_FiveCycle133_pent b j := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private def oma133_FiveCycle133_reserved (b : Fin 5 → Bool) (i j : Fin 6) : Prop :=
  if hi : i.val < 5 then
    if hj : j.val < 5 then oma133_FiveCycle133_pent ⟨i.val,hi⟩ ⟨j.val,hj⟩
    else b ⟨i.val,hi⟩ = true
  else if hj : j.val < 5 then b ⟨j.val,hj⟩ = true else False
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private instance (b : Fin 5 → Bool) : DecidableRel (oma133_FiveCycle133_reserved b) := by
  intro i j
  unfold oma133_FiveCycle133_reserved
  split <;> split <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private def oma133_FiveCycle133_spokePath (i : Fin 5) (positive : Bool) : Fin 5 → Fin 6 :=
  ![5, i.castSucc, (i + (if positive then 1 else 4)).castSucc,
    (i + (if positive then 2 else 3)).castSucc, (i + (if positive then 3 else 2)).castSucc]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private lemma oma133_FiveCycle133_computed_spokePath : ∀ b : Fin 5 → Bool,
    (∀ i, b i = true → b (i+2) = false) → (∃ i, b i = true) →
    ∃ i pos,
      (∀ u v : Fin 5, oma133_FiveCycle133_spokePath i pos u = oma133_FiveCycle133_spokePath i pos v → u = v) ∧
      ∀ u v : Fin 5, u < v → (oma133_FiveCycle133_reserved b (oma133_FiveCycle133_spokePath i pos u) (oma133_FiveCycle133_spokePath i pos v) ↔
        u.val + 1 = v.val) := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private theorem oma133_FiveCycle133_cycle_pentagon (h4 : FourCycleFree G) {c : Fin 5 → V}
    (inj : Function.Injective c) (sides : ∀ i, G.Adj (c i) (c (i+1))) :
    ∀ i j, G.Adj (c i) (c j) ↔ oma133_FiveCycle133_pent i j := by
  have forward (i j : Fin 5) (h : oma133_FiveCycle133_pent i j) : G.Adj (c i) (c j) := by
    rcases h with e | e
    · exact e ▸ sides i
    · exact e ▸ (sides j).symm
  intro i j
  refine ⟨?_,forward i j⟩
  intro e
  apply Classical.byContradiction
  intro no
  obtain ⟨a,b,ha,hb,e1,e2,e3⟩ := oma133_FiveCycle133_pent_alt i j (fun h => e.ne (congrArg c h)) no
  have eq := h4 (c i) (c b) (c a) (c j) (fun h => hb (inj h).symm)
    (forward _ _ e1) (forward _ _ e2).symm e (forward _ _ e3)
  exact ha (inj eq)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1000000 in
private theorem oma133_FiveCycle133_extend_pentagon (h4 : FourCycleFree G) {c : Fin 5 → V}
    (inj : Function.Injective c) (hcycle : ∀ i j, G.Adj (c i) (c j) ↔ oma133_FiveCycle133_pent i j)
    (x : V) (hx : ∀ i, x ≠ c i) (ha : ∃ i, G.Adj x (c i)) :
    ∃ f : Fin 5 → V, InducedPath G f := by
  classical
  let b : Fin 5 → Bool := fun i => decide (G.Adj x (c i))
  have btrue (i : Fin 5) : b i = true ↔ G.Adj x (c i) := by simp [b]
  have d2 (i : Fin 5) (h : b i = true) : b (i+2) = false := by
    cases e : b (i+2)
    · rfl
    · have e1 : oma133_FiveCycle133_pent i (i+1) := Or.inl rfl
      have e2 : oma133_FiveCycle133_pent (i+1) (i+2) := Or.inl (by fin_cases i <;> decide)
      have eq := h4 (c i) (c (i+2)) x (c (i+1))
        (fun w => (show i ≠ i+2 by fin_cases i <;> decide) (inj w))
        ((btrue _).mp h).symm ((btrue _).mp e).symm
        ((hcycle _ _).mpr e1) ((hcycle _ _).mpr e2).symm
      exact False.elim (hx _ eq)
  obtain ⟨i,pos,hi,hs⟩ := oma133_FiveCycle133_computed_spokePath b d2 (by
    obtain ⟨i,he⟩ := ha
    exact ⟨i,(btrue _).mpr he⟩)
  let g (r : Fin 6) : V := if hr : r.val < 5 then c ⟨r.val,hr⟩ else x
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < 5 <;> by_cases hB : b.val < 5
    · have he := inj (show c ⟨a.val,hA⟩ = c ⟨b.val,hB⟩ by simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun t : Fin 5 => t.val) he)
    · exact False.elim (hx ⟨a.val,hA⟩ (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm))
    · exact False.elim (hx ⟨b.val,hB⟩ (by simpa only [g,dif_neg hA,dif_pos hB] using eq))
    · apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
  have hrel (a q : Fin 6) : G.Adj (g a) (g q) ↔ oma133_FiveCycle133_reserved b a q := by
    by_cases hA : a.val < 5 <;> by_cases hQ : q.val < 5
    · simpa only [g,oma133_FiveCycle133_reserved,dif_pos hA,dif_pos hQ] using hcycle ⟨a.val,hA⟩ ⟨q.val,hQ⟩
    · simpa only [g,oma133_FiveCycle133_reserved,dif_pos hA,dif_neg hQ,G.adj_comm] using (btrue ⟨a.val,hA⟩).symm
    · simpa only [g,oma133_FiveCycle133_reserved,dif_neg hA,dif_pos hQ] using (btrue ⟨q.val,hQ⟩).symm
    · simp [g,oma133_FiveCycle133_reserved,hA,hQ]
  exact ⟨g ∘ oma133_FiveCycle133_spokePath i pos,ginj.comp hi,fun a q he => (hrel _ _).trans (hs a q he)⟩

end Graffiti133Revisit

end OMA133_FiveCycle133

section OMA133_RoundedBand133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Finset
open scoped BigOperators
variable {V : Type*} [Fintype V]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
theorem nat_density_of_le_average (G : SimpleGraph V) [Nonempty V] (d : ℕ)
    (h : (d : ℚ) ≤ averageLocal G) :
    d * Fintype.card V ≤ ∑ x, localIndependence G x := by
  classical
  unfold averageLocal at h
  have hn : (0 : ℚ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos (α := V)
  have hu := (le_div_iff₀ hn).mp h
  rw [← Nat.cast_sum, ← Nat.cast_mul] at hu
  exact_mod_cast hu

end Graffiti133Revisit

end OMA133_RoundedBand133

section OMA133_SixCycle133

namespace Graffiti133RevisitSix
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
open scoped BigOperators

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private def hex (i j : Fin 6) : Prop := i + 1 = j ∨ j + 1 = i
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private instance : DecidableRel hex := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private def oma133_SixCycle133_reserved (b : Fin 6 → Bool) (i j : Fin 7) : Prop :=
  if hi : i.val < 6 then
    if hj : j.val < 6 then hex ⟨i.val,hi⟩ ⟨j.val,hj⟩
    else b ⟨i.val,hi⟩ = true
  else if hj : j.val < 6 then b ⟨j.val,hj⟩ = true else False
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private instance (b : Fin 6 → Bool) : DecidableRel (oma133_SixCycle133_reserved b) := by
  intro i j
  unfold oma133_SixCycle133_reserved
  split <;> split <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private def oma133_SixCycle133_spokePath (i : Fin 6) (positive : Bool) : Fin 6 → Fin 7 :=
  ![6, i.castSucc, (i + (if positive then 1 else 5)).castSucc,
    (i + (if positive then 2 else 4)).castSucc, (i + 3).castSucc,
    (i + (if positive then 4 else 2)).castSucc]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private lemma oma133_SixCycle133_computed_spokePath : ∀ b : Fin 6 → Bool,
    (∀ i, b i = true → b (i+2) = false ∧ b (i+3) = false) → (∃ i, b i = true) →
    ∃ i pos,
      (∀ u v : Fin 6, oma133_SixCycle133_spokePath i pos u = oma133_SixCycle133_spokePath i pos v → u = v) ∧
      ∀ u v : Fin 6, u < v → (oma133_SixCycle133_reserved b (oma133_SixCycle133_spokePath i pos u) (oma133_SixCycle133_spokePath i pos v) ↔
        u.val + 1 = v.val) := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
theorem prepend_induced_with_positions {k : ℕ} (hk : 0 < k) {f : Fin k → V}
    (hf : InducedPath G f) (w : V) (hnew : ∀ i, w ≠ f i)
    (h₀ : G.Adj w (f ⟨0,hk⟩)) (h₁ : ∀ i : Fin k, 0 < i.val → ¬ G.Adj w (f i)) :
    ∃ ff : Fin (k+1) → V, InducedPath G ff ∧ ff ⟨0,by omega⟩ = w ∧
      ∀ i : Fin (k+1), ∀ hi : 0 < i.val, ff i = f ⟨i.val-1,by have := i.isLt; omega⟩ := by
  let F (i : Fin (k+1)) : V :=
    if h : i.val = 0 then w else f ⟨i.val-1,by omega⟩
  have head (i : Fin (k+1)) (hi : i.val = 0) : F i = w := dif_pos hi
  have tail (i : Fin (k+1)) (hi : i.val ≠ 0) :
      F i = f ⟨i.val-1,by have := i.isLt; omega⟩ := dif_neg hi
  refine ⟨F,⟨?_,?_⟩,head _ rfl, fun i hi => tail i (by omega)⟩
  · intro i j h
    apply Fin.ext
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · omega
    · rw [head _ hi,tail _ hj] at h
      exact (hnew _ h).elim
    · rw [tail _ hi,head _ hj] at h
      exact (hnew _ h.symm).elim
    · rw [tail _ hi,tail _ hj] at h
      have hh := congrArg Fin.val (hf.1 h)
      change i.val-1 = j.val-1 at hh
      omega
  · intro i j hij
    change i.val < j.val at hij
    have hji := j.isLt
    have hj : j.val ≠ 0 := by omega
    rw [tail _ hj]
    by_cases hi : i.val = 0
    · rw [head _ hi]
      by_cases h : j.val = 1
      · have hindex : (⟨j.val-1,by omega⟩ : Fin k) = ⟨0,hk⟩ :=
          Fin.ext (by change j.val-1=0; omega)
        rw [hindex]
        exact iff_of_true h₀ (by omega)
      · exact iff_of_false (h₁ _ (by change 0 < j.val-1; omega)) (by omega)
    · rw [tail _ hi,hf.2 _ _ (by change i.val-1 < j.val-1; omega)]
      change (i.val-1+1 = j.val-1) ↔ (i.val+1 = j.val)
      omega

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem oma133_SixCycle133_neighbor_pair (v : V) (hv : 2 ≤ localIndependence G v) :
    ∃ x y, x ≠ y ∧ G.Adj v x ∧ G.Adj v y ∧ ¬G.Adj x y := by
  classical
  have m (s : Finset V) : s ∈ localIndependentSets G v ↔
      (∀ x ∈ s, G.Adj v x) ∧ (∀ x ∈ s, ∀ y ∈ s, ¬G.Adj x y) := by
    simp [localIndependentSets, Finset.subset_iff]
  obtain ⟨A,hA,hM⟩ := Finset.exists_max_image (localIndependentSets G v) Finset.card
    ⟨∅, m _ |>.mpr (by simp)⟩
  have hi : localIndependence G v ≤ A.card := Finset.sup_le_iff.mpr hM
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  have hA := (m _).mp hA
  exact ⟨x,y,hxy,hA.1 x hx,hA.1 y hy,hA.2 x hx y hy⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem oma133_SixCycle133_side_neighbor (h4 : FourCycleFree G) {v s : V} (e : G.Adj v s)
    (hv : 2 ≤ localIndependence G v) :
    ∃ w, G.Adj v w ∧ w ≠ s ∧ ¬G.Adj w s := by
  obtain ⟨x,y,hne,hx,hy,hxy⟩ := oma133_SixCycle133_neighbor_pair v hv
  by_cases ex : x = s
  · subst x
    exact ⟨y,hy,hne.symm,fun h => hxy h.symm⟩
  by_cases ey : y = s
  · subst y
    exact ⟨x,hx,hne,hxy⟩
  by_cases es : G.Adj x s
  · have no : ¬ G.Adj y s := by
      intro hb
      exact hne (h4 v s x y e.ne hx es.symm hy hb.symm)
    exact ⟨y,hy,ey,no⟩
  · exact ⟨x,hx,ex,es⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem oma133_SixCycle133_short_neighbor (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) {k : ℕ} (hk : 2 ≤ k) {f : Fin k → V}
    (p : InducedPath G f) (hv : 2 ≤ localIndependence G (f ⟨0,by omega⟩)) :
    ∃ w, (∀ i, w ≠ f i) ∧ G.Adj w (f ⟨0,by omega⟩) ∧
      (∀ i : Fin k, 0 < i.val → i.val ≤ 3 → ¬G.Adj w (f i)) := by
  let a : Fin k := ⟨0,by omega⟩
  let b : Fin k := ⟨1,by omega⟩
  have e : G.Adj (f a) (f b) := (p.2 a b (by change 0<1; decide)).mpr rfl
  obtain ⟨w,ew,hw,hwB⟩ := oma133_SixCycle133_side_neighbor h4 e hv
  have off (i : Fin k) : w ≠ f i := by
    intro eq
    by_cases h : i = a
    · rw [h] at eq
      exact ew.ne eq.symm
    · have hlt : a < i := by
        change 0 < i.val
        apply Nat.pos_of_ne_zero
        intro he
        exact h (Fin.ext he)
      have j := (p.2 a i hlt).mp (eq ▸ ew)
      have eqi : i = b := Fin.ext j.symm
      exact hw (eq.trans (congrArg f eqi))
  have no2 {i : Fin k} (hi : i.val = 2) : ¬G.Adj w (f i) := by
    intro ewi
    have ebi := (p.2 b i (by change 1 < i.val; omega)).mpr (by change 2=i.val; omega)
    have eq := h4 (f a) (f i) w (f b) (fun h => by
      have hh := congrArg Fin.val (p.1 h)
      change 0 = i.val at hh
      omega) ew ewi.symm e ebi.symm
    exact hw eq
  refine ⟨w,off,ew.symm,?_⟩
  intro i hlo hhi
  rcases (show i.val = 1 ∨ i.val = 2 ∨ i.val = 3 by omega) with h | h | h
  · have ei : i = b := Fin.ext h
    exact ei ▸ hwB
  · exact no2 h
  · intro ewi
    let j : Fin k := ⟨2,by have := i.isLt; omega⟩
    have eBj := (p.2 b j (by change 1<2; decide)).mpr rfl
    have eji := (p.2 j i (by change 2 < i.val; omega)).mpr (by change 3=i.val; omega)
    have hIndices : [a,b,j,i].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
      constructor
      · intro neq
        rcases neq with q | q | q <;> have uu := congrArg Fin.val q <;> dsimp [a,b,j] at uu <;> omega
      · constructor
        · intro neq
          rcases neq with q | q <;> have uu := congrArg Fin.val q <;> dsimp [a,b,j] at uu <;> omega
        · refine ⟨?_, by trivial⟩
          intro q
          have hh := congrArg Fin.val q
          dsimp [j] at hh
          omega
    have hLists : [w,f a,f b,f j,f i].Nodup := by
      apply List.nodup_cons.mpr
      refine ⟨by simp [off],?_⟩
      simpa using hIndices.map p.1
    exact h5 _ _ _ _ _ hLists ew.symm e eBj eji ewi.symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem short_path_through (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (mind : ∀ x, 2 ≤ localIndependence G x) (v : V) :
    ∃ f : Fin 5 → V, InducedPath G f ∧ ∃ i, f i = v := by
  have p2 : ∃ f : Fin 2 → V, InducedPath G f ∧ ∃ i, f i = v := by
    obtain ⟨x,y,hxy,hx,hy,no⟩ := oma133_SixCycle133_neighbor_pair v (mind v)
    refine ⟨![v,x],⟨?_,?_⟩,0,rfl⟩
    · intro a b
      fin_cases a <;> fin_cases b <;> simp [hx.ne,hx.ne.symm]
    · intro a b h
      fin_cases a <;> fin_cases b <;> first | contradiction | exact iff_of_true hx rfl
  have onward : ∀ d : ℕ, d ≤ 3 → ∃ f : Fin (d+2) → V, InducedPath G f ∧ ∃ i, f i = v := by
    intro d
    induction d with
    | zero => intro _; exact p2
    | succ d ih =>
      intro hD
      obtain ⟨f,hf,i,hi⟩ := ih (by omega)
      obtain ⟨w,hw,e,no⟩ := oma133_SixCycle133_short_neighbor h4 h5 (by omega) hf (mind _)
      obtain ⟨g,hg,_,tail⟩ := prepend_induced_with_positions (by omega) hf w hw e
        (fun i hi => no i hi (by have := i.isLt; omega))
      let j : Fin (d+2+1) := ⟨i.val+1, by have := i.isLt; omega⟩
      have he := tail j (show 0 < j.val by dsimp [j]; omega)
      have hj : (⟨j.val-1,by have := i.isLt; dsimp [j]; omega⟩ : Fin (d+2)) = i :=
        Fin.ext (by dsimp [j])
      exact ⟨g,hg,j,he.trans (hj.symm ▸ hi)⟩
  exact onward 3 (by decide)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem extend_hexagon (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) {c : Fin 6 → V}
    (inj : Function.Injective c) (hcycle : ∀ i j, G.Adj (c i) (c j) ↔ hex i j)
    (x : V) (hx : ∀ i, x ≠ c i) (ha : ∃ i, G.Adj x (c i)) :
    ∃ f : Fin 6 → V, InducedPath G f := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (c i))
  have btrue (i : Fin 6) : b i = true ↔ G.Adj x (c i) := by simp [b]
  have d2 (i : Fin 6) (h : b i = true) : b (i+2) = false := by
    cases e : b (i+2)
    · rfl
    · have e1 : hex i (i+1) := Or.inl rfl
      have e2 : hex (i+1) (i+2) := Or.inl (by fin_cases i <;> decide)
      have eq := h4 (c i) (c (i+2)) x (c (i+1))
        (fun w => (show i ≠ i+2 by fin_cases i <;> decide) (inj w))
        ((btrue _).mp h).symm ((btrue _).mp e).symm
        ((hcycle _ _).mpr e1) ((hcycle _ _).mpr e2).symm
      exact False.elim (hx _ eq)
  have d3 (i : Fin 6) (h : b i = true) : b (i+3) = false := by
    cases e : b (i+3)
    · rfl
    · have ei : [i,i+1,i+2,i+3].Nodup :=
        (by decide : ∀ a : Fin 6, [a,a+1,a+2,a+3].Nodup) i
      have hh : [x,c i,c (i+1),c (i+2),c (i+3)].Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨by simp [hx],?_⟩
        simpa using ei.map inj
      exact (h5 _ _ _ _ _ hh ((btrue _).mp h) ((hcycle _ _).mpr (Or.inl rfl))
        ((hcycle _ _).mpr (Or.inl (by fin_cases i <;> decide)))
        ((hcycle _ _).mpr (Or.inl (by fin_cases i <;> decide)))
        ((btrue _).mp e).symm).elim
  obtain ⟨i,pos,hi,hs⟩ := oma133_SixCycle133_computed_spokePath b (fun i h => ⟨d2 i h,d3 i h⟩) (by
    obtain ⟨i,he⟩ := ha
    exact ⟨i,(btrue _).mpr he⟩)
  let g (r : Fin 7) : V := if hr : r.val < 6 then c ⟨r.val,hr⟩ else x
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < 6 <;> by_cases hB : b.val < 6
    · have he := inj (show c ⟨a.val,hA⟩ = c ⟨b.val,hB⟩ by simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun t : Fin 6 => t.val) he)
    · exact False.elim (hx ⟨a.val,hA⟩ (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm))
    · exact False.elim (hx ⟨b.val,hB⟩ (by simpa only [g,dif_neg hA,dif_pos hB] using eq))
    · apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
  have hrel (a q : Fin 7) : G.Adj (g a) (g q) ↔ oma133_SixCycle133_reserved b a q := by
    by_cases hA : a.val < 6 <;> by_cases hQ : q.val < 6
    · simpa only [g,oma133_SixCycle133_reserved,dif_pos hA,dif_pos hQ] using hcycle ⟨a.val,hA⟩ ⟨q.val,hQ⟩
    · simpa only [g,oma133_SixCycle133_reserved,dif_pos hA,dif_neg hQ,G.adj_comm] using (btrue ⟨a.val,hA⟩).symm
    · simpa only [g,oma133_SixCycle133_reserved,dif_neg hA,dif_pos hQ] using (btrue ⟨q.val,hQ⟩).symm
    · simp [g,oma133_SixCycle133_reserved,hA,hQ]
  exact ⟨g ∘ oma133_SixCycle133_spokePath i pos,ginj.comp hi,fun a q he => (hrel _ _).trans (hs a q he)⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private lemma hex_interior : ∀ i j : Fin 5,
    hex i.castSucc j.castSucc ↔ i.val+1=j.val ∨ j.val+1=i.val := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private lemma hex_edge : ∀ i : Fin 5, hex i.castSucc (5 : Fin 6) ↔ i.val=0 ∨ i.val=4 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private lemma hex_diag : ∀ i : Fin 6, ¬hex i i := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private lemma hex_neighbor_indices : ∀ i j : Fin 6, hex i j → j = i+1 ∨ j = i+5 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem hex_symm (i j : Fin 6) : hex i j ↔ hex j i := or_comm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem make_hex {p : Fin 5 → V} (hp : InducedPath G p) (w : V)
    (hw : ∀ i, w ≠ p i) (h0 : G.Adj w (p 0)) (h4 : G.Adj w (p 4))
    (hm : ∀ i : Fin 5, 0 < i.val → i.val ≤ 3 → ¬G.Adj w (p i)) :
    ∃ c : Fin 6 → V, Function.Injective c ∧
      (∀ i j, G.Adj (c i) (c j) ↔ hex i j) ∧ ∀ i, c i.castSucc = p i := by
  let c (i : Fin 6) := if hi : i.val < 5 then p ⟨i.val,hi⟩ else w
  have cP (i : Fin 5) : c i.castSucc = p i := by simp [c,i.isLt]
  have cW : c 5 = w := by rfl
  have other (i : Fin 6) : (∃ a : Fin 5, i = a.castSucc) ∨ i = (5 : Fin 6) := by
    by_cases hi : i.val < 5
    · exact Or.inl ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
    · exact Or.inr (Fin.ext (by change i.val = 5; have := i.isLt; omega))
  have inj : Function.Injective c := by
    intro i j he
    rcases other i with ⟨a,rfl⟩ | rfl <;> rcases other j with ⟨b,rfl⟩ | rfl
    · rw [cP,cP] at he
      exact congrArg Fin.castSucc (hp.1 he)
    · rw [cP,cW] at he
      exact (hw _ he.symm).elim
    · rw [cW,cP] at he
      exact (hw _ he).elim
    · rfl
  have interior (a b : Fin 5) : G.Adj (p a) (p b) ↔ a.val+1=b.val ∨ b.val+1=a.val := by
    rcases lt_trichotomy a b with lt | e | gt
    · rw [hp.2 a b lt]
      change a.val < b.val at lt
      omega
    · subst b
      simp [G.loopless.irrefl]
    · rw [G.adj_comm,hp.2 b a gt]
      change b.val < a.val at gt
      omega
  have exterior (i : Fin 5) : G.Adj (p i) w ↔ i.val=0 ∨ i.val=4 := by
    constructor
    · intro e
      have := i.isLt
      by_cases h0 : i.val = 0
      · exact Or.inl h0
      · by_cases h4 : i.val = 4
        · exact Or.inr h4
        · exact (hm i (by omega) (by omega) e.symm).elim
    · rintro (he | he)
      · have hi : i = 0 := Fin.ext he
        exact hi ▸ h0.symm
      · have hi : i = 4 := Fin.ext he
        exact hi ▸ h4.symm
  refine ⟨c,inj,?_ ,cP⟩
  intro i j
  rcases other i with ⟨a,rfl⟩ | rfl <;> rcases other j with ⟨b,rfl⟩ | rfl
  · rw [cP,cP,hex_interior]
    exact interior a b
  · rw [cP,cW,hex_edge]
    exact exterior a
  · rw [cW,cP,G.adj_comm,hex_symm,hex_edge]
    exact exterior b
  · exact iff_of_false (G.loopless.irrefl _) (hex_diag _)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem local_of_hex_no_P6 (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    {c : Fin 6 → V} (inj : Function.Injective c)
    (hs : ∀ i j, G.Adj (c i) (c j) ↔ hex i j)
    (no : ¬ ∃ f : Fin 6 → V, InducedPath G f) (i : Fin 6) :
    localIndependence G (c i) ≤ 2 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro s hs'
  have h := (Finset.mem_filter.mp hs').1
  have hN := Finset.mem_powerset.mp h
  have hsub : s ⊆ {c (i+1), c (i+5)} := by
    intro x hx
    have hadj := (Finset.mem_filter.mp (hN hx)).2
    by_cases he : ∃ j, c j = x
    · obtain ⟨j,rfl⟩ := he
      rcases hex_neighbor_indices i j ((hs _ _).mp hadj) with he | he <;> simp [he]
    · exact (no (extend_hexagon h4 h5 inj hs x
        (fun j he' => he ⟨j,he'.symm⟩) ⟨i,hadj.symm⟩)).elim
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
theorem six_path_of_min_and_high (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (mind : ∀ v, 2 ≤ localIndependence G v) (v : V) (high : 3 ≤ localIndependence G v) :
    ∃ f : Fin 6 → V, InducedPath G f := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨p,hp,i,hi⟩ := short_path_through h4 h5 mind v
  obtain ⟨w,hw,e,hn⟩ := oma133_SixCycle133_short_neighbor h4 h5 (by decide) hp (mind _)
  have last : G.Adj w (p 4) := by
    apply Classical.byContradiction
    intro hn4
    obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp w hw e (by
      intro j hj
      by_cases j4 : j.val = 4
      · have he : j = 4 := Fin.ext j4
        exact he ▸ hn4
      · exact hn j hj (by have := j.isLt; omega))
    exact no ⟨q,hq⟩
  obtain ⟨c,inj,hs,hOld⟩ := make_hex hp w hw e last hn
  have hV : c i.castSucc = v := (hOld i).trans hi
  have low := local_of_hex_no_P6 h4 h5 inj hs no i.castSucc
  rw [hV] at low
  omega

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
theorem P6_of_local_mean_three (G : SimpleGraph V) [Nonempty V]
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (hA : 3 ≤ averageLocal G) :
    ∃ f : Fin 6 → V, InducedPath G f := by
  classical
  apply lift_local_density_path 6 1 3 (by decide) (by decide) G h4
    (nat_density_of_le_average G 3 hA)
  intro W _ _ J emb hj h4J hmin hD
  have h5J : NoSimpleFive133 J := by
    intro a b c d e hn e1 e2 e3 e4 e5
    have hx := hn.map emb.injective
    exact h5 _ _ _ _ _ (by simpa using hx) ((hj _ _).mp e1)
      ((hj _ _).mp e2) ((hj _ _).mp e3) ((hj _ _).mp e4) ((hj _ _).mp e5)
  obtain ⟨v,hv⟩ : ∃ v, 3 ≤ localIndependence J v := by
    apply Classical.byContradiction
    intro no
    have hBound (x : W) : localIndependence J x ≤ 2 := by
      have : localIndependence J x < 3 := Nat.lt_of_not_ge (fun h => no ⟨x,h⟩)
      omega
    have ht : (∑ x, localIndependence J x) ≤ 2 * Fintype.card W := by
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset W)) (fun x _ => hBound x)
      simpa [Nat.mul_comm] using hh
    have hpos := Fintype.card_pos (α:=W)
    omega
  exact six_path_of_min_and_high h4J h5J hmin v hv

end Graffiti133RevisitSix

end OMA133_SixCycle133

section OMA133_PentagonStructure133

namespace Graffiti133Pentagon
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
def Outside (c : Fin 5 → V) (x : V) : Prop := ∀ i, x ≠ c i
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
def One (G : SimpleGraph V) (c : Fin 5 → V) (x : V) (i : Fin 5) : Prop :=
  Outside c x ∧ ∀ j, G.Adj x (c j) ↔ j = i
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
def Two (G : SimpleGraph V) (c : Fin 5 → V) (x : V) (i : Fin 5) : Prop :=
  Outside c x ∧ ∀ j, G.Adj x (c j) ↔ j = i ∨ j = i+1

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
structure PentagonFrame (G : SimpleGraph V) where
  c : Fin 5 → V
  inj : Function.Injective c
  adj : ∀ i j, G.Adj (c i) (c j) ↔ pent i j
  h4 : FourCycleFree G
  noP6 : ¬ ∃ f : Fin 6 → V, InducedPath G f
  dom : ∀ x, Outside c x → ∃ i, G.Adj x (c i)

namespace PentagonFrame
variable (F : PentagonFrame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma oma133_PentagonStructure133_finite_contact : ∀ b : Fin 5 → Bool,
    (∀ i, b i = true → b (i+2) = false) → (∃ i, b i = true) →
    (∃ i, ∀ j, b j = true ↔ j = i) ∨ (∃ i, ∀ j, b j = true ↔ j = i ∨ j = i+1) := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
lemma contact_sep2 {x : V} (hx : Outside F.c x) (i : Fin 5)
    (h : G.Adj x (F.c i)) : ¬G.Adj x (F.c (i+2)) := by
  intro e
  have eq := F.h4 (F.c i) (F.c (i+2)) x (F.c (i+1))
    (fun w => (show i ≠ i+2 by fin_cases i <;> decide) (F.inj w)) h.symm e.symm
    ((F.adj _ _).mpr (Or.inl rfl))
    ((F.adj _ _).mpr (Or.inr (by fin_cases i <;> decide)))
  exact hx _ eq

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem classify_contact (x : V) (hx : Outside F.c x) :
    (∃ i, One G F.c x i) ∨ (∃ i, Two G F.c x i) := by
  classical
  let b : Fin 5 → Bool := fun i => decide (G.Adj x (F.c i))
  have btrue (i : Fin 5) : b i = true ↔ G.Adj x (F.c i) := by simp [b]
  have sep (i : Fin 5) (h : b i = true) : b (i+2) = false := by
    cases he : b (i+2)
    · rfl
    · exact (F.contact_sep2 hx i ((btrue _).mp h) ((btrue _).mp he)).elim
  obtain ⟨i,hi⟩ := F.dom x hx
  rcases oma133_PentagonStructure133_finite_contact b sep ⟨i,(btrue _).mpr hi⟩ with ⟨j,hj⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨j,hx,fun w => (btrue _).symm.trans (hj w)⟩
  · exact Or.inr ⟨j,hx,fun w => (btrue _).symm.trans (hj w)⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem same_site_neighbors {x y z : V} (hx : Outside F.c x)
    (e1 : G.Adj x y) (e2 : G.Adj x z) {j : Fin 5}
    (hy : G.Adj y (F.c j)) (hz : G.Adj z (F.c j)) : y = z :=
  F.h4 x (F.c j) y z (hx j) e1 hy.symm e2 hz.symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem memLocalSet {v : V} {A : Finset V} :
    A ∈ localIndependentSets G v ↔ (∀ x ∈ A, G.Adj v x) ∧
      (∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) := by
  classical
  simp only [localIndependentSets, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_iff, Finset.mem_univ, true_and]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem maxLocalSet (v : V) :
    ∃ A ∈ localIndependentSets G v, A.card = localIndependence G v := by
  classical
  obtain ⟨A,hA,hM⟩ := Finset.exists_max_image (localIndependentSets G v) Finset.card
    ⟨∅, memLocalSet.mpr (by simp)⟩
  exact ⟨A,hA,le_antisymm (Finset.le_sup (f := Finset.card) hA)
    (Finset.sup_le_iff.mpr hM)⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private def oma133_PentagonStructure133_Stamp (y : V) (j : Fin 5) : Prop :=
  y = F.c j ∨ (Outside F.c y ∧ G.Adj y (F.c j))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem oma133_PentagonStructure133_stamp_exists (y : V) : ∃ j, F.oma133_PentagonStructure133_Stamp y j := by
  by_cases hi : Outside F.c y
  · obtain ⟨j,h⟩ := F.dom y hi
    exact ⟨j,Or.inr ⟨hi,h⟩⟩
  · apply Classical.byContradiction
    intro bad
    exact hi (fun j e => bad ⟨j,Or.inl e⟩)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem oma133_PentagonStructure133_stamp_inj {x y z : V} {j : Fin 5} (hx : Outside F.c x)
    (ey : G.Adj x y) (ez : G.Adj x z) (no : ¬ G.Adj y z)
    (sy : F.oma133_PentagonStructure133_Stamp y j) (sz : F.oma133_PentagonStructure133_Stamp z j) : y = z := by
  rcases sy with sy | ⟨hy,e1⟩ <;> rcases sz with sz | ⟨hz,e2⟩
  · exact sy.trans sz.symm
  · exact (no (sy.symm ▸ e2.symm)).elim
  · exact (no (sz.symm ▸ e1)).elim
  · exact F.same_site_neighbors hx ey ez e1 e2

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
noncomputable def label (y : V) : Fin 5 := Classical.choose (F.oma133_PentagonStructure133_stamp_exists y)
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem label_stamp (y : V) : F.oma133_PentagonStructure133_Stamp y (F.label y) :=
  Classical.choose_spec (F.oma133_PentagonStructure133_stamp_exists y)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem oma133_PentagonStructure133_label_inj {x : V} (hx : Outside F.c x)
    (A : Finset V) (hA : A ∈ localIndependentSets G x) :
    Set.InjOn F.label (↑A : Set V) := by
  obtain ⟨hN,hI⟩ := memLocalSet.mp hA
  intro y hy z hz he
  exact F.oma133_PentagonStructure133_stamp_inj hx (hN _ hy) (hN _ hz) (hI _ hy _ hz)
    (F.label_stamp y) (he.symm ▸ F.label_stamp z)

end PentagonFrame
end Graffiti133Pentagon

end OMA133_PentagonStructure133

section OMA133_PentagonBudget133

namespace Graffiti133Pentagon
namespace PentagonFrame
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : PentagonFrame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
noncomputable def singleSite (i : Fin 5) : Finset V := by
  classical
  exact univ.filter (fun x => One G F.c x i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma oma133_PentagonBudget133_site_mem {i : Fin 5} {x : V} :
    x ∈ F.singleSite i ↔ One G F.c x i := by
  classical
  simp [singleSite]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma pent_neighbors : ∀ i j : Fin 5, pent i j ↔ j = i+1 ∨ j = i+4 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma pent_ne : ∀ i j : Fin 5, pent i j → i ≠ j := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private def CSeat (y : V) (j : Fin 5) : Prop :=
  y = F.c j ∨ (Outside F.c y ∧ G.Adj y (F.c j))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem seat_for_non_single {i : Fin 5} {y : V} (ha : G.Adj (F.c i) y)
    (no : y ∉ F.singleSite i) : ∃ j, pent i j ∧ F.CSeat y j := by
  classical
  by_cases h : Outside F.c y
  · rcases F.classify_contact y h with ⟨j,hj⟩ | ⟨j,hj⟩
    · have e := (hj.2 i).mp ha.symm
      exact (no ((F.oma133_PentagonBudget133_site_mem).mpr (e.symm ▸ hj))).elim
    · rcases (hj.2 i).mp ha.symm with eq | eq
      · exact ⟨j+1,Or.inl (by rw [eq]),Or.inr ⟨h,(hj.2 _).mpr (Or.inr rfl)⟩⟩
      · exact ⟨j,Or.inr eq.symm,Or.inr ⟨h,(hj.2 _).mpr (Or.inl rfl)⟩⟩
  · obtain ⟨j,hj⟩ : ∃ j, y = F.c j := by
      apply Classical.byContradiction
      intro hh
      exact h fun j e => hh ⟨j,e⟩
    exact ⟨j,(F.adj _ _).mp (hj ▸ ha),Or.inl hj⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem cSeat_inj {i j : Fin 5} {y z : V}
    (hij : pent i j) (hy : G.Adj (F.c i) y) (hz : G.Adj (F.c i) z)
    (e : ¬G.Adj y z) (sy : F.CSeat y j) (sz : F.CSeat z j) :
    y = z := by
  rcases sy with sy | ⟨hoy,hyt⟩ <;> rcases sz with sz | ⟨hoz,hzt⟩
  · exact sy.trans sz.symm
  · exact (e (sy.symm ▸ hzt.symm)).elim
  · exact (e (sz.symm ▸ hyt)).elim
  · exact F.h4 (F.c i) (F.c j) y z (fun h => pent_ne i j hij (F.inj h))
      hy hyt.symm hz hzt.symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem local_cycle_bound (i : Fin 5) :
    localIndependence G (F.c i) ≤ 2 + (F.singleSite i).card := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := memLocalSet.mp hA
  let B := A \ F.singleSite i
  have haveLabel (y : V) (hy : y ∈ B) : ∃ j, pent i j ∧ F.CSeat y j :=
    F.seat_for_non_single (hN y (Finset.mem_sdiff.mp hy).1) (Finset.mem_sdiff.mp hy).2
  let rho (y : V) : Fin 5 := if hy : y ∈ B then Classical.choose (haveLabel y hy) else i
  have labels (y : V) (hy : y ∈ B) : pent i (rho y) ∧ F.CSeat y (rho y) := by
    rw [show rho y = Classical.choose (haveLabel y hy) from dif_pos hy]
    exact Classical.choose_spec (haveLabel y hy)
  have hinj : Set.InjOn rho (↑B : Set V) := by
    intro y hy z hz he
    exact F.cSeat_inj (labels y hy).1
      (hN _ (Finset.mem_sdiff.mp hy).1) (hN _ (Finset.mem_sdiff.mp hz).1)
      (hI _ (Finset.mem_sdiff.mp hy).1 _ (Finset.mem_sdiff.mp hz).1)
      (labels y hy).2 (he.symm ▸ (labels z hz).2)
  have hcard : B.card ≤ 2 := by
    let T : Finset (Fin 5) := {i+1,i+4}
    have c : B.card ≤ T.card := Finset.card_le_card_of_injOn rho
      (fun y hy => by simpa [T] using (pent_neighbors _ _).mp (labels y hy).1) hinj
    exact c.trans ((Finset.card_insert_le _ _).trans (by simp))
  have hB : B.card + (A ∩ F.singleSite i).card = A.card := Finset.card_sdiff_add_card_inter A (F.singleSite i)
  have hI := Finset.card_le_card (show A ∩ F.singleSite i ⊆ F.singleSite i from Finset.inter_subset_right)
  omega

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private noncomputable def oma133_PentagonBudget133_charge (x : V) : ℕ := by
  classical
  exact ∑ i : Fin 5, if x = F.c i then (F.singleSite i).card else 0

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private noncomputable def oma133_PentagonBudget133_cycleSet : Finset V := by
  classical
  exact Finset.univ.image F.c

end PentagonFrame
end Graffiti133Pentagon

end OMA133_PentagonBudget133

section OMA133_ThirdBand133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133Pentagon Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

end Graffiti133Revisit

end OMA133_ThirdBand133

section OMA133_MoreBands133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133Pentagon Finset
open scoped BigOperators
variable {V : Type*} [Fintype V]

end Graffiti133Revisit

end OMA133_MoreBands133

section OMA133_PentagonEar133

namespace Graffiti133Pentagon
namespace PentagonFrame
open SimpleGraph Graffiti133 Graffiti133Revisit Finset

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private def oma133_PentagonEar133_TypeContact (t : Fin 10) (i : Fin 5) : Prop :=
  if h : t.val < 5 then i = (⟨t.val,h⟩ : Fin 5)
  else i = (⟨t.val-5,by have := t.isLt; omega⟩ : Fin 5) ∨
    i = (⟨t.val-5,by have := t.isLt; omega⟩ : Fin 5) + 1
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private noncomputable instance (t : Fin 10) : DecidablePred (oma133_PentagonEar133_TypeContact t) := by
  intro i
  unfold oma133_PentagonEar133_TypeContact
  split <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private def oma133_PentagonEar133_RootContact (t : Fin 10) (d : Bool) (q : Fin 8) (i : Fin 5) : Prop :=
  if q = 5 then i = 0 else if q = 6 then i = 2 ∨ (d = true ∧ i = 3)
  else oma133_PentagonEar133_TypeContact t i
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private noncomputable instance (t : Fin 10) (d : Bool) (q : Fin 8) :
    DecidablePred (oma133_PentagonEar133_RootContact t d q) := by
  intro i
  unfold oma133_PentagonEar133_RootContact
  split
  · infer_instance
  · split <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private def earRel (t : Fin 10) (d a b : Bool) (x y : Fin 8) : Prop :=
  if hx : x.val < 5 then
    if hy : y.val < 5 then pent ⟨x.val,hx⟩ ⟨y.val,hy⟩
    else oma133_PentagonEar133_RootContact t d y ⟨x.val,hx⟩
  else if hy : y.val < 5 then oma133_PentagonEar133_RootContact t d x ⟨y.val,hy⟩
  else ((x = 5 ∧ y = 6) ∨ (x = 6 ∧ y = 5)) ∨
    (a = true ∧ ((x = 5 ∧ y = 7) ∨ (x = 7 ∧ y = 5))) ∨
    (b = true ∧ ((x = 6 ∧ y = 7) ∨ (x = 7 ∧ y = 6)))
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private noncomputable instance (t : Fin 10) (d a b : Bool) : DecidableRel (earRel t d a b) := by
  intro i j
  unfold earRel
  split <;> split <;> infer_instance

private inductive EarCert
| near
| via (i : Fin 8)
| four (i j a b : Fin 8)
| path (p : Fin 6 → Fin 8)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private def oma133_PentagonEar133_certTrue (R : Fin 8 → Fin 8 → Prop) : EarCert → Prop
| .near => R 0 7
| .via i => R 0 i ∧ R i 7
| .four i j a b => i ≠ j ∧ a ≠ b ∧ R i a ∧ R j a ∧ R i b ∧ R j b
| .path p => (∀ i j, p i = p j → i = j) ∧ ∀ i j, i < j → (R (p i) (p j) ↔ i.val+1=j.val)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private noncomputable instance (R : Fin 8 → Fin 8 → Prop) [DecidableRel R] :
    DecidablePred (oma133_PentagonEar133_certTrue R) := by
  intro e
  cases e <;> unfold oma133_PentagonEar133_certTrue <;> infer_instance

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : PentagonFrame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private lemma oma133_PentagonEar133_outside_cases : ∀ i : Fin 8, ¬ i.val < 5 → i = 5 ∨ i = 6 ∨ i = 7 := by decide

end PentagonFrame
end Graffiti133Pentagon

end OMA133_PentagonEar133

section OMA133_PentagonSparse133

namespace Graffiti133Pentagon
namespace PentagonFrame
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : PentagonFrame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private def refl (a : Fin 5) : Fin 5 ≃ Fin 5 where
  toFun i := a-i
  invFun i := a-i
  left_inv := ((by decide : ∀ a i : Fin 5, a-(a-i)=i) a)
  right_inv := ((by decide : ∀ a i : Fin 5, a-(a-i)=i) a)

end PentagonFrame
end Graffiti133Pentagon

end OMA133_PentagonSparse133

section OMA133_StrictDensity133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133RevisitSix Finset
open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

end Graffiti133Revisit

end OMA133_StrictDensity133

section OMA133_UnroundedBand133

namespace Graffiti133Pentagon
namespace PentagonFrame
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : PentagonFrame G)

end PentagonFrame
end Graffiti133Pentagon

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133Pentagon
variable {V : Type*} [Fintype V]

end Graffiti133Revisit

end OMA133_UnroundedBand133

section OMA133_Remaining133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133

variable {V : Type*} [Fintype V]

end Graffiti133Revisit

end OMA133_Remaining133

section OMA133_SeventhNoFive133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133
variable {V : Type*} [Fintype V]

end Graffiti133Revisit

end OMA133_SeventhNoFive133

section OMA133_NoFiveHoles133

namespace Graffiti133NoFive
open SimpleGraph Graffiti133 Graffiti133Revisit Finset

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def Cyclic {n : ℕ} (i j : Fin n) : Prop :=
  i.val+1=j.val ∨ j.val+1=i.val ∨
    (i.val=0 ∧ j.val+1=n) ∨ (j.val=0 ∧ i.val+1=n)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
instance {n : ℕ} : DecidableRel (@Cyclic n) := by
  intro i j
  unfold Cyclic
  infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem cyclic_symm {n : ℕ} (i j : Fin n) : Cyclic i j ↔ Cyclic j i := by
  unfold Cyclic
  tauto

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def Outside {n : ℕ} (c : Fin n → V) (x : V) : Prop := ∀ i, x ≠ c i

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
structure Hole (G : SimpleGraph V) (n : ℕ) where
  c : Fin n → V
  inj : Function.Injective c
  adj : ∀ i j, G.Adj (c i) (c j) ↔ Cyclic i j

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem close_induced_path {m : ℕ} (hm : 3 ≤ m) {p : Fin m → V}
    (hp : InducedPath G p) (w : V) (hw : ∀ i, w ≠ p i)
    (h0 : G.Adj w (p ⟨0,by omega⟩)) (hLast : G.Adj w (p ⟨m-1,by omega⟩))
    (hmiddle : ∀ i : Fin m, 0 < i.val → i.val+1 < m → ¬G.Adj w (p i)) :
    Nonempty (Hole G (m+1)) := by
  let c (i : Fin (m+1)) := if hi : i.val < m then p ⟨i.val,hi⟩ else w
  have cP (i : Fin m) : c i.castSucc = p i := by simp [c,i.isLt]
  have cW : c (Fin.last m) = w := by simp [c]
  have other (i : Fin (m+1)) : (∃ a : Fin m, i = a.castSucc) ∨ i = Fin.last m := by
    by_cases hi : i.val < m
    · exact Or.inl ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
    · exact Or.inr (Fin.ext (by change i.val = m; have := i.isLt; omega))
  have inj : Function.Injective c := by
    intro i j he
    rcases other i with ⟨a,rfl⟩ | rfl <;> rcases other j with ⟨b,rfl⟩ | rfl
    · rw [cP,cP] at he
      exact congrArg Fin.castSucc (hp.1 he)
    · rw [cP,cW] at he
      exact (hw _ he.symm).elim
    · rw [cW,cP] at he
      exact (hw _ he).elim
    · rfl
  have interior (a b : Fin m) : G.Adj (p a) (p b) ↔ Cyclic a.castSucc b.castSucc := by
    have aa := a.isLt
    have bb := b.isLt
    change G.Adj (p a) (p b) ↔ a.val+1=b.val ∨ b.val+1=a.val ∨
      (a.val=0 ∧ b.val+1=m+1) ∨ (b.val=0 ∧ a.val+1=m+1)
    rcases lt_trichotomy a b with lt | e | gt
    · rw [hp.2 a b lt]
      change a.val < b.val at lt
      omega
    · subst b
      simp [G.loopless.irrefl]
      omega
    · rw [G.adj_comm,hp.2 b a gt]
      change b.val < a.val at gt
      omega
  have ext (i : Fin m) : G.Adj (p i) w ↔ Cyclic i.castSucc (Fin.last m) := by
    change G.Adj (p i) w ↔ i.val+1=m ∨ m+1=i.val ∨
      (i.val=0 ∧ m+1=m+1) ∨ (m=0 ∧ i.val+1=m+1)
    constructor
    · intro e
      have := i.isLt
      by_cases h : i.val = 0
      · exact Or.inr (Or.inr (Or.inl ⟨h,rfl⟩))
      · by_cases e' : i.val+1=m
        · exact Or.inl e'
        · exact (hmiddle i (by omega) (by omega) e.symm).elim
    · intro h
      have hi := i.isLt
      have h' : i.val=0 ∨ i.val=m-1 := by omega
      rcases h' with h' | h'
      · have eq : i = ⟨0,by omega⟩ := Fin.ext h'
        exact eq ▸ h0.symm
      · have eq : i = ⟨m-1,by omega⟩ := Fin.ext h'
        exact eq ▸ hLast.symm
  refine ⟨⟨c,inj,?_⟩⟩
  intro i j
  rcases other i with ⟨a,rfl⟩ | rfl <;> rcases other j with ⟨b,rfl⟩ | rfl
  · rw [cP,cP]
    exact interior a b
  · rw [cP,cW]
    exact ext a
  · rw [cW,cP,G.adj_comm,cyclic_symm]
    exact ext b
  · rw [cW]
    have hg : ¬ Cyclic (Fin.last m) (Fin.last m) := by
      change ¬(m+1=m ∨ m+1=m ∨ (m=0 ∧ m+1=m+1) ∨ (m=0 ∧ m+1=m+1))
      omega
    exact iff_of_false (G.loopless.irrefl _) hg

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def SpokeRel {n : ℕ} (b : Fin n → Bool) (i j : Fin (n+1)) : Prop :=
  if hi : i.val < n then
    if hj : j.val < n then Cyclic ⟨i.val,hi⟩ ⟨j.val,hj⟩ else b ⟨i.val,hi⟩=true
  else if hj : j.val < n then b ⟨j.val,hj⟩=true else False

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
instance {n : ℕ} (b : Fin n → Bool) : DecidableRel (SpokeRel b) := by
  intro i j
  unfold SpokeRel
  split <;> split <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem lift_spoke {n : ℕ} (hn : 0 < n) (H : Hole G n)
    (x : V) (hx : Outside H.c x) {b : Fin n → Bool}
    (hb : ∀ i, b i = true ↔ G.Adj x (H.c i))
    (path : Fin n → Fin (n+1)) (inj : Function.Injective path)
    (hs : ∀ i j : Fin n, i < j → (SpokeRel b (path i) (path j) ↔ i.val+1=j.val))
    (head : path ⟨0,hn⟩ = Fin.last n)
    (tail : ∀ i, 0 < i.val → (path i).val < n) :
    ∃ p : Fin n → V, InducedPath G p ∧ p ⟨0,hn⟩ = x ∧
      ∀ i, 0 < i.val → ∃ j, p i = H.c j := by
  let g (r : Fin (n+1)) : V := if hr : r.val < n then H.c ⟨r.val,hr⟩ else x
  have gLast : g (Fin.last n) = x := by simp [g]
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < n <;> by_cases hB : b.val < n
    · have he := H.inj (show H.c ⟨a.val,hA⟩ = H.c ⟨b.val,hB⟩ by
        simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun z : Fin n => z.val) he)
    · exact False.elim (hx ⟨a.val,hA⟩ (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm))
    · exact False.elim (hx ⟨b.val,hB⟩ (by simpa only [g,dif_neg hA,dif_pos hB] using eq))
    · apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
  have hrel (a q : Fin (n+1)) : G.Adj (g a) (g q) ↔ SpokeRel b a q := by
    by_cases hA : a.val < n <;> by_cases hQ : q.val < n
    · simpa only [g,SpokeRel,dif_pos hA,dif_pos hQ] using H.adj ⟨a.val,hA⟩ ⟨q.val,hQ⟩
    · simpa only [g,SpokeRel,dif_pos hA,dif_neg hQ,G.adj_comm] using (hb ⟨a.val,hA⟩).symm
    · simpa only [g,SpokeRel,dif_neg hA,dif_pos hQ] using (hb ⟨q.val,hQ⟩).symm
    · simp [g,SpokeRel,hA,hQ,G.loopless.irrefl]
  refine ⟨g ∘ path,⟨ginj.comp inj,fun a q he => (hrel _ _).trans (hs a q he)⟩,
    ?_,?_⟩
  · change g (path ⟨0,hn⟩) = x
    rw [head,gLast]
  · intro i hi
    exact ⟨⟨_,tail i hi⟩,dif_pos (tail i hi)⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma chain6 : ∀ i : Fin 6, Cyclic i (i+1) ∧
    Cyclic (i+1) (i+2) ∧ Cyclic (i+2) (i+3) := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma chain7 : ∀ i : Fin 7, Cyclic i (i+1) ∧
    Cyclic (i+1) (i+2) ∧ Cyclic (i+2) (i+3) := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma inds6 : ∀ i : Fin 6, i≠i+2 ∧ [i,i+1,i+2,i+3].Nodup := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma inds7 : ∀ i : Fin 7, i≠i+2 ∧ [i,i+1,i+2,i+3].Nodup := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem no_spoke_offset {n : ℕ} [NeZero n]
    (hn : n = 6 ∨ n = 7) (H : Hole G n) (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (x : V) (hx : Outside H.c x) (i : Fin n) (hi : G.Adj x (H.c i)) :
    ¬G.Adj x (H.c (i+2)) ∧ ¬G.Adj x (H.c (i+3)) := by
  have chain (i : Fin n) : Cyclic i (i+1) ∧ Cyclic (i+1) (i+2) ∧ Cyclic (i+2) (i+3) := by
    rcases hn with rfl | rfl
    · exact chain6 i
    · exact chain7 i
  have steps : i ≠ i+2 ∧ [i,i+1,i+2,i+3].Nodup := by
    rcases hn with rfl | rfl
    · exact inds6 i
    · exact inds7 i
  obtain ⟨e1,e2,e3⟩ := chain i
  constructor
  · intro e
    exact hx _ (h4 (H.c i) (H.c (i+2)) x (H.c (i+1))
      (fun eq => steps.1 (H.inj eq)) hi.symm e.symm
      ((H.adj _ _).mpr e1) ((H.adj _ _).mpr e2).symm)
  · intro e
    have nod : [x,H.c i,H.c (i+1),H.c (i+2),H.c (i+3)].Nodup := by
      apply List.nodup_cons.mpr
      exact ⟨by simp [hx i,hx (i+1),hx (i+2),hx (i+3)],by simpa using steps.2.map H.inj⟩
    exact h5 _ _ _ _ _ nod hi ((H.adj _ _).mpr e1) ((H.adj _ _).mpr e2)
      ((H.adj _ _).mpr e3) e.symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def spokePath6 (i : Fin 6) (positive : Bool) : Fin 6 → Fin 7 :=
  ![6, i.castSucc, (i + (if positive then 1 else 5)).castSucc,
    (i + (if positive then 2 else 4)).castSucc, (i + 3).castSucc,
    (i + (if positive then 4 else 2)).castSucc]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def spokePath7 (i : Fin 7) (positive : Bool) : Fin 7 → Fin 8 :=
  ![7, i.castSucc, (i + (if positive then 1 else 6)).castSucc,
    (i + (if positive then 2 else 5)).castSucc, (i + (if positive then 3 else 4)).castSucc,
    (i + (if positive then 4 else 3)).castSucc, (i + (if positive then 5 else 2)).castSucc]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma spoke6 : ∀ b : Fin 6 → Bool,
    (∀ i, b i = true → b (i+2) = false ∧ b (i+3) = false) → (∃ i, b i = true) →
    ∃ i pos,
      (∀ a c : Fin 6, spokePath6 i pos a = spokePath6 i pos c → a=c) ∧
      (∀ a c : Fin 6, a<c → (SpokeRel b (spokePath6 i pos a) (spokePath6 i pos c) ↔ a.val+1=c.val)) ∧
      (∀ a : Fin 6, 0<a.val → (spokePath6 i pos a).val < 6) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma spoke7 : ∀ b : Fin 7 → Bool,
    (∀ i, b i = true → b (i+2) = false ∧ b (i+3) = false) → (∃ i, b i = true) →
    ∃ i pos,
      (∀ a c : Fin 7, spokePath7 i pos a = spokePath7 i pos c → a=c) ∧
      (∀ a c : Fin 7, a<c → (SpokeRel b (spokePath7 i pos a) (spokePath7 i pos c) ↔ a.val+1=c.val)) ∧
      (∀ a : Fin 7, 0<a.val → (spokePath7 i pos a).val < 7) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem extend_hole_no_five {n : ℕ} [NeZero n]
    (hn : n = 6 ∨ n = 7) (H : Hole G n) (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (x : V) (hx : Outside H.c x) (ha : ∃ i, G.Adj x (H.c i)) :
    ∃ p : Fin n → V, InducedPath G p ∧ p ⟨0,NeZero.pos n⟩ = x ∧
      ∀ i, 0 < i.val → ∃ j, p i = H.c j := by
  classical
  let b : Fin n → Bool := fun i => decide (G.Adj x (H.c i))
  have bh (i : Fin n) : b i=true ↔ G.Adj x (H.c i) := by simp [b]
  have hs (i : Fin n) (hi : b i=true) : b (i+2)=false ∧ b (i+3)=false := by
    have hh := no_spoke_offset hn H h4 h5 x hx i ((bh i).mp hi)
    constructor
    · cases he : b (i+2)
      · rfl
      · exact (hh.1 ((bh _).mp he)).elim
    · cases he : b (i+3)
      · rfl
      · exact (hh.2 ((bh _).mp he)).elim
  have some : ∃ i, b i = true := by
    obtain ⟨i,hi⟩ := ha
    exact ⟨i,(bh _).mpr hi⟩
  rcases hn with rfl | rfl
  · obtain ⟨i,pos,inj,e,tail⟩ := spoke6 b hs some
    exact lift_spoke (by decide) H x hx bh (spokePath6 i pos) inj e rfl tail
  · obtain ⟨i,pos,inj,e,tail⟩ := spoke7 b hs some
    exact lift_spoke (by decide) H x hx bh (spokePath7 i pos) inj e rfl tail

end Graffiti133NoFive

end OMA133_NoFiveHoles133

section OMA133_NoFiveHexDensity133

namespace Graffiti133NoFive
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private def Front {n : ℕ} (H : Hole G n) (x : V) : Prop :=
  Outside H.c x → ∃ i, G.Adj x (H.c i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
theorem hex_dominates (H : Hole G 6) (hc : G.Connected)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (no7 : ¬∃ f : Fin 7 → V, InducedPath G f) : ∀ x, Front H x := by
  classical
  have step (u v : V) (e : G.Adj u v) (hu : Front H u) : Front H v := by
    intro hv
    by_cases uu : Outside H.c u
    · apply Classical.byContradiction
      intro none
      obtain ⟨p,hp,h0,htail⟩ := extend_hole_no_five (Or.inl rfl) H h4 h5 u uu (hu uu)
      change p (0 : Fin 6) = u at h0
      have hn : ∀ i, v ≠ p i := by
        intro i he
        by_cases hh : i.val = 0
        · have eq : i = 0 := Fin.ext hh
          rw [eq,h0] at he
          exact e.ne he.symm
        · obtain ⟨j,hj⟩ := htail i (Nat.pos_of_ne_zero hh)
          exact hv j (he.trans hj)
      have ha : G.Adj v (p 0) := h0.symm ▸ e.symm
      have hn' (i : Fin 6) (hi : 0 < i.val) : ¬ G.Adj v (p i) := by
        intro er
        obtain ⟨j,hj⟩ := htail i hi
        exact none ⟨j,hj ▸ er⟩
      obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp v hn ha hn'
      exact no7 ⟨q,hq⟩
    · have h : ∃ i, u = H.c i := by
        apply Classical.byContradiction
        intro bad
        exact uu (fun i eq => bad ⟨i,eq⟩)
      obtain ⟨i,hi⟩ := h
      exact ⟨i,hi ▸ e.symm⟩
  intro x
  obtain ⟨p⟩ := hc (H.c 0) x
  have walkprop {a b : V} (p : G.Walk a b) (ha : Front H a) : Front H b := by
    induction p with
    | nil => exact ha
    | cons e q ih => exact ih (step _ _ e ha)
  exact walkprop p (fun h => (h 0 rfl).elim)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
theorem heptagon_spans (H : Hole G 7) (hc : G.Connected)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (no7 : ¬∃ f : Fin 7 → V, InducedPath G f) : Function.Surjective H.c := by
  classical
  have next (u v : V) (e : G.Adj u v) (hu : ∃ i, H.c i = u) : ∃ i, H.c i = v := by
    obtain ⟨i,rfl⟩ := hu
    apply Classical.byContradiction
    intro bad
    obtain ⟨p,hp,_,_⟩ := extend_hole_no_five (Or.inr rfl) H h4 h5 v
      (fun j eq => bad ⟨j,eq.symm⟩) ⟨i,e.symm⟩
    exact no7 ⟨p,hp⟩
  intro x
  obtain ⟨p⟩ := hc (H.c 0) x
  have walkprop {a b : V} (p : G.Walk a b) (ha : ∃ i, H.c i = a) : ∃ i, H.c i = b := by
    induction p with
    | nil => exact ha
    | cons e q ih => exact ih (next _ _ e ha)
  exact walkprop p ⟨0,rfl⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma oma133_NoFiveHexDensity133_cyc6_sites : ∀ i j : Fin 6, Cyclic i j ↔ j=i+1 ∨ j=i+5 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma cyc7_sites : ∀ i j : Fin 7, Cyclic i j ↔ j=i+1 ∨ j=i+6 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma oma133_NoFiveHexDensity133_cyc6_ne : ∀ i j : Fin 6, Cyclic i j → i≠j := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private def oma133_NoFiveHexDensity133_One (H : Hole G 6) (x : V) (i : Fin 6) : Prop :=
  Outside H.c x ∧ ∀ j, G.Adj x (H.c j) ↔ j = i
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private def oma133_NoFiveHexDensity133_Two (H : Hole G 6) (x : V) (i : Fin 6) : Prop :=
  Outside H.c x ∧ ∀ j, G.Adj x (H.c j) ↔ j = i ∨ j=i+1

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma classifyMask : ∀ b : Fin 6 → Bool,
    (∀ i, b i = true → b (i+2)=false ∧ b (i+3)=false) → (∃ i,b i=true) →
    (∃ i, ∀ j, b j=true ↔ j=i) ∨ (∃ i, ∀ j, b j=true ↔ j=i ∨ j=i+1) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem classify_hex (H : Hole G 6) (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (dom : ∀ x, Front H x) (x : V) (hx : Outside H.c x) :
    (∃ i, oma133_NoFiveHexDensity133_One H x i) ∨ (∃ i, oma133_NoFiveHexDensity133_Two H x i) := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (H.c i))
  have bt (i : Fin 6) : b i=true ↔ G.Adj x (H.c i) := by simp [b]
  have sep (i : Fin 6) (h : b i=true) : b (i+2)=false ∧ b (i+3)=false := by
    have hN := no_spoke_offset (Or.inl rfl) H h4 h5 x hx i ((bt i).mp h)
    constructor
    · cases eq : b (i+2)
      · rfl
      · exact (hN.1 ((bt _).mp eq)).elim
    · cases eq : b (i+3)
      · rfl
      · exact (hN.2 ((bt _).mp eq)).elim
  obtain ⟨i,hi⟩ := dom x hx
  rcases classifyMask b sep ⟨i,(bt i).mpr hi⟩ with ⟨j,hj⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨j,hx,fun k => (bt k).symm.trans (hj k)⟩
  · exact Or.inr ⟨j,hx,fun k => (bt k).symm.trans (hj k)⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private def cycNear2 (i j : Fin 6) : Prop := j = i+2 ∨ i = j+2
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private instance : DecidableRel cycNear2 := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma mid6 : ∀ i j : Fin 6, cycNear2 i j →
    ∃ k, k≠i ∧ k≠j ∧ i≠j ∧ Cyclic i k ∧ Cyclic k j := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem forbidAdjacentSite (H : Hole G 6) (h4 : FourCycleFree G) {x y : V}
    (hx : Outside H.c x) (hy : Outside H.c y) (e : G.Adj x y)
    {i j : Fin 6} (xi : G.Adj x (H.c i)) (yj : G.Adj y (H.c j)) :
    ¬Cyclic i j := by
  intro h
  exact hy i (h4 x (H.c j) y (H.c i) (hx j) e yj.symm xi ((H.adj _ _).mpr h).symm)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem forbidNear2Site (H : Hole G 6) (h5 : NoSimpleFive133 G) {x y : V}
    (hx : Outside H.c x) (hy : Outside H.c y) (e : G.Adj x y)
    {i j : Fin 6} (xi : G.Adj x (H.c i)) (yj : G.Adj y (H.c j)) :
    ¬cycNear2 i j := by
  intro h
  obtain ⟨k,ki,kj,ij,e1,e2⟩ := mid6 i j h
  have hN : [x,y,H.c j,H.c k,H.c i].Nodup := by
    simp [e.ne,hx j,hx k,hx i,hy j,hy k,hy i,H.inj.ne kj.symm,H.inj.ne ij.symm,H.inj.ne ki]
  exact h5 _ _ _ _ _ hN e yj ((H.adj _ _).mpr e2).symm ((H.adj _ _).mpr e1).symm xi.symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma remainingContact : ∀ i j : Fin 6, ¬Cyclic i j → ¬cycNear2 i j →
    j=i ∨ j=i+3 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma impossibleDouble : ∀ i j : Fin 6,
    (j=i ∨ j=i+3) → (j=i+1 ∨ j=(i+1)+3) → False := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem seat_available (H : Hole G 6) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) {x y : V} (hx : Outside H.c x) (hy : Outside H.c y)
    (e : G.Adj x y) {i j : Fin 6} (xi : G.Adj x (H.c i)) (yj : G.Adj y (H.c j)) :
    j=i ∨ j=i+3 :=
  remainingContact i j (forbidAdjacentSite H h4 hx hy e xi yj)
    (forbidNear2Site H h5 hx hy e xi yj)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private def oma133_NoFiveHexDensity133_Stamp (H : Hole G 6) (y : V) (j : Fin 6) : Prop :=
  y = H.c j ∨ (Outside H.c y ∧ G.Adj y (H.c j))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem oma133_NoFiveHexDensity133_stamp_exists (H : Hole G 6) (dom : ∀ x, Front H x) (y : V) :
    ∃ j, oma133_NoFiveHexDensity133_Stamp H y j := by
  by_cases h : Outside H.c y
  · obtain ⟨j,hj⟩ := dom y h
    exact ⟨j,Or.inr ⟨h,hj⟩⟩
  · apply Classical.byContradiction
    intro no
    exact h (fun j eq => no ⟨j,Or.inl eq⟩)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem stamp_single (H : Hole G 6) (h4 : FourCycleFree G)
    {x y z : V} {j : Fin 6} (hne : x ≠ H.c j)
    (ey : G.Adj x y) (ez : G.Adj x z) (no : ¬G.Adj y z)
    (sy : oma133_NoFiveHexDensity133_Stamp H y j) (sz : oma133_NoFiveHexDensity133_Stamp H z j) : y = z := by
  rcases sy with sy | ⟨hy,e1⟩ <;> rcases sz with sz | ⟨hz,e2⟩
  · exact sy.trans sz.symm
  · exact (no (sy.symm ▸ e2.symm)).elim
  · exact (no (sz.symm ▸ e1)).elim
  · exact h4 x (H.c j) y z hne ey e1.symm ez e2.symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem local_single_bound (H : Hole G 6) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (dom : ∀ x, Front H x) {x : V} {i : Fin 6}
    (hx : oma133_NoFiveHexDensity133_One H x i) : localIndependence G x ≤ 2 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let f (w : V) := Classical.choose (oma133_NoFiveHexDensity133_stamp_exists H dom w)
  have spec (w : V) : oma133_NoFiveHexDensity133_Stamp H w (f w) := Classical.choose_spec (oma133_NoFiveHexDensity133_stamp_exists H dom w)
  let seats : Finset (Fin 6) := {i,i+3}
  have hf (w : V) (hw : w ∈ A) : f w ∈ seats := by
    rcases spec w with eq | ⟨hw',hW⟩
    · have : f w = i := (hx.2 _).mp (eq ▸ hN w hw)
      simp [seats,this]
    · have := seat_available H h4 h5 hx.1 hw' (hN w hw) ((hx.2 i).mpr rfl) hW
      simpa [seats] using this
  have inj : Set.InjOn f (↑A : Set V) := by
    intro a ha b hb he
    exact stamp_single H h4 (hx.1 (f a)) (hN _ ha) (hN _ hb) (hI _ ha _ hb)
      (spec a) (he.symm ▸ spec b)
  exact (Finset.card_le_card_of_injOn f hf inj).trans ((Finset.card_insert_le _ _).trans (by simp))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem oma133_NoFiveHexDensity133_local_double_bound (H : Hole G 6) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (dom : ∀ x, Front H x) {x : V} {i : Fin 6}
    (hx : oma133_NoFiveHexDensity133_Two H x i) : localIndependence G x ≤ 1 := by
  classical
  have hh (y : V) (e : G.Adj x y) : y = H.c i ∨ y = H.c (i+1) := by
    by_cases out : Outside H.c y
    · obtain ⟨j,hj⟩ := dom y out
      have e1 := seat_available H h4 h5 hx.1 out e ((hx.2 _).mpr (Or.inl rfl)) hj
      have e2 := seat_available H h4 h5 hx.1 out e ((hx.2 _).mpr (Or.inr rfl)) hj
      exact (impossibleDouble i j e1 e2).elim
    · obtain ⟨j,hj⟩ : ∃ j, y = H.c j := by
        apply Classical.byContradiction
        intro no
        exact out fun j eq => no ⟨j,eq⟩
      rcases (hx.2 _).mp (hj ▸ e) with a | b
      · exact Or.inl (hj.trans (congrArg H.c a))
      · exact Or.inr (hj.trans (congrArg H.c b))
  have adj : G.Adj (H.c i) (H.c (i+1)) :=
    (H.adj _ _).mpr ((oma133_NoFiveHexDensity133_cyc6_sites _ _).mpr (Or.inl rfl))
  apply Finset.sup_le_iff.mpr
  intro A hA
  apply Finset.card_le_one.mpr
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  intro y hy z hz
  rcases hh y (hN _ hy) with e | e <;> rcases hh z (hN _ hz) with f | f
  · exact e.trans f.symm
  · exact (hI _ hy _ hz (e.symm ▸ f.symm ▸ adj)).elim
  · exact (hI _ hy _ hz (e.symm ▸ f.symm ▸ adj.symm)).elim
  · exact e.trans f.symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private noncomputable def oma133_NoFiveHexDensity133_singleSite (H : Hole G 6) (i : Fin 6) : Finset V := by
  classical exact Finset.univ.filter (fun x => oma133_NoFiveHexDensity133_One H x i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma oma133_NoFiveHexDensity133_site_mem (H : Hole G 6) {i : Fin 6} {x : V} :
    x ∈ oma133_NoFiveHexDensity133_singleSite H i ↔ oma133_NoFiveHexDensity133_One H x i := by
  classical simp [oma133_NoFiveHexDensity133_singleSite]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem oma133_NoFiveHexDensity133_local_cycle_bound (H : Hole G 6) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (dom : ∀ x, Front H x) (i : Fin 6) :
    localIndependence G (H.c i) ≤ 2 + (oma133_NoFiveHexDensity133_singleSite H i).card := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let B := A \ oma133_NoFiveHexDensity133_singleSite H i
  let seats : Finset (Fin 6) := {i+1,i+5}
  have label (w : V) (hw : w ∈ B) : ∃ j, Cyclic i j ∧ oma133_NoFiveHexDensity133_Stamp H w j := by
    have e := hN w (Finset.mem_sdiff.mp hw).1
    by_cases out : Outside H.c w
    · rcases classify_hex H h4 h5 dom w out with ⟨j,hj⟩ | ⟨j,hj⟩
      · have he := (hj.2 i).mp e.symm
        exact ((Finset.mem_sdiff.mp hw).2 ((oma133_NoFiveHexDensity133_site_mem H).mpr (he.symm ▸ hj))).elim
      · rcases (hj.2 i).mp e.symm with he | he
        · have m : Cyclic i (j+1) := (oma133_NoFiveHexDensity133_cyc6_sites _ _).mpr (Or.inl (by rw [he]))
          exact ⟨j+1,m,Or.inr ⟨out,(hj.2 _).mpr (Or.inr rfl)⟩⟩
        · have m : Cyclic i j := (cyclic_symm _ _).mpr ((oma133_NoFiveHexDensity133_cyc6_sites _ _).mpr (Or.inl he))
          exact ⟨j,m,Or.inr ⟨out,(hj.2 _).mpr (Or.inl rfl)⟩⟩
    · obtain ⟨j,hj⟩ : ∃ j, w = H.c j := by
        apply Classical.byContradiction
        intro no
        exact out (fun j eq => no ⟨j,eq⟩)
      exact ⟨j,(H.adj _ _).mp (hj ▸ e),Or.inl hj⟩
  let f (w : V) := if hw : w ∈ B then Classical.choose (label w hw) else i
  have fs (w : V) (hw : w ∈ B) : Cyclic i (f w) ∧ oma133_NoFiveHexDensity133_Stamp H w (f w) := by
    simpa only [f,dif_pos hw] using Classical.choose_spec (label w hw)
  have hf (w : V) (hw : w ∈ B) : f w ∈ seats := by
    simpa [seats] using (oma133_NoFiveHexDensity133_cyc6_sites _ _).mp (fs w hw).1
  have inj : Set.InjOn f (↑B : Set V) := by
    intro y hy z hz e
    have hyA := (Finset.mem_sdiff.mp hy).1
    have hzA := (Finset.mem_sdiff.mp hz).1
    have ne : H.c i ≠ H.c (f y) := H.inj.ne (oma133_NoFiveHexDensity133_cyc6_ne _ _ (fs y hy).1)
    exact stamp_single H h4 ne (hN _ hyA) (hN _ hzA) (hI _ hyA _ hzA)
      (fs y hy).2 (e.symm ▸ (fs z hz).2)
  have cb : B.card ≤ 2 := (Finset.card_le_card_of_injOn f hf inj).trans
    ((Finset.card_insert_le _ _).trans (by simp))
  have hInt := Finset.card_le_card (show A ∩ oma133_NoFiveHexDensity133_singleSite H i ⊆ oma133_NoFiveHexDensity133_singleSite H i from Finset.inter_subset_right)
  have hC : B.card + (A ∩ oma133_NoFiveHexDensity133_singleSite H i).card = A.card := Finset.card_sdiff_add_card_inter A _
  omega

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private noncomputable def oma133_NoFiveHexDensity133_singles (H : Hole G 6) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => ∃ i, oma133_NoFiveHexDensity133_One H x i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma oma133_NoFiveHexDensity133_singles_iff (H : Hole G 6) (x : V) :
    x ∈ oma133_NoFiveHexDensity133_singles H ↔ ∃ i, oma133_NoFiveHexDensity133_One H x i := by classical simp [oma133_NoFiveHexDensity133_singles]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private noncomputable def oma133_NoFiveHexDensity133_core (H : Hole G 6) : Finset V := by
  classical
  exact (Finset.univ : Finset (Fin 6)).image H.c

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private noncomputable def oma133_NoFiveHexDensity133_fSite (H : Hole G 6) (x : V) : Fin 6 := by
  classical exact if h : ∃ i, oma133_NoFiveHexDensity133_One H x i then Classical.choose h else 0

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem oma133_NoFiveHexDensity133_sum_sites (H : Hole G 6) : (∑ i, (oma133_NoFiveHexDensity133_singleSite H i).card) = (oma133_NoFiveHexDensity133_singles H).card := by
  classical
  have fiber (i : Fin 6) : oma133_NoFiveHexDensity133_singleSite H i = (oma133_NoFiveHexDensity133_singles H).filter (fun x => oma133_NoFiveHexDensity133_fSite H x = i) := by
    ext x
    rw [oma133_NoFiveHexDensity133_site_mem,Finset.mem_filter]
    have fvalid (h : x ∈ oma133_NoFiveHexDensity133_singles H) : oma133_NoFiveHexDensity133_One H x (oma133_NoFiveHexDensity133_fSite H x) := by
      have q := (oma133_NoFiveHexDensity133_singles_iff H x).mp h
      unfold oma133_NoFiveHexDensity133_fSite
      rw [dif_pos q]
      exact Classical.choose_spec q
    refine ⟨?_,fun ⟨h,he⟩ => he ▸ fvalid h⟩
    intro h
    have hS := (oma133_NoFiveHexDensity133_singles_iff H x).mpr ⟨i,h⟩
    exact ⟨hS,(h.2 _).mp (((fvalid hS).2 _).mpr rfl)⟩
  simpa only [fiber] using
    (Finset.card_eq_sum_card_fiberwise (s:=oma133_NoFiveHexDensity133_singles H) (t:=Finset.univ)
      (f:=oma133_NoFiveHexDensity133_fSite H) (fun _ _ => Finset.mem_univ _)).symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private noncomputable def oma133_NoFiveHexDensity133_charge (H : Hole G 6) (x : V) : ℕ := by
  classical exact ∑ i : Fin 6, if x = H.c i then (oma133_NoFiveHexDensity133_singleSite H i).card else 0

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private noncomputable def fee (H : Hole G 6) (x : V) : ℕ := by
  classical exact if x ∈ oma133_NoFiveHexDensity133_core H ∪ oma133_NoFiveHexDensity133_singles H then 1 else 0

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
theorem hex_budget (H : Hole G 6) (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (dom : ∀ x, Front H x) :
    (∑ x, localIndependence G x) + 6 ≤ 3 * Fintype.card V := by
  classical
  have pointwise (x : V) : localIndependence G x + fee H x ≤ 3 + oma133_NoFiveHexDensity133_charge H x := by
    by_cases out : Outside H.c x
    · have b : fee H x ≤ 1 := by
        unfold fee
        split <;> omega
      rcases classify_hex H h4 h5 dom x out with ⟨i,h⟩ | ⟨i,h⟩
      · have l := local_single_bound H h4 h5 dom h
        omega
      · have l := oma133_NoFiveHexDensity133_local_double_bound H h4 h5 dom h
        omega
    · obtain ⟨i,e⟩ : ∃ i, x = H.c i := by
        apply Classical.byContradiction
        intro no
        exact out fun j e => no ⟨j,e⟩
      have hL := oma133_NoFiveHexDensity133_local_cycle_bound H h4 h5 dom i
      rw [← e] at hL
      have hl : (oma133_NoFiveHexDensity133_singleSite H i).card ≤ oma133_NoFiveHexDensity133_charge H x := by
        have hh := Finset.single_le_sum (f := fun j : Fin 6 =>
          if x = H.c j then (oma133_NoFiveHexDensity133_singleSite H j).card else 0) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
        simpa [oma133_NoFiveHexDensity133_charge,e] using hh
      have b : fee H x ≤ 1 := by
        unfold fee
        split <;> omega
      omega
  have disj : Disjoint (oma133_NoFiveHexDensity133_core H) (oma133_NoFiveHexDensity133_singles H) := by
    apply Finset.disjoint_left.mpr
    intro x hx hs
    obtain ⟨a,_,e⟩ := Finset.mem_image.mp hx
    obtain ⟨i,hi⟩ := (oma133_NoFiveHexDensity133_singles_iff H x).mp hs
    exact hi.1 a e.symm
  have hc : (oma133_NoFiveHexDensity133_core H).card = 6 := by
    unfold oma133_NoFiveHexDensity133_core
    rw [Finset.card_image_of_injective _ H.inj]
    simp
  have hfee : (∑ x, fee H x) = 6+(oma133_NoFiveHexDensity133_singles H).card := by
    have hF : (Finset.univ : Finset V).filter (fun x => x ∈ oma133_NoFiveHexDensity133_core H ∪ oma133_NoFiveHexDensity133_singles H) = oma133_NoFiveHexDensity133_core H ∪ oma133_NoFiveHexDensity133_singles H := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    simp only [fee,Finset.sum_ite,Finset.sum_const,Finset.sum_const_zero,nsmul_eq_mul,
      Nat.cast_id,mul_one,mul_zero,add_zero,hF,Finset.card_union_of_disjoint disj,hc]
  have hcharge : (∑ x, oma133_NoFiveHexDensity133_charge H x) = (oma133_NoFiveHexDensity133_singles H).card := by
    unfold oma133_NoFiveHexDensity133_charge
    rw [Finset.sum_comm]
    simp [oma133_NoFiveHexDensity133_sum_sites H]
  have h := Finset.sum_le_sum (s:=(Finset.univ : Finset V)) (fun x _ => pointwise x)
  have hu : (∑ x, localIndependence G x) + (6+(oma133_NoFiveHexDensity133_singles H).card) ≤
      3*Fintype.card V + (oma133_NoFiveHexDensity133_singles H).card := by
    simpa [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hfee,hcharge,
      Nat.mul_comm] using h
  omega

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
theorem heptagon_budget (H : Hole G 7) (sur : Function.Surjective H.c) :
    (∑ x, localIndependence G x) ≤ 2 * Fintype.card V := by
  classical
  have atmost (x : V) : localIndependence G x ≤ 2 := by
    obtain ⟨i,rfl⟩ := sur x
    apply Finset.sup_le_iff.mpr
    intro A hA
    obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
    have hsub : A ⊆ ({H.c (i+1),H.c (i+6)} : Finset V) := by
      intro y hy
      obtain ⟨j,rfl⟩ := sur y
      have hh := (cyc7_sites i j).mp ((H.adj _ _).mp (hN _ hy))
      rcases hh with rfl | rfl <;> simp
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
  have h := Finset.sum_le_sum (s:=(Finset.univ : Finset V)) (fun x _ => atmost x)
  simpa [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_comm] using h

end Graffiti133NoFive

end OMA133_NoFiveHexDensity133

section OMA133_NoFivePeel133

namespace Graffiti133NoFive
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Finset
open scoped BigOperators
universe u

variable {V : Type u} [Fintype V]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem simplicial_of_local_le_one (G : SimpleGraph V) (v : V)
    (low : localIndependence G v ≤ 1) {a b : V}
    (ha : G.Adj v a) (hb : G.Adj v b) :
    a = b ∨ G.Adj a b := by
  classical
  by_cases ne : a = b
  · exact Or.inl ne
  by_cases e : G.Adj a b
  · exact Or.inr e
  exfalso
  have hs : ({a,b} : Finset V) ∈ localIndependentSets G v := by
    apply Graffiti133Pentagon.PentagonFrame.memLocalSet.mpr
    refine ⟨?_,?_⟩
    · intro x hx
      rcases (by simpa using hx : x=a ∨ x=b) with rfl | rfl
      · exact ha
      · exact hb
    · intro x hx y hy
      rcases (by simpa using hx : x=a ∨ x=b) with hx' | hx' <;>
        rcases (by simpa using hy : y=a ∨ y=b) with hy' | hy' <;> rw [hx',hy']
      · exact G.loopless.irrefl _
      · exact e
      · exact fun h => e h.symm
      · exact G.loopless.irrefl _
  have h := (Finset.le_sup (f:=Finset.card) hs).trans low
  simp [ne] at h

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem connected_delete_low_local (G : SimpleGraph V) (hc : G.Connected)
    (v : V) (low : localIndependence G v ≤ 1) (non : Nonempty {y : V // y ≠ v}) :
    (G.induce {y | y ≠ v}).Connected := by
  let S : Set V := {y | y ≠ v}
  let H := G.induce S
  have non' : Nonempty S := non
  apply @SimpleGraph.Connected.mk _ H _ non'
  intro x y
  obtain ⟨p⟩ := hc x.val y.val
  have reduce {a b : V} (q : G.Walk a b) (hb : b ≠ v) (u : S)
      (hu : u.val=a ∨ (a=v ∧ G.Adj u.val v)) : H.Reachable u ⟨b,hb⟩ := by
    induction q generalizing u with
    | nil =>
      rcases hu with eq | ⟨eq,_⟩
      · have he : u = ⟨_,hb⟩ := Subtype.ext eq
        exact he.symm ▸ SimpleGraph.Reachable.refl _
      · exact (hb eq).elim
    | @cons a b c e q ih =>
      by_cases bb : b=v
      · have aa : a ≠ v := by
          intro h
          exact e.ne (h.trans bb.symm)
        rcases hu with h | ⟨h,_⟩
        · exact ih hb u (Or.inr ⟨bb,h.symm ▸ (bb ▸ e)⟩)
        · exact (aa h).elim
      · let t : S := ⟨b,bb⟩
        have step : H.Reachable u t := by
          rcases hu with h | ⟨h,hu⟩
          · have ee : H.Adj u t := by
              change G.Adj u.val b
              exact h.symm ▸ e
            exact ee.reachable
          · have eb : G.Adj v b := h ▸ e
            rcases simplicial_of_local_le_one G v low hu.symm eb with near | adj
            · have eq : u = t := Subtype.ext near
              exact eq.symm ▸ SimpleGraph.Reachable.refl _
            · exact (show H.Adj u t from adj).reachable
        exact step.trans (ih hb t (Or.inl rfl))
  exact reduce p y.prop x (Or.inl rfl)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem connected_peel_for_P7 (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G)
    (hD : 3*Fintype.card V ≤ (∑ v, localIndependence G v))
    (core : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W), J.Connected →
      FourCycleFree J → NoSimpleFive133 J → (∀ v, 2 ≤ localIndependence J v) →
      3*Fintype.card W ≤ (∑ v, localIndependence J v) →
      ∃ f : Fin 7 → W, InducedPath J f) :
    ∃ f : Fin 7 → V, InducedPath G f := by
  classical
  let Claim (n : ℕ) := ∀ (W : Type u) [Fintype W] (J : SimpleGraph W),
    Fintype.card W=n → J.Connected → FourCycleFree J → NoSimpleFive133 J →
    3*Fintype.card W ≤ (∑ v, localIndependence J v) →
    ∃ f : Fin 7 → W, InducedPath J f
  have aux (n : ℕ) : Claim n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ G hn hC h4 h5 dens
      letI := hC.nonempty
      by_cases hmin : ∀ v, 2 ≤ localIndependence G v
      · exact core W G hC h4 h5 hmin dens
      push_neg at hmin
      obtain ⟨v,hv⟩ := hmin
      let S : Set W := {w | w ≠ v}
      let H := G.induce S
      have hpos : 0 < Fintype.card W := Fintype.card_pos
      have hS : Fintype.card S + 1 = Fintype.card W := by
        have hs : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card {x : W // ¬ x = v} = _
          rw [Fintype.card_subtype_compl]
          rw [show Fintype.card {x : W // x = v} = 1 from Fintype.card_unique]
        omega
      have h4' : FourCycleFree H := by
        intro a b x y hab hax hbx hay hby
        apply Subtype.ext
        exact h4 _ _ _ _ (fun h => hab (Subtype.ext h)) hax hbx hay hby
      have h5' : NoSimpleFive133 H := by
        intro a b c d e nd ha hb hC hd he
        have nd' := nd.map (Subtype.val_injective (p:=fun x : W => x ≠ v))
        exact h5 _ _ _ _ _ (by simpa using nd') ha hb hC hd he
      have non : Nonempty S := by
        have pos : 0 < (∑ v, localIndependence G v) := by omega
        obtain ⟨a,b,ab⟩ : ∃ a b, G.Adj a b := by
          apply Classical.byContradiction
          intro no
          have eq : ∀ x, localIndependence G x = 0 := by
            intro x
            obtain ⟨A,hA,hc⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
            rw [← hc,Finset.card_eq_zero]
            apply Finset.not_nonempty_iff_eq_empty.mp
            rintro ⟨a,ha⟩
            exact no ⟨x,a,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 a ha⟩
          simp [eq] at pos
        by_cases ha : a=v
        · exact ⟨⟨b,(ha ▸ ab.ne).symm⟩⟩
        · exact ⟨⟨a,ha⟩⟩
      have hConn : H.Connected := connected_delete_low_local G hC v (by omega) non
      have loss := local_sum_delete_bound G h4 v
      have dH : 3*Fintype.card S ≤ (∑ w, localIndependence H w) := by
        rw [← hS,Nat.mul_add,Nat.mul_one] at dens
        change (∑ w, localIndependence G w) ≤ (∑ w : S, localIndependence H w) +
          2*localIndependence G v at loss
        omega
      obtain ⟨f,hf⟩ := ih _ (by omega : Fintype.card S < n) S H rfl hConn h4' h5' dH
      exact ⟨fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
  exact aux (Fintype.card V) V G rfl hc h4 h5 hD

end Graffiti133NoFive

end OMA133_NoFivePeel133

section OMA133_NoFiveSeventh133

namespace Graffiti133NoFive
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem oma133_NoFiveSeventh133_neighbor_pair (v : V) (hv : 2 ≤ localIndependence G v) :
    ∃ x y, x ≠ y ∧ G.Adj v x ∧ G.Adj v y ∧ ¬G.Adj x y := by
  classical
  have m (s : Finset V) : s ∈ localIndependentSets G v ↔
      (∀ x ∈ s, G.Adj v x) ∧ (∀ x ∈ s, ∀ y ∈ s, ¬G.Adj x y) := by
    simp [localIndependentSets, Finset.subset_iff]
  obtain ⟨A,hA,hM⟩ := Finset.exists_max_image (localIndependentSets G v) Finset.card
    ⟨∅, m _ |>.mpr (by simp)⟩
  have hi : localIndependence G v ≤ A.card := Finset.sup_le_iff.mpr hM
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  have hA := (m _).mp hA
  exact ⟨x,y,hxy,hA.1 x hx,hA.1 y hy,hA.2 x hx y hy⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem oma133_NoFiveSeventh133_side_neighbor (h4 : FourCycleFree G) {v s : V} (e : G.Adj v s)
    (hv : 2 ≤ localIndependence G v) :
    ∃ w, G.Adj v w ∧ w ≠ s ∧ ¬G.Adj w s := by
  obtain ⟨x,y,hne,hx,hy,hxy⟩ := oma133_NoFiveSeventh133_neighbor_pair v hv
  by_cases ex : x = s
  · subst x
    exact ⟨y,hy,hne.symm,fun h => hxy h.symm⟩
  by_cases ey : y = s
  · subst y
    exact ⟨x,hx,hne,hxy⟩
  by_cases es : G.Adj x s
  · have no : ¬ G.Adj y s := by
      intro hb
      exact hne (h4 v s x y e.ne hx es.symm hy hb.symm)
    exact ⟨y,hy,ey,no⟩
  · exact ⟨x,hx,ex,es⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem oma133_NoFiveSeventh133_short_neighbor (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) {k : ℕ} (hk : 2 ≤ k) {f : Fin k → V}
    (p : InducedPath G f) (hv : 2 ≤ localIndependence G (f ⟨0,by omega⟩)) :
    ∃ w, (∀ i, w ≠ f i) ∧ G.Adj w (f ⟨0,by omega⟩) ∧
      (∀ i : Fin k, 0 < i.val → i.val ≤ 3 → ¬G.Adj w (f i)) := by
  let a : Fin k := ⟨0,by omega⟩
  let b : Fin k := ⟨1,by omega⟩
  have e : G.Adj (f a) (f b) := (p.2 a b (by change 0<1; decide)).mpr rfl
  obtain ⟨w,ew,hw,hwB⟩ := oma133_NoFiveSeventh133_side_neighbor h4 e hv
  have off (i : Fin k) : w ≠ f i := by
    intro eq
    by_cases h : i = a
    · rw [h] at eq
      exact ew.ne eq.symm
    · have hlt : a < i := by
        change 0 < i.val
        apply Nat.pos_of_ne_zero
        intro he
        exact h (Fin.ext he)
      have j := (p.2 a i hlt).mp (eq ▸ ew)
      have eqi : i = b := Fin.ext j.symm
      exact hw (eq.trans (congrArg f eqi))
  have no2 {i : Fin k} (hi : i.val = 2) : ¬G.Adj w (f i) := by
    intro ewi
    have ebi := (p.2 b i (by change 1 < i.val; omega)).mpr (by change 2=i.val; omega)
    have eq := h4 (f a) (f i) w (f b) (fun h => by
      have hh := congrArg Fin.val (p.1 h)
      change 0 = i.val at hh
      omega) ew ewi.symm e ebi.symm
    exact hw eq
  refine ⟨w,off,ew.symm,?_⟩
  intro i hlo hhi
  rcases (show i.val = 1 ∨ i.val = 2 ∨ i.val = 3 by omega) with h | h | h
  · have ei : i = b := Fin.ext h
    exact ei ▸ hwB
  · exact no2 h
  · intro ewi
    let j : Fin k := ⟨2,by have := i.isLt; omega⟩
    have eBj := (p.2 b j (by change 1<2; decide)).mpr rfl
    have eji := (p.2 j i (by change 2 < i.val; omega)).mpr (by change 3=i.val; omega)
    have hIndices : [a,b,j,i].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
      constructor
      · intro neq
        rcases neq with q | q | q <;> have uu := congrArg Fin.val q <;> dsimp [a,b,j] at uu <;> omega
      · constructor
        · intro neq
          rcases neq with q | q <;> have uu := congrArg Fin.val q <;> dsimp [a,b,j] at uu <;> omega
        · refine ⟨?_, by trivial⟩
          intro q
          have hh := congrArg Fin.val q
          dsimp [j] at hh
          omega
    have hLists : [w,f a,f b,f j,f i].Nodup := by
      apply List.nodup_cons.mpr
      refine ⟨by simp [off],?_⟩
      simpa using hIndices.map p.1
    exact h5 _ _ _ _ _ hLists ew.symm e eBj eji ewi.symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem core_P7 (hc : G.Connected) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (hl : ∀ v, 2 ≤ localIndependence G v)
    (hD : 3*Fintype.card V ≤ (∑ x, localIndependence G x)) :
    ∃ p : Fin 7 → V, InducedPath G p := by
  classical
  letI := hc.nonempty
  apply Classical.byContradiction
  intro no
  have ha : 3 ≤ averageLocal G := by
    unfold averageLocal
    have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α:=V)
    apply (le_div_iff₀ hn).mpr
    rw [← Nat.cast_sum]
    exact_mod_cast hD
  obtain ⟨p,hp⟩ := P6_of_local_mean_three G h4 h5 ha
  obtain ⟨w,hw,e,hn⟩ := oma133_NoFiveSeventh133_short_neighbor h4 h5 (by decide) hp (hl _)
  change G.Adj w (p 0) at e
  have H : Nonempty (Hole G 6) ∨ Nonempty (Hole G 7) := by
    by_cases hW4 : G.Adj w (p 4)
    · apply Or.inl
      let q := p ∘ Fin.castLE (by decide : 5 ≤ 6)
      have hq : InducedPath G q := ⟨hp.1.comp (Fin.castLE_injective (by decide)),
        fun i j ht => hp.2 _ _ ht⟩
      apply close_induced_path (by decide) hq w (fun i => hw _)
      · exact e
      · exact hW4
      · intro i h1 h2
        exact hn (Fin.castLE (by decide : 5 ≤ 6) i) h1 (by change i.val ≤ 3; omega)
    · by_cases hW5 : G.Adj w (p 5)
      · apply Or.inr
        apply close_induced_path (by decide) hp w hw e hW5
        intro i h1 h2
        by_cases hi4 : i.val = 4
        · have ee : i = 4 := Fin.ext hi4
          exact ee ▸ hW4
        · exact hn i h1 (by omega)
      · exfalso
        obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp w hw e (by
          intro i hi
          by_cases h4 : i.val = 4
          · have h : i=4 := Fin.ext h4
            exact h ▸ hW4
          · by_cases h5 : i.val = 5
            · have h : i=5 := Fin.ext h5
              exact h ▸ hW5
            · exact hn i hi (by have := i.isLt; omega))
        exact no ⟨q,hq⟩
  rcases H with H6 | H7
  · obtain ⟨H⟩ := H6
    have h := hex_budget H h4 h5 (hex_dominates H hc h4 h5 no)
    omega
  · obtain ⟨H⟩ := H7
    have h := heptagon_budget H (heptagon_spans H hc h4 h5 no)
    have pos := Fintype.card_pos (α:=V)
    omega

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem P7_of_mean_three_no_five (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (ha : 3 ≤ averageLocal G) :
    ∃ f : Fin 7 → V, InducedPath G f := by
  letI := hc.nonempty
  apply connected_peel_for_P7 G hc h4 h5 (nat_density_of_le_average G 3 ha)
  intro W _ J c a b lo d
  exact core_P7 c a b lo d

end Graffiti133NoFive

end OMA133_NoFiveSeventh133

section OMA133_FarPentagon133

namespace Graffiti133FarPentagon
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133Pentagon Graffiti133NoFive Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
structure Frame (G : SimpleGraph V) where
  c : Fin 5 → V
  inj : Function.Injective c
  adj : ∀ i j, G.Adj (c i) (c j) ↔ pent i j
  h4 : FourCycleFree G

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def MakeOne (F : Frame G) (x : V) (i : Fin 5) : Prop :=
  (∀ j, x ≠ F.c j) ∧ ∀ j, G.Adj x (F.c j) ↔ j = i

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def MakeTwo (F : Frame G) (x : V) (i : Fin 5) : Prop :=
  (∀ j, x ≠ F.c j) ∧ ∀ j, G.Adj x (F.c j) ↔ j = i ∨ j = i+1

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def Near (F : Frame G) (x : V) : Prop := (∀ i, x ≠ F.c i) ∧ ∃ i, G.Adj x (F.c i)
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def Far (F : Frame G) (x : V) : Prop := (∀ i, x ≠ F.c i) ∧ ∀ i, ¬G.Adj x (F.c i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem build_frame (h4 : FourCycleFree G) (h5 : ¬ NoSimpleFive133 G) :
    Nonempty (Frame G) := by
  classical
  unfold NoSimpleFive133 at h5
  push_neg at h5
  obtain ⟨a,b,c,d,e,hn,hAB,hBC,hCD,hDE,hEA⟩ := h5
  let f : Fin 5 → V := ![a,b,c,d,e]
  have inj : Function.Injective f := by
    apply List.nodup_ofFn.mp
    simpa [f,List.ofFn_succ] using hn
  have hside (i : Fin 5) : G.Adj (f i) (f (i+1)) := by
    fin_cases i
    all_goals first | exact hAB | exact hBC | exact hCD | exact hDE | exact hEA.1
  exact ⟨⟨f,inj,cycle_pentagon h4 inj hside,h4⟩⟩

namespace Frame
variable (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma oma133_FarPentagon133_finite_contact : ∀ b : Fin 5 → Bool,
    (∀ i, b i = true → b (i+2) = false) → (∃ i, b i = true) →
    (∃ i, ∀ j, b j = true ↔ j = i) ∨ (∃ i, ∀ j, b j = true ↔ j = i ∨ j = i+1) := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma forbid2 {x : V} (hx : ∀ i, x ≠ F.c i) (i : Fin 5)
    (h : G.Adj x (F.c i)) : ¬G.Adj x (F.c (i+2)) := by
  intro e
  have eq := F.h4 (F.c i) (F.c (i+2)) x (F.c (i+1))
    (fun w => (show i ≠ i+2 by fin_cases i <;> decide) (F.inj w)) h.symm e.symm
    ((F.adj _ _).mpr (Or.inl rfl))
    ((F.adj _ _).mpr (Or.inr (by fin_cases i <;> decide)))
  exact hx _ eq

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem classify {x : V} (hx : Near F x) :
    (∃ i, MakeOne F x i) ∨ (∃ i, MakeTwo F x i) := by
  classical
  let b : Fin 5 → Bool := fun i => decide (G.Adj x (F.c i))
  have btrue (i : Fin 5) : b i = true ↔ G.Adj x (F.c i) := by simp [b]
  have sep (i : Fin 5) (h : b i = true) : b (i+2) = false := by
    cases he : b (i+2)
    · rfl
    · exact (F.forbid2 hx.1 i ((btrue _).mp h) ((btrue _).mp he)).elim
  obtain ⟨i,hi⟩ := hx.2
  rcases oma133_FarPentagon133_finite_contact b sep ⟨i,(btrue _).mpr hi⟩ with ⟨j,hj⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨j,hx.1,fun w => (btrue _).symm.trans (hj w)⟩
  · exact Or.inr ⟨j,hx.1,fun w => (btrue _).symm.trans (hj w)⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma far_ne_near {a b : V} (ha : Far F a) (hb : Near F b) : a ≠ b := by
  intro e
  obtain ⟨i,hi⟩ := hb.2
  exact ha.2 i (e.symm ▸ hi)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem completes_far (no7 : ¬∃ f : Fin 7 → V, InducedPath G f)
    {x y z : V} (hx : Near F x) (hy : Far F y) (hz : Far F z)
    (exy : G.Adj x y) (eyz : G.Adj y z) : G.Adj x z := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨p,hp,h0,ht⟩ := extend_pentagon F.h4 F.inj F.adj x hx.1 hx.2
  have offY (i : Fin 5) : y ≠ p i := by
    intro e
    by_cases h : i.val=0
    · have eq : i=0 := Fin.ext h
      rw [eq,h0] at e
      exact exy.ne e.symm
    · obtain ⟨j,ej⟩ := ht i (Nat.pos_of_ne_zero h)
      exact hy.1 j (e.trans ej)
  have adjY : G.Adj y (p 0) := h0.symm ▸ exy.symm
  have noY (i : Fin 5) (h : 0 < i.val) : ¬G.Adj y (p i) := by
    obtain ⟨j,hj⟩ := ht i h
    exact fun e => hy.2 j (hj ▸ e)
  obtain ⟨q,hq,q0,qt⟩ := prepend_induced_with_positions (by decide) hp y offY adjY noY
  change q (0:Fin 6)=y at q0
  have q_rest (i : Fin 6) (h : 0 < i.val) : q i = x ∨ ∃ j, q i = F.c j := by
    let t : Fin 5 := ⟨i.val-1,by have := i.isLt; omega⟩
    have eq : q i = p t := qt i h
    by_cases e : t.val=0
    · have et : t=0 := Fin.ext e
      exact Or.inl (eq.trans (et ▸ h0))
    · obtain ⟨j,hj⟩ := ht t (Nat.pos_of_ne_zero e)
      exact Or.inr ⟨j,eq.trans hj⟩
  have offZ (i : Fin 6) : z ≠ q i := by
    intro e
    by_cases h : i.val=0
    · have eq : i=0 := Fin.ext h
      rw [eq,q0] at e
      exact eyz.ne e.symm
    · rcases q_rest i (Nat.pos_of_ne_zero h) with eq | ⟨j,eq⟩
      · exact (F.far_ne_near hz hx) (e.trans eq)
      · exact hz.1 j (e.trans eq)
  have adjZ : G.Adj z (q 0) := q0.symm ▸ eyz.symm
  have noZ (i : Fin 6) (h : 0 < i.val) : ¬G.Adj z (q i) := by
    intro e
    rcases q_rest i h with eq | ⟨j,eq⟩
    · exact no (eq ▸ e.symm)
    · exact hz.2 j (eq ▸ e)
  obtain ⟨r,hr,_,_⟩ := prepend_induced_with_positions (by decide) hq z offZ adjZ noZ
  exact no7 ⟨r,hr⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem far_has_near (hc : G.Connected)
    (no7 : ¬∃ f : Fin 7 → V, InducedPath G f) :
    ∀ y, Far F y → ∃ x, Near F x ∧ G.Adj x y := by
  classical
  have step (u v : V) (e : G.Adj u v)
      (hu : Far F u → ∃ x, Near F x ∧ G.Adj x u) :
      Far F v → ∃ x, Near F x ∧ G.Adj x v := by
    intro hv
    have out : ∀ i, u ≠ F.c i := fun i eq => hv.2 i ((eq ▸ e).symm)
    by_cases near : ∃ i, G.Adj u (F.c i)
    · exact ⟨u,⟨out,near⟩,e⟩
    · have hFar : Far F u := ⟨out,fun i h => near ⟨i,h⟩⟩
      obtain ⟨x,hx,ex⟩ := hu hFar
      exact ⟨x,hx,F.completes_far no7 hx hFar hv ex e⟩
  intro y
  obtain ⟨p⟩ := hc (F.c 0) y
  have hwalk {a b : V} (q : G.Walk a b)
      (ha : Far F a → ∃ x, Near F x ∧ G.Adj x a) :
      Far F b → ∃ x, Near F x ∧ G.Adj x b := by
    induction q with
    | nil => exact ha
    | cons e q ih => exact ih (step _ _ e ha)
  exact hwalk p (fun h => (h.1 0 rfl).elim)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem far_independent (hc : G.Connected) (no7 : ¬∃ f : Fin 7 → V, InducedPath G f)
    (min : ∀ x, 2 ≤ localIndependence G x)
    {y z : V} (hy : Far F y) (hz : Far F z) :
    ¬ G.Adj y z := by
  classical
  intro e
  obtain ⟨x,hx,ex⟩ := F.far_has_near hc no7 y hy
  have ez := F.completes_far no7 hx hy hz ex e
  have allN (v : V) (hv : G.Adj y v) : v = x ∨ v = z := by
    have out : ∀ i, v ≠ F.c i := fun i eq => hy.2 i (eq ▸ hv)
    by_cases ht : ∃ i, G.Adj v (F.c i)
    · have near : Near F v := ⟨out,ht⟩
      have hvz := F.completes_far no7 near hy hz hv.symm e
      exact Or.inl (F.h4 y z v x e.ne hv hvz.symm ex.symm ez.symm)
    · have far : Far F v := ⟨out,fun i h => ht ⟨i,h⟩⟩
      have exv := F.completes_far no7 hx hy far ex hv
      exact Or.inr (F.h4 x y v z ex.ne exv hv ez e)
  have low : localIndependence G y ≤ 1 := by
    apply Finset.sup_le_iff.mpr
    intro A hA
    obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rcases allN a (hN _ ha) with ea | ea <;> rcases allN b (hN _ hb) with eb | eb
    · exact ea.trans eb.symm
    · exact (hI _ ha _ hb (ea.symm ▸ eb.symm ▸ ez)).elim
    · exact (hI _ ha _ hb (ea.symm ▸ eb.symm ▸ ez.symm)).elim
    · exact ea.trans eb.symm
  have h := min y
  omega

end Frame
end Graffiti133FarPentagon

end OMA133_FarPentagon133

section OMA133_FarPair133

namespace Graffiti133FarPentagon
namespace Frame
open SimpleGraph Graffiti133 Graffiti133Pentagon Graffiti133NoFive

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def oma133_FarPair133_TypeContact (t : Fin 10) (i : Fin 5) : Prop :=
  if h : t.val < 5 then i = (⟨t.val,h⟩ : Fin 5)
  else i = (⟨t.val-5,by have := t.isLt; omega⟩ : Fin 5) ∨
    i = (⟨t.val-5,by have := t.isLt; omega⟩ : Fin 5) + 1
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private noncomputable instance (t : Fin 10) : DecidablePred (oma133_FarPair133_TypeContact t) := by
  intro i
  unfold oma133_FarPair133_TypeContact
  split <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def oma133_FarPair133_RootContact (t u : Fin 10) (q : Fin 8) (i : Fin 5) : Prop :=
  if q = 5 then oma133_FarPair133_TypeContact t i else if q = 6 then oma133_FarPair133_TypeContact u i else False
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private noncomputable instance (t u : Fin 10) (q : Fin 8) :
    DecidablePred (oma133_FarPair133_RootContact t u q) := by
  intro i
  unfold oma133_FarPair133_RootContact
  split
  · infer_instance
  · split <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def farRel (t u : Fin 10) (x y : Fin 8) : Prop :=
  if hx : x.val < 5 then
    if hy : y.val < 5 then pent ⟨x.val,hx⟩ ⟨y.val,hy⟩
    else oma133_FarPair133_RootContact t u y ⟨x.val,hx⟩
  else if hy : y.val < 5 then oma133_FarPair133_RootContact t u x ⟨y.val,hy⟩
  else (x = 7 ∧ (y = 5 ∨ y = 6)) ∨ (y = 7 ∧ (x = 5 ∨ x = 6))
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private noncomputable instance (t u : Fin 10) : DecidableRel (farRel t u) := by
  intro i j
  unfold farRel
  split <;> split <;> infer_instance

private inductive Cert
| four (i j a b : Fin 8)
| path (p : Fin 7 → Fin 8)
| hole6 (c : Fin 6 → Fin 8)
| hole7 (c : Fin 7 → Fin 8)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def oma133_FarPair133_certTrue (R : Fin 8 → Fin 8 → Prop) : Cert → Prop
| .four i j a b => i ≠ j ∧ a ≠ b ∧ R i a ∧ R j a ∧ R i b ∧ R j b
| .path p => (∀ i j, p i = p j → i = j) ∧ ∀ i j, i < j → (R (p i) (p j) ↔ i.val+1=j.val)
| .hole6 c => (∀ i j, c i = c j → i = j) ∧ ∀ i j, R (c i) (c j) ↔ Cyclic i j
| .hole7 c => (∀ i j, c i = c j → i = j) ∧ ∀ i j, R (c i) (c j) ↔ Cyclic i j

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private noncomputable instance (R : Fin 8 → Fin 8 → Prop) [DecidableRel R] :
    DecidablePred (oma133_FarPair133_certTrue R) := by
  intro e
  cases e <;> unfold oma133_FarPair133_certTrue <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def farTable (t u : Fin 10) : Cert :=
  match t.val,u.val with
  | 0, 0 => .four 0 7 5 6
  | 0, 1 => .path ![2,3,4,0,5,7,6]
  | 0, 2 => .hole6 ![0,1,2,6,7,5]
  | 0, 3 => .hole6 ![0,4,3,6,7,5]
  | 0, 4 => .path ![1,2,3,4,6,7,5]
  | 0, 5 => .four 0 7 5 6
  | 0, 6 => .hole7 ![0,4,3,2,6,7,5]
  | 0, 7 => .hole6 ![0,1,2,6,7,5]
  | 0, 8 => .hole7 ![0,1,2,3,6,7,5]
  | 0, 9 => .four 0 7 5 6
  | 1, 0 => .path ![2,3,4,0,6,7,5]
  | 1, 1 => .four 1 7 5 6
  | 1, 2 => .path ![0,4,3,2,6,7,5]
  | 1, 3 => .hole6 ![1,2,3,6,7,5]
  | 1, 4 => .hole6 ![0,1,5,7,6,4]
  | 1, 5 => .four 1 7 5 6
  | 1, 6 => .four 1 7 5 6
  | 1, 7 => .hole7 ![0,1,5,7,6,3,4]
  | 1, 8 => .hole6 ![0,1,5,7,6,4]
  | 1, 9 => .hole7 ![1,2,3,4,6,7,5]
  | 2, 0 => .hole6 ![0,1,2,5,7,6]
  | 2, 1 => .path ![0,4,3,2,5,7,6]
  | 2, 2 => .four 2 7 5 6
  | 2, 3 => .path ![1,0,4,3,6,7,5]
  | 2, 4 => .hole6 ![2,3,4,6,7,5]
  | 2, 5 => .hole7 ![0,4,3,2,5,7,6]
  | 2, 6 => .four 2 7 5 6
  | 2, 7 => .four 2 7 5 6
  | 2, 8 => .hole7 ![0,1,2,5,7,6,4]
  | 2, 9 => .hole6 ![0,1,2,5,7,6]
  | 3, 0 => .hole6 ![0,4,3,5,7,6]
  | 3, 1 => .hole6 ![1,2,3,5,7,6]
  | 3, 2 => .path ![1,0,4,3,5,7,6]
  | 3, 3 => .four 3 7 5 6
  | 3, 4 => .path ![0,1,2,3,5,7,6]
  | 3, 5 => .hole6 ![0,4,3,5,7,6]
  | 3, 6 => .hole7 ![0,1,6,7,5,3,4]
  | 3, 7 => .four 3 7 5 6
  | 3, 8 => .four 3 7 5 6
  | 3, 9 => .hole7 ![0,1,2,3,5,7,6]
  | 4, 0 => .path ![1,2,3,4,5,7,6]
  | 4, 1 => .hole6 ![0,1,6,7,5,4]
  | 4, 2 => .hole6 ![2,3,4,5,7,6]
  | 4, 3 => .path ![0,1,2,3,6,7,5]
  | 4, 4 => .four 4 7 5 6
  | 4, 5 => .hole7 ![1,2,3,4,5,7,6]
  | 4, 6 => .hole6 ![0,1,6,7,5,4]
  | 4, 7 => .hole7 ![0,1,2,6,7,5,4]
  | 4, 8 => .four 4 7 5 6
  | 4, 9 => .four 4 7 5 6
  | 5, 0 => .four 0 7 5 6
  | 5, 1 => .four 1 7 5 6
  | 5, 2 => .hole7 ![0,4,3,2,6,7,5]
  | 5, 3 => .hole6 ![0,4,3,6,7,5]
  | 5, 4 => .hole7 ![1,2,3,4,6,7,5]
  | 5, 5 => .four 0 1 5 6
  | 5, 6 => .four 1 7 5 6
  | 5, 7 => .hole6 ![0,4,3,6,7,5]
  | 5, 8 => .hole6 ![1,2,3,6,7,5]
  | 5, 9 => .four 0 7 5 6
  | 6, 0 => .hole7 ![0,4,3,2,5,7,6]
  | 6, 1 => .four 1 7 5 6
  | 6, 2 => .four 2 7 5 6
  | 6, 3 => .hole7 ![0,1,5,7,6,3,4]
  | 6, 4 => .hole6 ![0,1,5,7,6,4]
  | 6, 5 => .four 1 7 5 6
  | 6, 6 => .four 1 2 5 6
  | 6, 7 => .four 2 7 5 6
  | 6, 8 => .hole6 ![0,1,5,7,6,4]
  | 6, 9 => .hole6 ![2,3,4,6,7,5]
  | 7, 0 => .hole6 ![0,1,2,5,7,6]
  | 7, 1 => .hole7 ![0,1,6,7,5,3,4]
  | 7, 2 => .four 2 7 5 6
  | 7, 3 => .four 3 7 5 6
  | 7, 4 => .hole7 ![0,1,2,5,7,6,4]
  | 7, 5 => .hole6 ![0,4,3,5,7,6]
  | 7, 6 => .four 2 7 5 6
  | 7, 7 => .four 2 3 5 6
  | 7, 8 => .four 3 7 5 6
  | 7, 9 => .hole6 ![0,1,2,5,7,6]
  | 8, 0 => .hole7 ![0,1,2,3,5,7,6]
  | 8, 1 => .hole6 ![0,1,6,7,5,4]
  | 8, 2 => .hole7 ![0,1,2,6,7,5,4]
  | 8, 3 => .four 3 7 5 6
  | 8, 4 => .four 4 7 5 6
  | 8, 5 => .hole6 ![1,2,3,5,7,6]
  | 8, 6 => .hole6 ![0,1,6,7,5,4]
  | 8, 7 => .four 3 7 5 6
  | 8, 8 => .four 3 4 5 6
  | 8, 9 => .four 4 7 5 6
  | 9, 0 => .four 0 7 5 6
  | 9, 1 => .hole7 ![1,2,3,4,5,7,6]
  | 9, 2 => .hole6 ![0,1,2,6,7,5]
  | 9, 3 => .hole7 ![0,1,2,3,6,7,5]
  | 9, 4 => .four 4 7 5 6
  | 9, 5 => .four 0 7 5 6
  | 9, 6 => .hole6 ![2,3,4,5,7,6]
  | 9, 7 => .hole6 ![0,1,2,6,7,5]
  | 9, 8 => .four 4 7 5 6
  | 9, 9 => .four 0 4 5 6
  | _, _ => .four 0 0 0 0

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem checkFar : ∀ t u, oma133_FarPair133_certTrue (farRel t u) (farTable t u) := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma oma133_FarPair133_outside_cases : ∀ i : Fin 8, ¬ i.val < 5 → i = 5 ∨ i = 6 ∨ i = 7 := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma type_of_near {z : V} (hz : Near F z) :
    ∃ t, ∀ i, G.Adj z (F.c i) ↔ oma133_FarPair133_TypeContact t i := by
  rcases F.classify hz with ⟨i,hi⟩ | ⟨i,hi⟩
  · refine ⟨⟨i.val,by have := i.isLt; omega⟩,fun j => (hi.2 j).trans ?_⟩
    have he : i.val < 5 := i.isLt
    simp [oma133_FarPair133_TypeContact,he]
  · refine ⟨⟨i.val+5,by have := i.isLt; omega⟩,fun j => (hi.2 j).trans ?_⟩
    have he : ¬i.val+5 < 5 := by omega
    have he' : (⟨i.val+5-5,by have := i.isLt; omega⟩ : Fin 5) = i := Fin.ext (by simp)
    simp [oma133_FarPair133_TypeContact,he,he']

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem far_pair_forces_hole {x y z : V} (hx : Near F x) (hy : Near F y) (hz : Far F z)
    (xy : x ≠ y) (nxy : ¬G.Adj x y) (exz : G.Adj x z) (eyz : G.Adj y z)
    (no7 : ¬∃ f : Fin 7 → V, InducedPath G f) : Nonempty (Hole G 6) ∨ Nonempty (Hole G 7) := by
  classical
  obtain ⟨t,ht⟩ := F.type_of_near hx
  obtain ⟨u,hu⟩ := F.type_of_near hy
  let g (i : Fin 8) : V :=
    if hi : i.val < 5 then F.c ⟨i.val,hi⟩
    else if i = 5 then x else if i = 6 then y else z
  have gx : g 5 = x := rfl
  have gy : g 6 = y := rfl
  have gz : g 7 = z := rfl
  have inj : Function.Injective g := by
    intro i j eq
    by_cases hi : i.val < 5 <;> by_cases hj : j.val < 5
    · have e : F.c ⟨i.val,hi⟩ = F.c ⟨j.val,hj⟩ := by
        simpa only [g,dif_pos hi,dif_pos hj] using eq
      exact Fin.ext (congrArg (fun i : Fin 5 => i.val) (F.inj e))
    · rcases oma133_FarPair133_outside_cases j hj with rfl | rfl | rfl
      · exact (hx.1 ⟨_,hi⟩ (by simpa only [g,dif_pos hi,gx] using eq.symm)).elim
      · exact (hy.1 ⟨_,hi⟩ (by simpa only [g,dif_pos hi,gy] using eq.symm)).elim
      · exact (hz.1 ⟨_,hi⟩ (by simpa only [g,dif_pos hi,gz] using eq.symm)).elim
    · rcases oma133_FarPair133_outside_cases i hi with rfl | rfl | rfl
      · exact (hx.1 ⟨_,hj⟩ (by simpa only [g,dif_pos hj,gx] using eq)).elim
      · exact (hy.1 ⟨_,hj⟩ (by simpa only [g,dif_pos hj,gy] using eq)).elim
      · exact (hz.1 ⟨_,hj⟩ (by simpa only [g,dif_pos hj,gz] using eq)).elim
    · rcases oma133_FarPair133_outside_cases i hi with rfl | rfl | rfl <;>
        rcases oma133_FarPair133_outside_cases j hj with rfl | rfl | rfl <;>
          first | rfl | exact (xy eq).elim | exact (xy eq.symm).elim |
            exact (exz.ne eq).elim | exact (exz.ne eq.symm).elim |
            exact (eyz.ne eq).elim | exact (eyz.ne eq.symm).elim
  have rightContact (i : Fin 8) (hi : ¬i.val < 5) (j : Fin 5) :
      G.Adj (g i) (F.c j) ↔ oma133_FarPair133_RootContact t u i j := by
    rcases oma133_FarPair133_outside_cases i hi with rfl | rfl | rfl
    · rw [gx]
      exact (ht j).trans (by simp [oma133_FarPair133_RootContact])
    · rw [gy]
      exact (hu j).trans (by simp [oma133_FarPair133_RootContact])
    · rw [gz]
      simp [oma133_FarPair133_RootContact,hz.2 j]
  have nyx : ¬G.Adj y x := fun h => nxy h.symm
  have lift (i j : Fin 8) : G.Adj (g i) (g j) ↔ farRel t u i j := by
    by_cases hi : i.val < 5 <;> by_cases hj : j.val < 5
    · simpa only [g,farRel,dif_pos hi,dif_pos hj] using F.adj ⟨_,hi⟩ ⟨_,hj⟩
    · rw [farRel,dif_pos hi,dif_neg hj,show g i = F.c ⟨i.val,hi⟩ from dif_pos hi,G.adj_comm,
        rightContact j hj]
    · rw [farRel,dif_neg hi,dif_pos hj,show g j = F.c ⟨j.val,hj⟩ from dif_pos hj,
        rightContact i hi]
    · rcases oma133_FarPair133_outside_cases i hi with rfl | rfl | rfl <;>
        rcases oma133_FarPair133_outside_cases j hj with rfl | rfl | rfl
      all_goals simp [farRel,hi,hj,gx,gy,gz,exz,exz.symm,eyz,eyz.symm,nxy,
        nyx,G.loopless.irrefl]
  have cert := checkFar t u
  cases he : farTable t u with
  | four i j p q =>
    have er : i ≠ j ∧ p ≠ q ∧ farRel t u i p ∧ farRel t u j p ∧
        farRel t u i q ∧ farRel t u j q := by
      simpa only [he,oma133_FarPair133_certTrue] using cert
    obtain ⟨nij,npq,ip,jp,iq,jq⟩ := er
    have contra := F.h4 _ _ _ _ (fun e => nij (inj e)) ((lift _ _).mpr ip)
      ((lift _ _).mpr jp) ((lift _ _).mpr iq) ((lift _ _).mpr jq)
    exact (npq (inj contra)).elim
  | path p =>
    have er : (∀ i j, p i = p j → i = j) ∧
        ∀ i j : Fin 7, i < j → (farRel t u (p i) (p j) ↔ i.val+1=j.val) := by
      simpa only [he,oma133_FarPair133_certTrue] using cert
    exact (no7 ⟨g ∘ p,inj.comp er.1,fun i j h => (lift _ _).trans (er.2 i j h)⟩).elim
  | hole6 c =>
    have er : (∀ i j, c i = c j → i = j) ∧
        ∀ i j : Fin 6, farRel t u (c i) (c j) ↔ Cyclic i j := by
      simpa only [he,oma133_FarPair133_certTrue] using cert
    exact Or.inl ⟨⟨g ∘ c,inj.comp er.1,fun i j => (lift _ _).trans (er.2 _ _)⟩⟩
  | hole7 c =>
    have er : (∀ i j, c i = c j → i = j) ∧
        ∀ i j : Fin 7, farRel t u (c i) (c j) ↔ Cyclic i j := by
      simpa only [he,oma133_FarPair133_certTrue] using cert
    exact Or.inr ⟨⟨g ∘ c,inj.comp er.1,fun i j => (lift _ _).trans (er.2 _ _)⟩⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem far_forces_hole (hc : G.Connected)
    (no7 : ¬∃ f : Fin 7 → V, InducedPath G f)
    (hmin : ∀ x, 2 ≤ localIndependence G x) {z : V} (hz : Far F z) :
    Nonempty (Hole G 6) ∨ Nonempty (Hole G 7) := by
  classical
  obtain ⟨A,hA,hC⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) z
  have pos := hmin z
  obtain ⟨x,hx,y,hy,hne⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  have near (v : V) (ev : G.Adj z v) : Near F v := by
    have out : ∀ i, v ≠ F.c i := fun i he => hz.2 i (he ▸ ev)
    refine ⟨out,?_⟩
    apply Classical.byContradiction
    intro no
    have hFar : Far F v := ⟨out,fun i h => no ⟨i,h⟩⟩
    exact F.far_independent hc no7 hmin hz hFar ev
  exact F.far_pair_forces_hole (near x (hN x hx)) (near y (hN y hy)) hz hne
    (hI _ hx _ hy) (hN _ hx).symm (hN _ hy).symm no7

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma long_pent_arc : ∀ i j : Fin 5, i ≠ j → ¬pent i j →
    ∃ k l, [i,j,k,l].Nodup ∧ pent j k ∧ pent k l ∧ pent l i ∧
      ¬pent j l ∧ ¬pent i k := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem different_singles_hole {x y : V} {i j : Fin 5}
    (hx : MakeOne F x i) (hy : MakeOne F y j) (ij : i ≠ j) (e : G.Adj x y) :
    Nonempty (Hole G 6) := by
  have ex := (hx.2 i).mpr rfl
  have ey := (hy.2 j).mpr rfl
  have nc : ¬pent i j := by
    intro h
    exact hy.1 i (F.h4 x (F.c j) y (F.c i) (hx.1 j) e ey.symm ex
      ((F.adj _ _).mpr h).symm)
  obtain ⟨k,l,hn,ek,el,ei,nl,nk⟩ := long_pent_arc i j ij nc
  have nd : [F.c i,F.c j,F.c k,F.c l].Nodup := by simpa using hn.map F.inj
  have ij' : F.c i ≠ F.c j := F.inj.ne ij
  have jk : j ≠ k := by
    intro h
    have n := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
    exact n (by simp [h])
  have jl : j ≠ l := by
    intro h
    have n := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
    exact n (by simp [h])
  have ik : i ≠ k := by
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [h])
  have il : i ≠ l := by
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [h])
  have kl : k ≠ l := by
    intro h
    have n := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).1
    exact n (by simp [h])
  let p : Fin 5 → V := ![x,y,F.c j,F.c k,F.c l]
  have hp : InducedPath G p := by
    constructor
    · apply List.nodup_ofFn.mp
      simp [p,List.ofFn_succ,e.ne,hx.1 j,hx.1 k,hx.1 l,hy.1 j,hy.1 k,hy.1 l,
        F.inj.ne jk,F.inj.ne jl,F.inj.ne kl]
    · intro u v huv
      have ajk := (F.adj _ _).mpr ek
      have akl := (F.adj _ _).mpr el
      have nxj : ¬G.Adj x (F.c j) := fun h => ij ((hx.2 j).mp h).symm
      have nxk : ¬G.Adj x (F.c k) := fun h => ik ((hx.2 k).mp h).symm
      have nxl : ¬G.Adj x (F.c l) := fun h => il ((hx.2 l).mp h).symm
      have nyk : ¬G.Adj y (F.c k) := fun h => jk ((hy.2 k).mp h).symm
      have nyl : ¬G.Adj y (F.c l) := fun h => jl ((hy.2 l).mp h).symm
      have njl : ¬G.Adj (F.c j) (F.c l) := fun h => nl ((F.adj _ _).mp h)
      fin_cases u <;> fin_cases v
      all_goals first | contradiction | exact iff_of_true e rfl | exact iff_of_true ey rfl |
        exact iff_of_true ajk rfl | exact iff_of_true akl rfl |
        exact iff_of_false nxj (by decide) | exact iff_of_false nxk (by decide) |
        exact iff_of_false nxl (by decide) | exact iff_of_false nyk (by decide) |
        exact iff_of_false nyl (by decide) | exact iff_of_false njl (by decide)
  have off (t : Fin 5) : F.c i ≠ p t := by
    fin_cases t
    · exact (hx.1 _).symm
    · exact (hy.1 _).symm
    · exact ij'
    · exact F.inj.ne ik
    · exact F.inj.ne il
  refine close_induced_path (m:=5) (by decide) hp (F.c i) off ?_ ?_ ?_
  · change G.Adj (F.c i) x
    exact ex.symm
  · change G.Adj (F.c i) (F.c l)
    exact ((F.adj _ _).mpr ei).symm
  · intro t h0 hm
    have not_y : ¬G.Adj (F.c i) y := fun h => ij ((hy.2 _).mp h.symm)
    have not_j : ¬G.Adj (F.c i) (F.c j) := fun h => nc ((F.adj _ _).mp h)
    have not_k : ¬G.Adj (F.c i) (F.c k) := fun h => nk ((F.adj _ _).mp h)
    fin_cases t
    · exact ((by decide : ¬ (0 < 0)) h0).elim
    · exact not_y
    · exact not_j
    · exact not_k
    · exact ((by decide : ¬(4+1 < 5)) hm).elim

end Frame
end Graffiti133FarPentagon

end OMA133_FarPair133

section OMA133_DominatingPentagon133

namespace Graffiti133FarPentagon
namespace Frame
open SimpleGraph Graffiti133 Graffiti133Pentagon Graffiti133NoFive Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma contacts1 : ∀ i j : Fin 5, ¬pent i j → j=i ∨ j=i+2 ∨ j=i+3 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma contacts2 : ∀ i j : Fin 5, ¬pent i j → ¬pent (i+1) j → j=i+3 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma pair_in_slots : ∀ i j : Fin 5, (j=i ∨ j=i+2 ∨ j=i+3) →
    (j+1=i ∨ j+1=i+2 ∨ j+1=i+3) → j=i+2 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma pentSites : ∀ i j : Fin 5, pent i j ↔ j=i+1 ∨ j=i+4 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma pentNe : ∀ i j : Fin 5, pent i j → i ≠ j := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem not_adj_sites {x y : V} (hx : ∀ i,x ≠ F.c i) (hy : ∀ i,y ≠ F.c i)
    (e : G.Adj x y) {i j : Fin 5} (xi : G.Adj x (F.c i)) (yj : G.Adj y (F.c j)) :
    ¬pent i j := by
  intro p
  exact hy i (F.h4 x (F.c j) y (F.c i) (hx j) e yj.symm xi ((F.adj _ _).mpr p).symm)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private def oma133_DominatingPentagon133_Stamp (v : V) (i : Fin 5) : Prop := v = F.c i ∨ G.Adj v (F.c i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem oma133_DominatingPentagon133_stamp_inj {x y z : V} {i : Fin 5} (hne : x ≠ F.c i)
    (ey : G.Adj x y) (ez : G.Adj x z) (no : ¬ G.Adj y z)
    (sy : F.oma133_DominatingPentagon133_Stamp y i) (sz : F.oma133_DominatingPentagon133_Stamp z i) : y = z := by
  rcases sy with sy | sy <;> rcases sz with sz | sz
  · exact sy.trans sz.symm
  · exact (no (sy.symm ▸ sz.symm)).elim
  · exact (no (sz.symm ▸ sy)).elim
  · exact F.h4 x (F.c i) y z hne ey sy.symm ez sz.symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem local_le_two_of_seats (x : V) (P Q : V → Prop)
    (seats : ∀ y, G.Adj x y → P y ∨ Q y)
    (seatP : ∀ {y z}, G.Adj x y → G.Adj x z → ¬G.Adj y z → P y → P z → y=z)
    (seatQ : ∀ {y z}, G.Adj x y → G.Adj x z → ¬G.Adj y z → Q y → Q z → y=z) :
    localIndependence G x ≤ 2 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let f (y : V) : Bool := decide (P y)
  have hh : Set.InjOn f (↑A : Set V) := by
    intro y hy z hz fe
    by_cases hp : P y
    · have hPz : P z := by
        have eq : f y = true := by simp [f,hp]
        simpa [f] using fe.symm.trans eq
      exact seatP (hN _ hy) (hN _ hz) (hI _ hy _ hz) hp hPz
    · have hpz : ¬ P z := by
        have eq : f y = false := by simp [f,hp]
        simpa [f] using fe.symm.trans eq
      exact seatQ (hN _ hy) (hN _ hz) (hI _ hy _ hz)
        ((seats _ (hN _ hy)).resolve_left hp)
        ((seats _ (hN _ hz)).resolve_left hpz)
  have h := Finset.card_le_card_of_injOn f (t:=(Finset.univ : Finset Bool))
    (fun _ _ => Finset.mem_univ _) hh
  simpa using h

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem local_one_two (dom : ∀ x, (∀ i, x ≠ F.c i) → Near F x)
    (no6 : ¬Nonempty (Hole G 6)) {x : V} {i : Fin 5} (hx : MakeOne F x i) :
    localIndependence G x ≤ 2 := by
  classical
  apply local_le_two_of_seats x (fun y => F.oma133_DominatingPentagon133_Stamp y i) (fun y => F.oma133_DominatingPentagon133_Stamp y (i+2))
  · intro y e
    by_cases out : ∀ j, y ≠ F.c j
    · rcases F.classify (dom y out) with ⟨j,hy⟩ | ⟨j,hy⟩
      · have eq : j = i := by
          apply Classical.byContradiction
          intro ne
          exact no6 (F.different_singles_hole hx hy (fun h => ne h.symm) e)
        exact Or.inl (Or.inr ((hy.2 i).mpr eq.symm))
      · have c1 := contacts1 i j (F.not_adj_sites hx.1 hy.1 e ((hx.2 _).mpr rfl)
          ((hy.2 _).mpr (Or.inl rfl)))
        have c2 := contacts1 i (j+1) (F.not_adj_sites hx.1 hy.1 e ((hx.2 _).mpr rfl)
          ((hy.2 _).mpr (Or.inr rfl)))
        have eq := pair_in_slots i j c1 c2
        exact Or.inr (Or.inr ((hy.2 _).mpr (Or.inl eq.symm)))
    · obtain ⟨j,hj⟩ : ∃ j, y = F.c j := by
        apply Classical.byContradiction
        intro no
        exact out (fun j h => no ⟨j,h⟩)
      have ji := (hx.2 j).mp (hj ▸ e)
      exact Or.inl (Or.inl (hj.trans (congrArg F.c ji)))
  · intro a b e1 e2 no s1 s2
    exact F.oma133_DominatingPentagon133_stamp_inj (hx.1 i) e1 e2 no s1 s2
  · intro a b e1 e2 no s1 s2
    exact F.oma133_DominatingPentagon133_stamp_inj (hx.1 (i+2)) e1 e2 no s1 s2

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem local_two_two (dom : ∀ x, (∀ i, x ≠ F.c i) → Near F x)
    {x : V} {i : Fin 5} (hx : MakeTwo F x i) :
    localIndependence G x ≤ 2 := by
  classical
  apply local_le_two_of_seats x (fun y => y=F.c i ∨ y=F.c (i+1)) (fun y => F.oma133_DominatingPentagon133_Stamp y (i+3))
  · intro y e
    by_cases out : ∀ j, y ≠ F.c j
    · obtain ⟨j,hj⟩ := (dom y out).2
      have ne1 := F.not_adj_sites hx.1 out e ((hx.2 _).mpr (Or.inl rfl)) hj
      have ne2 := F.not_adj_sites hx.1 out e ((hx.2 _).mpr (Or.inr rfl)) hj
      exact Or.inr (Or.inr (contacts2 i j ne1 ne2 ▸ hj))
    · obtain ⟨j,hj⟩ : ∃ j, y = F.c j := by
        apply Classical.byContradiction
        intro no
        exact out (fun j h => no ⟨j,h⟩)
      apply Or.inl
      rcases (hx.2 _).mp (hj ▸ e) with eq | eq
      · exact Or.inl (hj.trans (congrArg F.c eq))
      · exact Or.inr (hj.trans (congrArg F.c eq))
  · intro a b e1 e2 no s1 s2
    have adjacent : G.Adj (F.c i) (F.c (i+1)) := (F.adj _ _).mpr (Or.inl rfl)
    rcases s1 with ea | ea <;> rcases s2 with eb | eb
    · exact ea.trans eb.symm
    · exact (no (ea.symm ▸ eb.symm ▸ adjacent)).elim
    · exact (no (ea.symm ▸ eb.symm ▸ adjacent.symm)).elim
    · exact ea.trans eb.symm
  · intro a b e1 e2 no s1 s2
    exact F.oma133_DominatingPentagon133_stamp_inj (hx.1 (i+3)) e1 e2 no s1 s2

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private noncomputable def oma133_DominatingPentagon133_singleSite (i : Fin 5) : Finset V := by
  classical exact Finset.univ.filter (fun x => MakeOne F x i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma oma133_DominatingPentagon133_site_mem {i : Fin 5} {x : V} :
    x ∈ F.oma133_DominatingPentagon133_singleSite i ↔ MakeOne F x i := by
  classical simp [oma133_DominatingPentagon133_singleSite]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem oma133_DominatingPentagon133_local_cycle_bound (dom : ∀ x, (∀ i, x ≠ F.c i) → Near F x) (i : Fin 5) :
    localIndependence G (F.c i) ≤ 2 + (F.oma133_DominatingPentagon133_singleSite i).card := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let B := A \ F.oma133_DominatingPentagon133_singleSite i
  let seats : Finset (Fin 5) := {i+1,i+4}
  have label (w : V) (hw : w ∈ B) : ∃ j, pent i j ∧ F.oma133_DominatingPentagon133_Stamp w j := by
    have e := hN w (Finset.mem_sdiff.mp hw).1
    by_cases out : ∀ i, w ≠ F.c i
    · rcases F.classify (dom w out) with ⟨j,hj⟩ | ⟨j,hj⟩
      · have he := (hj.2 i).mp e.symm
        exact ((Finset.mem_sdiff.mp hw).2 (F.oma133_DominatingPentagon133_site_mem.mpr (he.symm ▸ hj))).elim
      · rcases (hj.2 i).mp e.symm with he | he
        · exact ⟨j+1,Or.inl (by rw [he]),Or.inr ((hj.2 _).mpr (Or.inr rfl))⟩
        · exact ⟨j,Or.inr he.symm,Or.inr ((hj.2 _).mpr (Or.inl rfl))⟩
    · obtain ⟨j,hj⟩ : ∃ j, w = F.c j := by
        apply Classical.byContradiction
        intro no
        exact out (fun j eq => no ⟨j,eq⟩)
      exact ⟨j,(F.adj _ _).mp (hj ▸ e),Or.inl hj⟩
  let f (w : V) := if hw : w ∈ B then Classical.choose (label w hw) else i
  have fs (w : V) (hw : w ∈ B) : pent i (f w) ∧ F.oma133_DominatingPentagon133_Stamp w (f w) := by
    simpa only [f,dif_pos hw] using Classical.choose_spec (label w hw)
  have hf (w : V) (hw : w ∈ B) : f w ∈ seats := by
    simpa [seats] using (pentSites _ _).mp (fs w hw).1
  have inj : Set.InjOn f (↑B : Set V) := by
    intro y hy z hz e
    have hyA := (Finset.mem_sdiff.mp hy).1
    have hzA := (Finset.mem_sdiff.mp hz).1
    have ne : F.c i ≠ F.c (f y) := F.inj.ne (pentNe _ _ (fs y hy).1)
    exact F.oma133_DominatingPentagon133_stamp_inj ne (hN _ hyA) (hN _ hzA) (hI _ hyA _ hzA)
      (fs y hy).2 (e.symm ▸ (fs z hz).2)
  have cb : B.card ≤ 2 := (Finset.card_le_card_of_injOn f hf inj).trans
    ((Finset.card_insert_le _ _).trans (by simp))
  have hInt := Finset.card_le_card (show A ∩ F.oma133_DominatingPentagon133_singleSite i ⊆ F.oma133_DominatingPentagon133_singleSite i from Finset.inter_subset_right)
  have hC : B.card + (A ∩ F.oma133_DominatingPentagon133_singleSite i).card = A.card := Finset.card_sdiff_add_card_inter A _
  omega

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private noncomputable def oma133_DominatingPentagon133_singles : Finset V := by
  classical
  exact Finset.univ.filter (fun x => ∃ i, MakeOne F x i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private lemma oma133_DominatingPentagon133_singles_iff (x : V) :
    x ∈ F.oma133_DominatingPentagon133_singles ↔ ∃ i, MakeOne F x i := by classical simp [oma133_DominatingPentagon133_singles]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private noncomputable def oma133_DominatingPentagon133_core : Finset V := by
  classical
  exact (Finset.univ : Finset (Fin 5)).image F.c

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private noncomputable def oma133_DominatingPentagon133_fSite (x : V) : Fin 5 := by
  classical exact if h : ∃ i, MakeOne F x i then Classical.choose h else 0

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem oma133_DominatingPentagon133_sum_sites : (∑ i, (F.oma133_DominatingPentagon133_singleSite i).card) = (F.oma133_DominatingPentagon133_singles).card := by
  classical
  have fiber (i : Fin 5) : F.oma133_DominatingPentagon133_singleSite i = (F.oma133_DominatingPentagon133_singles).filter (fun x => F.oma133_DominatingPentagon133_fSite x = i) := by
    ext x
    rw [oma133_DominatingPentagon133_site_mem,Finset.mem_filter]
    have fvalid (h : x ∈ F.oma133_DominatingPentagon133_singles) : MakeOne F x (F.oma133_DominatingPentagon133_fSite x) := by
      have q := (F.oma133_DominatingPentagon133_singles_iff x).mp h
      unfold oma133_DominatingPentagon133_fSite
      rw [dif_pos q]
      exact Classical.choose_spec q
    refine ⟨?_,fun ⟨h,he⟩ => he ▸ fvalid h⟩
    intro h
    have hS := (F.oma133_DominatingPentagon133_singles_iff x).mpr ⟨i,h⟩
    exact ⟨hS,(h.2 _).mp (((fvalid hS).2 _).mpr rfl)⟩
  simpa only [fiber] using
    (Finset.card_eq_sum_card_fiberwise (s:=F.oma133_DominatingPentagon133_singles) (t:=Finset.univ)
      (f:=F.oma133_DominatingPentagon133_fSite) (fun _ _ => Finset.mem_univ _)).symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private noncomputable def oma133_DominatingPentagon133_charge (x : V) : ℕ := by
  classical exact ∑ i : Fin 5, if x = F.c i then (F.oma133_DominatingPentagon133_singleSite i).card else 0

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem pent_budget (dom : ∀ x, (∀ i, x ≠ F.c i) → Near F x)
    (no6 : ¬Nonempty (Hole G 6)) :
    (∑ x, localIndependence G x) + 5 ≤ 3 * Fintype.card V := by
  classical
  have pointwise (x : V) : localIndependence G x ≤ 2 + F.oma133_DominatingPentagon133_charge x := by
    by_cases out : ∀ i, x ≠ F.c i
    · rcases F.classify (dom x out) with ⟨i,h⟩ | ⟨i,h⟩
      · have l := F.local_one_two dom no6 h
        omega
      · have l := F.local_two_two dom h
        omega
    · obtain ⟨i,e⟩ : ∃ i, x = F.c i := by
        apply Classical.byContradiction
        intro no
        exact out fun j e => no ⟨j,e⟩
      have hL := F.oma133_DominatingPentagon133_local_cycle_bound dom i
      rw [← e] at hL
      have hl : (F.oma133_DominatingPentagon133_singleSite i).card ≤ F.oma133_DominatingPentagon133_charge x := by
        have hh := Finset.single_le_sum (f := fun j : Fin 5 =>
          if x = F.c j then (F.oma133_DominatingPentagon133_singleSite j).card else 0) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
        simpa [oma133_DominatingPentagon133_charge,e] using hh
      omega
  have disj : Disjoint F.oma133_DominatingPentagon133_core F.oma133_DominatingPentagon133_singles := by
    apply Finset.disjoint_left.mpr
    intro x hx hs
    obtain ⟨a,_,e⟩ := Finset.mem_image.mp hx
    obtain ⟨i,hi⟩ := (F.oma133_DominatingPentagon133_singles_iff x).mp hs
    exact hi.1 a e.symm
  have hC : F.oma133_DominatingPentagon133_core.card = 5 := by
    unfold oma133_DominatingPentagon133_core
    rw [Finset.card_image_of_injective _ F.inj]
    simp
  have hSize := Finset.card_le_card (Finset.subset_univ (F.oma133_DominatingPentagon133_core ∪ F.oma133_DominatingPentagon133_singles))
  rw [Finset.card_union_of_disjoint disj,hC,Finset.card_univ] at hSize
  have hcharge : (∑ x, F.oma133_DominatingPentagon133_charge x) = F.oma133_DominatingPentagon133_singles.card := by
    unfold oma133_DominatingPentagon133_charge
    rw [Finset.sum_comm]
    simp [F.oma133_DominatingPentagon133_sum_sites]
  have h := Finset.sum_le_sum (s:=(Finset.univ : Finset V)) (fun x _ => pointwise x)
  have hu : (∑ x, localIndependence G x) ≤ 2*Fintype.card V + F.oma133_DominatingPentagon133_singles.card := by
    simpa [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcharge,
      Nat.mul_comm] using h
  omega

end Frame
end Graffiti133FarPentagon

end OMA133_DominatingPentagon133

section OMA133_P7OrHole133

namespace Graffiti133FarPentagon
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133NoFive Finset
open scoped BigOperators
universe u

variable {V : Type u} [Fintype V]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
def Finding (G : SimpleGraph V) : Prop :=
  (∃ f : Fin 7 → V, InducedPath G f) ∨ Nonempty (Hole G 6) ∨ Nonempty (Hole G 7)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
private theorem connected_peel_finding (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G)
    (hD : 3*Fintype.card V ≤ (∑ v, localIndependence G v))
    (core : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W), J.Connected →
      FourCycleFree J → (∀ v, 2 ≤ localIndependence J v) →
      3*Fintype.card W ≤ (∑ v, localIndependence J v) →
      Finding J) :
    Finding G := by
  classical
  let Claim (n : ℕ) := ∀ (W : Type u) [Fintype W] (J : SimpleGraph W),
    Fintype.card W=n → J.Connected → FourCycleFree J →
    3*Fintype.card W ≤ (∑ v, localIndependence J v) →
    Finding J
  have aux (n : ℕ) : Claim n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ G hn hC h4 dens
      letI := hC.nonempty
      by_cases hmin : ∀ v, 2 ≤ localIndependence G v
      · exact core W G hC h4 hmin dens
      push_neg at hmin
      obtain ⟨v,hv⟩ := hmin
      let S : Set W := {w | w ≠ v}
      let H := G.induce S
      have hpos : 0 < Fintype.card W := Fintype.card_pos
      have hS : Fintype.card S + 1 = Fintype.card W := by
        have hs : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card {x : W // ¬ x = v} = _
          rw [Fintype.card_subtype_compl]
          rw [show Fintype.card {x : W // x = v} = 1 from Fintype.card_unique]
        omega
      have h4' : FourCycleFree H := by
        intro a b x y hab hax hbx hay hby
        apply Subtype.ext
        exact h4 _ _ _ _ (fun h => hab (Subtype.ext h)) hax hbx hay hby
      have non : Nonempty S := by
        have pos : 0 < (∑ v, localIndependence G v) := by omega
        obtain ⟨a,b,ab⟩ : ∃ a b, G.Adj a b := by
          apply Classical.byContradiction
          intro no
          have eq : ∀ x, localIndependence G x = 0 := by
            intro x
            obtain ⟨A,hA,hc⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
            rw [← hc,Finset.card_eq_zero]
            apply Finset.not_nonempty_iff_eq_empty.mp
            rintro ⟨a,ha⟩
            exact no ⟨x,a,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 a ha⟩
          simp [eq] at pos
        by_cases ha : a=v
        · exact ⟨⟨b,(ha ▸ ab.ne).symm⟩⟩
        · exact ⟨⟨a,ha⟩⟩
      have hConn : H.Connected := connected_delete_low_local G hC v (by omega) non
      have loss := local_sum_delete_bound G h4 v
      have dH : 3*Fintype.card S ≤ (∑ w, localIndependence H w) := by
        rw [← hS,Nat.mul_add,Nat.mul_one] at dens
        change (∑ w, localIndependence G w) ≤ (∑ w : S, localIndependence H w) +
          2*localIndependence G v at loss
        omega
      have witness := ih _ (by omega : Fintype.card S < n) S H rfl hConn h4' dH
      rcases witness with p | a | b
      · obtain ⟨f,hf⟩ := p
        exact Or.inl ⟨fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
      · obtain ⟨H⟩ := a
        exact Or.inr (Or.inl ⟨⟨fun i => (H.c i).val,Subtype.val_injective.comp H.inj,H.adj⟩⟩)
      · obtain ⟨H⟩ := b
        exact Or.inr (Or.inr ⟨⟨fun i => (H.c i).val,Subtype.val_injective.comp H.inj,H.adj⟩⟩)
  exact aux (Fintype.card V) V G rfl hc h4 hD

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
theorem local_mean_three_path_or_hole (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (hA : 3 ≤ averageLocal G) :
    Finding G := by
  classical
  letI := hc.nonempty
  apply connected_peel_finding G hc h4 (nat_density_of_le_average G 3 hA)
  intro W _ J conn h4 min hsum
  letI := conn.nonempty
  by_cases h5 : NoSimpleFive133 J
  · have av : 3 ≤ averageLocal J := by
      unfold averageLocal
      have hpos : (0 : ℚ) < Fintype.card W := by exact_mod_cast Fintype.card_pos (α:=W)
      apply (le_div_iff₀ hpos).mpr
      rw [← Nat.cast_sum]
      exact_mod_cast hsum
    exact Or.inl (P7_of_mean_three_no_five J conn h4 h5 av)
  · by_cases yes7 : ∃ f : Fin 7 → W, InducedPath J f
    · exact Or.inl yes7
    · by_cases yesH : Nonempty (Hole J 6) ∨ Nonempty (Hole J 7)
      · exact Or.inr yesH
      · exfalso
        obtain ⟨F⟩ := build_frame h4 h5
        have dom (x : W) (hx : ∀ i, x ≠ F.c i) : Near F x := by
          refine ⟨hx,?_⟩
          apply Classical.byContradiction
          intro unknown
          have far : Far F x := ⟨hx,fun i e => unknown ⟨i,e⟩⟩
          exact yesH (F.far_forces_hole conn yes7 min far)
        have hB := F.pent_budget dom (fun he => yesH (Or.inl he))
        omega

end Graffiti133FarPentagon

end OMA133_P7OrHole133

section OMA133_HexFrameGeneral133

namespace Graffiti133Hex
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133NoFive Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem lift_spoke_any {m n : ℕ} (hm : 0 < m) (H : Hole G n)
    (x : V) (hx : Outside H.c x) {b : Fin n → Bool}
    (hb : ∀ i, b i = true ↔ G.Adj x (H.c i))
    (path : Fin m → Fin (n+1)) (inj : Function.Injective path)
    (hs : ∀ i j : Fin m, i < j → (SpokeRel b (path i) (path j) ↔ i.val+1=j.val))
    (head : path ⟨0,hm⟩ = Fin.last n)
    (tail : ∀ i, 0 < i.val → (path i).val < n) :
    ∃ p : Fin m → V, InducedPath G p ∧ p ⟨0,hm⟩ = x ∧
      ∀ i, 0 < i.val → ∃ j, p i = H.c j := by
  let g (r : Fin (n+1)) : V := if hr : r.val < n then H.c ⟨r.val,hr⟩ else x
  have gLast : g (Fin.last n) = x := by simp [g]
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < n <;> by_cases hB : b.val < n
    · have he := H.inj (show H.c ⟨a.val,hA⟩ = H.c ⟨b.val,hB⟩ by
        simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun z : Fin n => z.val) he)
    · exact False.elim (hx ⟨a.val,hA⟩ (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm))
    · exact False.elim (hx ⟨b.val,hB⟩ (by simpa only [g,dif_neg hA,dif_pos hB] using eq))
    · apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
  have hrel (a q : Fin (n+1)) : G.Adj (g a) (g q) ↔ SpokeRel b a q := by
    by_cases hA : a.val < n <;> by_cases hQ : q.val < n
    · simpa only [g,SpokeRel,dif_pos hA,dif_pos hQ] using H.adj ⟨a.val,hA⟩ ⟨q.val,hQ⟩
    · simpa only [g,SpokeRel,dif_pos hA,dif_neg hQ,G.adj_comm] using (hb ⟨a.val,hA⟩).symm
    · simpa only [g,SpokeRel,dif_neg hA,dif_pos hQ] using (hb ⟨q.val,hQ⟩).symm
    · simp [g,SpokeRel,hA,hQ,G.loopless.irrefl]
  refine ⟨g ∘ path,⟨ginj.comp inj,fun a q he => (hrel _ _).trans (hs a q he)⟩,
    ?_,?_⟩
  · change g (path ⟨0,hm⟩) = x
    rw [head,gLast]
  · intro i hi
    exact ⟨⟨_,tail i hi⟩,dif_pos (tail i hi)⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
structure Frame (G : SimpleGraph V) extends Hole G 6 where
  h4 : FourCycleFree G
  no7 : ¬∃ p : Fin 7 → V, InducedPath G p

namespace Frame
variable (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def Single (x : V) (i : Fin 6) : Prop :=
  Outside F.c x ∧ ∀ j, G.Adj x (F.c j) ↔ j=i
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def Double (x : V) (i : Fin 6) : Prop :=
  Outside F.c x ∧ ∀ j, G.Adj x (F.c j) ↔ j=i ∨ j=i+1

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def frontInd (i : Fin 3) : Fin 6 := i.castLE (by decide)
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def Opp (x : V) (i : Fin 3) : Prop :=
  Outside F.c x ∧ ∀ j, G.Adj x (F.c j) ↔ j=frontInd i ∨ j=frontInd i+3

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def Near (x : V) : Prop := Outside F.c x ∧ ∃ i, G.Adj x (F.c i)
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def Far (x : V) : Prop := Outside F.c x ∧ ∀ i, ¬G.Adj x (F.c i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma allowed6 : ∀ b : Fin 6 → Bool,
    (∀ i, b i = true → b (i+2) = false) → (∃ i, b i = true) →
    (∃ i, ∀ j, b j=true ↔ j=i) ∨ (∃ i, ∀ j, b j=true ↔ j=i ∨ j=i+1) ∨
      (∃ i : Fin 3, ∀ j, b j=true ↔ j=frontInd i ∨ j=frontInd i+3) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma step6 : ∀ i : Fin 6, Cyclic i (i+1) ∧ Cyclic (i+1) (i+2) ∧ i≠i+2 := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem classify {x : V} (hx : F.Near x) :
    (∃ i, F.Single x i) ∨ (∃ i, F.Double x i) ∨ ∃ i, F.Opp x i := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (F.c i))
  have bt (i : Fin 6) : b i=true ↔ G.Adj x (F.c i) := by simp [b]
  have sep (i : Fin 6) (h : b i=true) : b (i+2)=false := by
    cases he : b (i+2)
    · rfl
    · have t := step6 i
      have eq := F.h4 (F.c i) (F.c (i+2)) x (F.c (i+1))
        (fun e => t.2.2 (F.inj e)) ((bt _).mp h).symm ((bt _).mp he).symm
        ((F.adj _ _).mpr t.1) ((F.adj _ _).mpr t.2.1).symm
      exact (hx.1 _ eq).elim
  obtain ⟨i,hi⟩ := hx.2
  rcases allowed6 b sep ⟨i,(bt _).mpr hi⟩ with a | a | a
  · obtain ⟨j,hj⟩ := a
    exact Or.inl ⟨j,hx.1,fun k => (bt k).symm.trans (hj k)⟩
  · obtain ⟨j,hj⟩ := a
    exact Or.inr (Or.inl ⟨j,hx.1,fun k => (bt k).symm.trans (hj k)⟩)
  · obtain ⟨j,hj⟩ := a
    exact Or.inr (Or.inr ⟨j,hx.1,fun k => (bt k).symm.trans (hj k)⟩)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem contact_forbid {x y : V} (hx : Outside F.c x) (hy : Outside F.c y)
    (e : G.Adj x y) {i j : Fin 6} (ex : G.Adj x (F.c i)) (ey : G.Adj y (F.c j)) :
    ¬Cyclic i j := by
  intro ed
  have h := F.h4 x (F.c j) y (F.c i) (hx j) e ey.symm ex ((F.adj _ _).mpr ed).symm
  exact hy _ h

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem stamp_uniq {x y z : V} {i : Fin 6} (hx : x ≠ F.c i)
    (ex : G.Adj x y) (ez : G.Adj x z) (no : ¬G.Adj y z)
    (hy : y = F.c i ∨ G.Adj y (F.c i)) (hz : z = F.c i ∨ G.Adj z (F.c i)) :
    y=z := by
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact hy.trans hz.symm
  · exact (no (hy.symm ▸ hz.symm)).elim
  · exact (no (hz.symm ▸ hy)).elim
  · exact F.h4 x (F.c i) y z hx ex hy.symm ez hz.symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def path6 (i : Fin 6) (positive : Bool) : Fin 6 → Fin 7 :=
  ![6,i.castSucc,(i+(if positive then 1 else 5)).castSucc,
    (i+(if positive then 2 else 4)).castSucc,(i+3).castSucc,
    (i+(if positive then 4 else 2)).castSucc]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma normal6 : ∀ b : Fin 6 → Bool,
    ((∃ i, ∀ j,b j=true ↔ j=i) ∨ (∃ i, ∀ j,b j=true ↔ j=i ∨ j=i+1)) →
    ∃ i pos,
      (∀ a c : Fin 6,path6 i pos a=path6 i pos c → a=c) ∧
      (∀ a c : Fin 6,a<c → (SpokeRel b (path6 i pos a) (path6 i pos c) ↔ a.val+1=c.val)) ∧
      (∀ a : Fin 6,0 < a.val → (path6 i pos a).val < 6) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem rooted6 {x : V} (hx : Outside F.c x)
    (kind : (∃ i, F.Single x i) ∨ ∃ i, F.Double x i) :
    ∃ p : Fin 6 → V, InducedPath G p ∧ p 0=x ∧
      ∀ j, 0 < j.val → ∃ i, p j=F.c i := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (F.c i))
  have bt (i : Fin 6) : b i=true ↔ G.Adj x (F.c i) := by simp [b]
  have shape : (∃ i, ∀ j,b j=true ↔ j=i) ∨ (∃ i, ∀ j,b j=true ↔ j=i ∨ j=i+1) := by
    rcases kind with ⟨i,hi⟩ | ⟨i,hi⟩
    · exact Or.inl ⟨i,fun j => (bt j).trans (hi.2 j)⟩
    · exact Or.inr ⟨i,fun j => (bt j).trans (hi.2 j)⟩
  obtain ⟨i,pos,hi,he,ht⟩ := normal6 b shape
  exact lift_spoke_any (by decide) F.toHole x hx bt (path6 i pos) hi he rfl ht

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private def antiPath4 (i : Fin 3) : Fin 4 → Fin 7 :=
  ![6,(frontInd i).castSucc,(frontInd i+1).castSucc,(frontInd i+2).castSucc]
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma anti4_ok : ∀ i : Fin 3, ∀ b : Fin 6 → Bool,
    (∀ j,b j=true ↔ j=frontInd i ∨ j=frontInd i+3) →
    (∀ a c : Fin 4,antiPath4 i a=antiPath4 i c → a=c) ∧
      (∀ a c : Fin 4,a<c → (SpokeRel b (antiPath4 i a) (antiPath4 i c) ↔ a.val+1=c.val)) ∧
      (∀ a : Fin 4,0 < a.val → (antiPath4 i a).val < 6) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem rooted4 {x : V} {i : Fin 3} (hx : F.Opp x i) :
    ∃ p : Fin 4 → V, InducedPath G p ∧ p 0=x ∧
      ∀ j, 0 < j.val → ∃ i, p j=F.c i := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (F.c i))
  have bt (i : Fin 6) : b i=true ↔ G.Adj x (F.c i) := by simp [b]
  obtain ⟨a,c,tail⟩ := anti4_ok i b (fun j => (bt j).trans (hx.2 j))
  exact lift_spoke_any (by decide) F.toHole x hx.1 bt (antiPath4 i) a c rfl tail

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem far_edge_opposite {x y : V} (hx : F.Near x) (hy : F.Far y)
    (e : G.Adj x y) : ∃ i, F.Opp x i := by
  classical
  rcases F.classify hx with single | double | opp
  · obtain ⟨p,hp,h0,ht⟩ := F.rooted6 hx.1 (Or.inl single)
    apply False.elim
    apply F.no7
    have off (i : Fin 6) : y ≠ p i := by
      intro eq
      by_cases h : i.val=0
      · have h' : i=0 := Fin.ext h
        rw [h',h0] at eq
        exact e.ne eq.symm
      · obtain ⟨j,hj⟩ := ht i (Nat.pos_of_ne_zero h)
        exact hy.1 j (eq.trans hj)
    have adj : G.Adj y (p 0) := h0.symm ▸ e.symm
    have no (i : Fin 6) (hi : 0 < i.val) : ¬ G.Adj y (p i) := by
      obtain ⟨j,hj⟩ := ht i hi
      exact fun eq => hy.2 j (hj ▸ eq)
    obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp y off adj no
    exact ⟨q,hq⟩
  · obtain ⟨p,hp,h0,ht⟩ := F.rooted6 hx.1 (Or.inr double)
    apply False.elim
    apply F.no7
    have off (i : Fin 6) : y ≠ p i := by
      intro eq
      by_cases h : i.val=0
      · have h' : i=0 := Fin.ext h
        rw [h',h0] at eq
        exact e.ne eq.symm
      · obtain ⟨j,hj⟩ := ht i (Nat.pos_of_ne_zero h)
        exact hy.1 j (eq.trans hj)
    have adj : G.Adj y (p 0) := h0.symm ▸ e.symm
    have no (i : Fin 6) (hi : 0 < i.val) : ¬ G.Adj y (p i) := by
      obtain ⟨j,hj⟩ := ht i hi
      exact fun eq => hy.2 j (hj ▸ eq)
    obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp y off adj no
    exact ⟨q,hq⟩
  · exact opp

end Frame
end Graffiti133Hex

end OMA133_HexFrameGeneral133

section OMA133_C7OnlyCert

namespace Graffiti133C7Only
open SimpleGraph Graffiti133 Graffiti133NoFive Finset

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
def Profile (i j : Fin 7) : Prop := j=i ∨ j=i+3 ∨ j=i+4
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
instance : DecidableRel Profile := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
def Mask (m : Fin 128) (i : Fin 7) : Prop := m.val.testBit i.val = true
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
instance : DecidableRel Mask := fun _ _ => inferInstanceAs (Decidable (_ = _))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private def profileMask (b : Fin 7 → Bool) : Fin 128 :=
  ⟨(if b 0 then 1 else 0) + (if b 1 then 2 else 0) + (if b 2 then 4 else 0) +
   (if b 3 then 8 else 0) + (if b 4 then 16 else 0) + (if b 5 then 32 else 0) +
   (if b 6 then 64 else 0), by
     have h0 : (if b 0 then 1 else 0) ≤ (1:ℕ) := by split <;> decide
     have h1 : (if b 1 then 2 else 0) ≤ (2:ℕ) := by split <;> decide
     have h2 : (if b 2 then 4 else 0) ≤ (4:ℕ) := by split <;> decide
     have h3 : (if b 3 then 8 else 0) ≤ (8:ℕ) := by split <;> decide
     have h4 : (if b 4 then 16 else 0) ≤ (16:ℕ) := by split <;> decide
     have h5 : (if b 5 then 32 else 0) ≤ (32:ℕ) := by split <;> decide
     have h6 : (if b 6 then 64 else 0) ≤ (64:ℕ) := by split <;> decide
     omega⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
lemma mask_cover : ∀ b : Fin 7 → Bool, ∀ i, Mask (profileMask b) i ↔ b i = true := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
def Rel8 (m : Fin 128) (i j : Fin 8) : Prop :=
  if hi : i.val < 7 then
    if hj : j.val < 7 then Cyclic ⟨_,hi⟩ ⟨_,hj⟩ else Mask m ⟨_,hi⟩
  else if hj : j.val < 7 then Mask m ⟨_,hj⟩ else False
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
instance (m : Fin 128) : DecidableRel (Rel8 m) := by
  intro i j
  unfold Rel8
  split <;> split <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
def Rel9 (a b : Fin 7) (edge : Bool) (i j : Fin 9) : Prop :=
  if hi : i.val < 7 then
    if hj : j.val < 7 then Cyclic ⟨_,hi⟩ ⟨_,hj⟩ else Profile (if j=7 then a else b) ⟨_,hi⟩
  else if hj : j.val < 7 then Profile (if i=7 then a else b) ⟨_,hj⟩ else i ≠ j ∧ edge=true
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
noncomputable instance (a b : Fin 7) (e : Bool) : DecidableRel (Rel9 a b e) := by
  intro i j
  unfold Rel9
  split <;> split <;> infer_instance

inductive Cert (n : ℕ)
| pass
| four (i j a b : Fin n)
| path (p : Fin 7 → Fin n)
| hole (p : Fin 6 → Fin n)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
def Cert.Valid {n : ℕ} (R : Fin n → Fin n → Prop) (s : Prop) : Cert n → Prop
| .pass => s
| .four i j a b => i≠j ∧ a≠b ∧ R i a ∧ R j a ∧ R i b ∧ R j b
| .path p => (∀ i j, p i=p j → i=j) ∧ ∀ i j, i<j → (R (p i) (p j) ↔ i.val+1=j.val)
| .hole p => (∀ i j, p i=p j → i=j) ∧ ∀ i j, R (p i) (p j) ↔ Cyclic i j
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (s : Prop) [Decidable s] :
    DecidablePred (Cert.Valid R s) := by
  intro c
  cases c <;> unfold Cert.Valid <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private def table8 (m : Fin 128) : Cert 8 :=
  match m.val with
  | 1 => .path ![2,3,4,5,6,0,7]
  | 2 => .path ![3,4,5,6,0,1,7]
  | 3 => .path ![2,3,4,5,6,0,7]
  | 4 => .path ![0,6,5,4,3,2,7]
  | 5 => .four 0 2 1 7
  | 6 => .path ![0,6,5,4,3,2,7]
  | 7 => .four 0 2 1 7
  | 8 => .path ![1,0,6,5,4,3,7]
  | 9 => .hole ![0,6,5,4,3,7]
  | 10 => .four 1 3 2 7
  | 11 => .four 1 3 2 7
  | 12 => .path ![1,0,6,5,4,3,7]
  | 13 => .four 0 2 1 7
  | 14 => .four 1 3 2 7
  | 15 => .four 0 2 1 7
  | 16 => .path ![2,1,0,6,5,4,7]
  | 17 => .hole ![0,1,2,3,4,7]
  | 18 => .hole ![0,1,7,4,5,6]
  | 20 => .four 2 4 3 7
  | 21 => .four 0 2 1 7
  | 22 => .four 2 4 3 7
  | 23 => .four 0 2 1 7
  | 24 => .path ![2,1,0,6,5,4,7]
  | 26 => .four 1 3 2 7
  | 27 => .four 1 3 2 7
  | 28 => .four 2 4 3 7
  | 29 => .four 0 2 1 7
  | 30 => .four 1 3 2 7
  | 31 => .four 0 2 1 7
  | 32 => .path ![0,1,2,3,4,5,7]
  | 33 => .four 0 5 6 7
  | 34 => .hole ![1,2,3,4,5,7]
  | 35 => .four 0 5 6 7
  | 36 => .hole ![0,1,2,7,5,6]
  | 37 => .four 0 2 1 7
  | 39 => .four 0 2 1 7
  | 40 => .four 3 5 4 7
  | 41 => .four 0 5 6 7
  | 42 => .four 1 3 2 7
  | 43 => .four 0 5 6 7
  | 44 => .four 3 5 4 7
  | 45 => .four 0 2 1 7
  | 46 => .four 1 3 2 7
  | 47 => .four 0 2 1 7
  | 48 => .path ![3,2,1,0,6,5,7]
  | 49 => .four 0 5 6 7
  | 51 => .four 0 5 6 7
  | 52 => .four 2 4 3 7
  | 53 => .four 0 2 1 7
  | 54 => .four 2 4 3 7
  | 55 => .four 0 2 1 7
  | 56 => .four 3 5 4 7
  | 57 => .four 0 5 6 7
  | 58 => .four 1 3 2 7
  | 59 => .four 0 5 6 7
  | 60 => .four 2 4 3 7
  | 61 => .four 0 2 1 7
  | 62 => .four 1 3 2 7
  | 63 => .four 0 2 1 7
  | 64 => .path ![1,2,3,4,5,6,7]
  | 65 => .path ![1,2,3,4,5,6,7]
  | 66 => .four 0 7 1 6
  | 67 => .four 0 7 1 6
  | 68 => .hole ![2,3,4,5,6,7]
  | 69 => .four 0 2 1 7
  | 70 => .four 0 7 1 6
  | 71 => .four 0 2 1 7
  | 72 => .hole ![0,1,2,3,7,6]
  | 74 => .four 0 7 1 6
  | 75 => .four 0 7 1 6
  | 77 => .four 0 2 1 7
  | 78 => .four 0 7 1 6
  | 79 => .four 0 2 1 7
  | 80 => .four 4 6 5 7
  | 81 => .four 4 6 5 7
  | 82 => .four 0 7 1 6
  | 83 => .four 0 7 1 6
  | 84 => .four 2 4 3 7
  | 85 => .four 0 2 1 7
  | 86 => .four 0 7 1 6
  | 87 => .four 0 2 1 7
  | 88 => .four 4 6 5 7
  | 89 => .four 4 6 5 7
  | 90 => .four 0 7 1 6
  | 91 => .four 0 7 1 6
  | 92 => .four 2 4 3 7
  | 93 => .four 0 2 1 7
  | 94 => .four 0 7 1 6
  | 95 => .four 0 2 1 7
  | 96 => .path ![0,1,2,3,4,5,7]
  | 97 => .four 0 5 6 7
  | 98 => .four 0 7 1 6
  | 99 => .four 0 5 6 7
  | 101 => .four 0 2 1 7
  | 102 => .four 0 7 1 6
  | 103 => .four 0 2 1 7
  | 104 => .four 3 5 4 7
  | 105 => .four 0 5 6 7
  | 106 => .four 0 7 1 6
  | 107 => .four 0 5 6 7
  | 108 => .four 3 5 4 7
  | 109 => .four 0 2 1 7
  | 110 => .four 0 7 1 6
  | 111 => .four 0 2 1 7
  | 112 => .four 4 6 5 7
  | 113 => .four 0 5 6 7
  | 114 => .four 0 7 1 6
  | 115 => .four 0 5 6 7
  | 116 => .four 2 4 3 7
  | 117 => .four 0 2 1 7
  | 118 => .four 0 7 1 6
  | 119 => .four 0 2 1 7
  | 120 => .four 3 5 4 7
  | 121 => .four 0 5 6 7
  | 122 => .four 0 7 1 6
  | 123 => .four 0 5 6 7
  | 124 => .four 2 4 3 7
  | 125 => .four 0 2 1 7
  | 126 => .four 0 7 1 6
  | 127 => .four 0 2 1 7
  | _ => .pass
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private def table9 (i j : Fin 7) (b : Bool) : Cert 9 :=
  match i.val,j.val,b with
  | 0, 0, false => .four 0 3 7 8
  | 0, 0, true => .four 0 3 7 8
  | 0, 1, false => .path ![2,3,7,0,6,5,8]
  | 0, 1, true => .four 0 8 1 7
  | 0, 2, false => .hole ![0,6,8,2,3,7]
  | 0, 2, true => .four 0 8 6 7
  | 0, 3, false => .four 0 3 7 8
  | 0, 3, true => .four 0 3 7 8
  | 0, 4, false => .four 0 4 7 8
  | 0, 4, true => .four 0 4 7 8
  | 0, 5, false => .hole ![0,1,8,5,4,7]
  | 0, 5, true => .four 0 8 1 7
  | 0, 6, false => .path ![1,2,8,6,5,4,7]
  | 0, 6, true => .four 0 8 6 7
  | 1, 0, false => .path ![2,3,8,0,6,5,7]
  | 1, 0, true => .four 0 7 1 8
  | 1, 1, false => .four 1 4 7 8
  | 1, 1, true => .four 1 4 7 8
  | 1, 2, false => .path ![0,6,8,2,3,4,7]
  | 1, 2, true => .four 1 8 2 7
  | 1, 3, false => .hole ![0,1,7,4,3,8]
  | 1, 3, true => .four 0 7 1 8
  | 1, 4, false => .four 1 4 7 8
  | 1, 4, true => .four 0 7 1 8
  | 1, 5, false => .four 1 5 7 8
  | 1, 5, true => .four 1 5 7 8
  | 1, 6, false => .hole ![1,2,8,6,5,7]
  | 1, 6, true => .four 1 8 2 7
  | 2, 0, false => .hole ![0,6,7,2,3,8]
  | 2, 0, true => .four 0 7 6 8
  | 2, 1, false => .path ![0,6,7,2,3,4,8]
  | 2, 1, true => .four 1 7 2 8
  | 2, 2, false => .four 2 5 7 8
  | 2, 2, true => .four 2 5 7 8
  | 2, 3, false => .path ![1,0,8,3,4,5,7]
  | 2, 3, true => .four 0 7 6 8
  | 2, 4, false => .hole ![1,2,7,5,4,8]
  | 2, 4, true => .four 0 7 6 8
  | 2, 5, false => .four 2 5 7 8
  | 2, 5, true => .four 1 7 2 8
  | 2, 6, false => .four 2 6 7 8
  | 2, 6, true => .four 2 6 7 8
  | 3, 0, false => .four 0 3 7 8
  | 3, 0, true => .four 0 3 7 8
  | 3, 1, false => .hole ![0,1,8,4,3,7]
  | 3, 1, true => .four 0 8 1 7
  | 3, 2, false => .path ![1,0,7,3,4,5,8]
  | 3, 2, true => .four 0 8 6 7
  | 3, 3, false => .four 0 3 7 8
  | 3, 3, true => .four 0 3 7 8
  | 3, 4, false => .path ![2,1,8,4,5,6,7]
  | 3, 4, true => .four 0 7 6 8
  | 3, 5, false => .hole ![2,3,7,6,5,8]
  | 3, 5, true => .four 0 8 1 7
  | 3, 6, false => .four 3 6 7 8
  | 3, 6, true => .four 0 8 6 7
  | 4, 0, false => .four 0 4 7 8
  | 4, 0, true => .four 0 4 7 8
  | 4, 1, false => .four 1 4 7 8
  | 4, 1, true => .four 0 8 1 7
  | 4, 2, false => .hole ![1,2,8,5,4,7]
  | 4, 2, true => .four 0 8 6 7
  | 4, 3, false => .path ![2,1,7,4,5,6,8]
  | 4, 3, true => .four 0 7 1 8
  | 4, 4, false => .four 0 1 7 8
  | 4, 4, true => .four 0 1 7 8
  | 4, 5, false => .path ![3,2,8,5,6,0,7]
  | 4, 5, true => .four 0 8 1 7
  | 4, 6, false => .hole ![0,6,8,3,4,7]
  | 4, 6, true => .four 0 8 6 7
  | 5, 0, false => .hole ![0,1,7,5,4,8]
  | 5, 0, true => .four 0 7 1 8
  | 5, 1, false => .four 1 5 7 8
  | 5, 1, true => .four 1 5 7 8
  | 5, 2, false => .four 2 5 7 8
  | 5, 2, true => .four 1 8 2 7
  | 5, 3, false => .hole ![2,3,8,6,5,7]
  | 5, 3, true => .four 0 7 1 8
  | 5, 4, false => .path ![3,2,7,5,6,0,8]
  | 5, 4, true => .four 0 7 1 8
  | 5, 5, false => .four 1 2 7 8
  | 5, 5, true => .four 1 2 7 8
  | 5, 6, false => .path ![0,1,7,5,4,3,8]
  | 5, 6, true => .four 1 8 2 7
  | 6, 0, false => .path ![1,2,7,6,5,4,8]
  | 6, 0, true => .four 0 7 6 8
  | 6, 1, false => .hole ![1,2,7,6,5,8]
  | 6, 1, true => .four 1 7 2 8
  | 6, 2, false => .four 2 6 7 8
  | 6, 2, true => .four 2 6 7 8
  | 6, 3, false => .four 3 6 7 8
  | 6, 3, true => .four 0 7 6 8
  | 6, 4, false => .hole ![0,6,7,3,4,8]
  | 6, 4, true => .four 0 7 6 8
  | 6, 5, false => .path ![0,1,8,5,4,3,7]
  | 6, 5, true => .four 1 7 2 8
  | 6, 6, false => .four 2 3 7 8
  | 6, 6, true => .four 2 3 7 8
  | _, _, _ => .pass
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
lemma check_single : ∀ m : Fin 128, (∃ i, Mask m i) →
    (table8 m).Valid (Rel8 m) (∃ i, ∀ j, Mask m j ↔ Profile i j) := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
lemma check_pair : ∀ i j b, (table9 i j b).Valid (Rel9 i j b) False := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
def RootPath (i : Fin 7) : Fin 4 → Fin 8 :=
  ![7,i.castSucc,(i+1).castSucc,(i+2).castSucc]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
def Spoke (a : Fin 7) : Fin 7 → Bool := fun i => decide (Profile a i)
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private lemma rooted_check : ∀ i : Fin 7,
  (∀ a b, RootPath i a = RootPath i b → a=b) ∧
  (∀ a b, a<b → (SpokeRel (Spoke i) (RootPath i a) (RootPath i b) ↔ a.val+1=b.val)) ∧
  (∀ a, 0 < a.val → (RootPath i a).val < 7) := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private lemma sound {n} {R : Fin n → Fin n → Prop} {s : Prop}
    (g : Fin n → V) (gi : Function.Injective g)
    (gr : ∀ i j, G.Adj (g i) (g j) ↔ R i j)
    (c : Cert n) (ok : c.Valid R s)
    (h4 : FourCycleFree G) (h7 : ¬∃ p : Fin 7 → V, InducedPath G p)
    (h6 : ¬Nonempty (Hole G 6)) : s := by
  cases c with
  | pass => exact ok
  | four i j x y =>
    obtain ⟨ij,xy,a,b,c,d⟩ := ok
    exact (xy (gi (h4 _ _ _ _ (fun e => ij (gi e)) ((gr ..).mpr a) ((gr ..).mpr b)
      ((gr ..).mpr c) ((gr ..).mpr d)))).elim
  | path p =>
    exact (h7 ⟨g ∘ p,gi.comp ok.1,fun i j h => (gr ..).trans (ok.2 i j h)⟩).elim
  | hole p =>
    exact (h6 ⟨⟨g ∘ p,gi.comp ok.1,fun i j => (gr ..).trans (ok.2 i j)⟩⟩).elim

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
def IsProfile (H : Hole G 7) (x : V) (i : Fin 7) : Prop :=
  Outside H.c x ∧ ∀ j, G.Adj x (H.c j) ↔ Profile i j

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
def OnlyFar (H : Hole G 7) (x : V) : Prop :=
  Outside H.c x ∧ ∀ i, ¬G.Adj x (H.c i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem model8 (H : Hole G 7) {x : V} (hx : Outside H.c x)
    (m : Fin 128) (hm : ∀ j, G.Adj x (H.c j) ↔ Mask m j) :
    ∃ g : Fin 8 → V, Function.Injective g ∧ (∀ j : Fin 7, g j.castSucc = H.c j) ∧
      g 7=x ∧ ∀ i j, G.Adj (g i) (g j) ↔ Rel8 m i j := by
  let g (i : Fin 8) := if h : i.val < 7 then H.c ⟨i.val,h⟩ else x
  have cg (i : Fin 7) : g i.castSucc = H.c i := by simp [g,i.isLt]
  have gx : g 7 = x := rfl
  have cases8 (i : Fin 8) : (∃ j : Fin 7, i = j.castSucc) ∨ i=7 := by
    by_cases hi : i.val < 7
    · exact Or.inl ⟨⟨_,hi⟩,Fin.ext rfl⟩
    · exact Or.inr (Fin.ext (by have := i.isLt; change i.val = 7; omega))
  refine ⟨g,?_,cg,gx,?_⟩
  · intro a b h
    rcases cases8 a with ⟨i,rfl⟩|rfl <;> rcases cases8 b with ⟨j,rfl⟩|rfl
    · rw [cg,cg] at h
      exact congrArg Fin.castSucc (H.inj h)
    · rw [cg,gx] at h
      exact (hx i h.symm).elim
    · rw [gx,cg] at h
      exact (hx j h).elim
    · rfl
  · intro a b
    rcases cases8 a with ⟨i,rfl⟩|rfl <;> rcases cases8 b with ⟨j,rfl⟩|rfl
    · simpa [cg,Rel8,i.isLt,j.isLt] using H.adj i j
    · rw [cg,gx,G.adj_comm]
      simpa [Rel8,i.isLt,show ¬(7 : Fin 8).val < 7 by decide] using hm i
    · rw [cg,gx]
      simpa [Rel8,j.isLt,show ¬(7 : Fin 8).val < 7 by decide] using hm j
    · rw [gx]
      change G.Adj x x ↔ False
      simp [G.loopless.irrefl]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem classify (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ p : Fin 7 → V, InducedPath G p) (h6 : ¬Nonempty (Hole G 6))
    {x : V} (hx : Outside H.c x) (adj : ∃ i, G.Adj x (H.c i)) :
    ∃ i, IsProfile H x i := by
  classical
  let b (i : Fin 7) := decide (G.Adj x (H.c i))
  let m := profileMask b
  have hm (i : Fin 7) : G.Adj x (H.c i) ↔ Mask m i := by
    rw [mask_cover b]
    simp [b]
  obtain ⟨i,hi⟩ := adj
  obtain ⟨g,ginj,_,_,gr⟩ := model8 H hx m hm
  obtain ⟨j,hj⟩ := sound g ginj gr _ (check_single m ⟨i,(hm _).mp hi⟩) h4 h7 h6
  exact ⟨j,hx,fun k => (hm k).trans (hj k)⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem single_front (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ p : Fin 7 → V, InducedPath G p) (h6 : ¬Nonempty (Hole G 6))
    {x y : V} {i j : Fin 7} (hx : IsProfile H x i) (hy : IsProfile H y j) :
    x=y := by
  classical
  apply Classical.byContradiction
  intro hxy
  let b := decide (G.Adj x y)
  have hb : b=true ↔ G.Adj x y := by simp [b]
  let g (k : Fin 9) := if hk : k.val<7 then H.c ⟨k.val,hk⟩ else if k=7 then x else y
  have cg (r : Fin 7) : g (Fin.castLE (by decide : 7 ≤ 9) r) = H.c r := by simp [g,r.isLt]
  have gx : g 7=x := rfl
  have gy : g 8=y := rfl
  have cases9 (k : Fin 9) : (∃ r : Fin 7, k = Fin.castLE (by decide : 7 ≤ 9) r) ∨ k=7 ∨ k=8 := by
    by_cases hk : k.val<7
    · exact Or.inl ⟨⟨_,hk⟩,Fin.ext rfl⟩
    · have h := k.isLt
      by_cases e : k.val=7
      · exact Or.inr (Or.inl (Fin.ext e))
      · exact Or.inr (Or.inr (Fin.ext (by change k.val=8; omega)))
  have gi : Function.Injective g := by
    intro a b h
    rcases cases9 a with ⟨r,rfl⟩|rfl|rfl <;> rcases cases9 b with ⟨s,rfl⟩|rfl|rfl
    · rw [cg,cg] at h
      exact congrArg (Fin.castLE (by decide : 7 ≤ 9)) (H.inj h)
    all_goals
      first
      | rfl
      | exfalso
        simp only [cg,gx,gy] at h
        first
        | exact hx.1 _ h
        | exact hx.1 _ h.symm
        | exact hy.1 _ h
        | exact hy.1 _ h.symm
        | exact hxy h
        | exact hxy h.symm
  have gr (a c : Fin 9) : G.Adj (g a) (g c) ↔ Rel9 i j b a c := by
    rcases cases9 a with ⟨r,rfl⟩|rfl|rfl <;> rcases cases9 c with ⟨s,rfl⟩|rfl|rfl
    · simpa [cg,Rel9,r.isLt,s.isLt] using H.adj r s
    · rw [cg,gx,G.adj_comm]
      simpa [Rel9,r.isLt,show ¬(7 : Fin 9).val < 7 by decide] using hx.2 r
    · rw [cg,gy,G.adj_comm]
      simpa [Rel9,r.isLt,show ¬(8 : Fin 9).val < 7 by decide,show (8 : Fin 9) ≠ 7 by decide] using hy.2 r
    · rw [cg,gx]
      simpa [Rel9,s.isLt,show ¬(7 : Fin 9).val < 7 by decide] using hx.2 s
    · simp [gx,G.loopless.irrefl,Rel9,show ¬(7 : Fin 9).val < 7 by decide]
    · rw [gx,gy]
      change G.Adj x y ↔ (7 : Fin 9) ≠ 8 ∧ b=true
      simpa [show (7 : Fin 9) ≠ 8 by decide] using hb.symm
    · rw [cg,gy]
      simpa [Rel9,s.isLt,show ¬(8 : Fin 9).val < 7 by decide,show (8 : Fin 9) ≠ 7 by decide] using hy.2 s
    · rw [gx,gy]
      change G.Adj y x ↔ (8 : Fin 9) ≠ 7 ∧ b=true
      rw [G.adj_comm]
      simpa [show (8 : Fin 9) ≠ 7 by decide] using hb.symm
    · simp [gy,G.loopless.irrefl,Rel9,show ¬(8 : Fin 9).val < 7 by decide]
  exact sound g gi gr _ (check_pair i j b) h4 h7 h6

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem rooted4 (H : Hole G 7) {x : V} {i : Fin 7} (hx : IsProfile H x i) :
    ∃ p : Fin 4 → V, InducedPath G p ∧ p 0=x ∧ ∀ j, 0<j.val → ∃ k, p j = H.c k := by
  let m := profileMask (Spoke i)
  have hm (j) : G.Adj x (H.c j) ↔ Mask m j := by
    rw [mask_cover (Spoke i)]
    simpa [Spoke] using hx.2 j
  obtain ⟨g,gi,cg,gx,gr⟩ := model8 H hx.1 m hm
  have er (a b : Fin 8) : Rel8 m a b ↔ SpokeRel (Spoke i) a b := by
    unfold Rel8 SpokeRel
    split <;> split <;> simp [m,mask_cover]
  obtain ⟨ri,rr,rt⟩ := rooted_check i
  refine ⟨g ∘ RootPath i,⟨gi.comp ri,fun a b h => (gr ..).trans ((er ..).trans (rr a b h))⟩,gx,?_⟩
  intro j hj
  let k : Fin 7 := ⟨_,rt j hj⟩
  exact ⟨k,(congrArg g (show RootPath i j=k.castSucc from Fin.ext rfl)).trans (cg k)⟩

end Graffiti133C7Only

end OMA133_C7OnlyCert

section OMA133_C7OnlyMain

namespace Graffiti133C7Only
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Graffiti133NoFive Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem local_bound {v : V} (A : Finset V)
    (hb : ∀ x, G.Adj v x → x ∈ A) : localIndependence G v ≤ A.card := by
  classical
  apply Finset.sup_le_iff.mpr
  intro s hs
  exact Finset.card_le_card fun w hw => hb w (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hs |>.1 w hw)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem oma133_C7OnlyMain_side_neighbor (h4 : FourCycleFree G) {v s : V} (e : G.Adj v s)
    (hv : 2 ≤ localIndependence G v) :
    ∃ w, G.Adj v w ∧ w ≠ s ∧ ¬G.Adj w s := by
  classical
  obtain ⟨A,hA,hM⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  have N (u) (hu : u ∈ A) := (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 u hu
  have no : ¬G.Adj x y := (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).2 x hx y hy
  by_cases ex : x = s
  · subst x
    exact ⟨y,N y hy,hxy.symm,fun h => no h.symm⟩
  by_cases ey : y = s
  · subst y
    exact ⟨x,N x hx,hxy,no⟩
  by_cases ex' : G.Adj x s
  · refine ⟨y,N y hy,ey,?_⟩
    intro ey'
    exact e.ne (h4 x y v s hxy (N x hx).symm (N y hy).symm ex' ey')
  · exact ⟨x,N x hx,ex,ex'⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem extension {n : ℕ} (hn : 0 < n) {p : Fin n → V} {x y : V}
    {U : V → Prop} (hp : InducedPath G p) (head : p ⟨0,hn⟩=x)
    (tail : ∀ i : Fin n, 0 < i.val → U (p i))
    (ex : G.Adj y x) (off : ∀ v, U v → y≠v ∧ ¬G.Adj y v) :
    ∃ q : Fin (n+1) → V, InducedPath G q ∧ q ⟨0,by omega⟩=y ∧
      ∀ i : Fin (n+1), 0 < i.val → q i=x ∨ U (q i) := by
  have no (i : Fin n) : y ≠ p i := by
    by_cases h : 0 < i.val
    · exact (off _ (tail _ h)).1
    · have eq : i=⟨0,hn⟩ := Fin.ext (by change i.val = 0; omega)
      rw [eq,head]
      exact ex.ne
  obtain ⟨q,hq,h0,hqt⟩ := prepend_induced_with_positions hn hp y no (head.symm ▸ ex)
    (fun i hi => (off _ (tail _ hi)).2)
  refine ⟨q,hq,h0,?_⟩
  intro i hi
  rw [hqt i hi]
  let j : Fin n := ⟨i.val-1,by have := i.isLt; omega⟩
  change p j=x ∨ U (p j)
  by_cases hj : 0 < j.val
  · exact Or.inr (tail _ hj)
  · exact Or.inl ((congrArg p (Fin.ext (by change j.val = 0; omega) : j=⟨0,hn⟩)).trans head)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem far_step (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ p : Fin 7 → V, InducedPath G p)
    (h6 : ¬Nonempty (Hole G 6)) (hl : ∀ v, 2 ≤ localIndependence G v)
    {x a b : V} {i : Fin 7} (hx : IsProfile H x i)
    (ha : OnlyFar H a) (hb : OnlyFar H b) (exa : G.Adj x a) (eab : G.Adj a b) :
    G.Adj x b := by
  classical
  by_contra noxb
  obtain ⟨c,ebc,can,eca⟩ := oma133_C7OnlyMain_side_neighbor h4 eab.symm (hl b)
  have xbn : x≠b := by
    intro e
    exact hb.2 i (e ▸ (hx.2 i).mpr (Or.inl rfl))
  have cOut (j) : c ≠ H.c j := fun e => hb.2 j (e ▸ ebc)
  have cneX : c≠x := fun e => noxb (e ▸ ebc.symm)
  have hc : OnlyFar H c := by
    refine ⟨cOut,?_⟩
    intro j e
    obtain ⟨k,hk⟩ := classify H h4 h7 h6 cOut ⟨j,e⟩
    exact cneX (single_front H h4 h7 h6 hk hx)
  have noxc : ¬G.Adj x c := by
    intro e
    exact can (h4 x b c a xbn e ebc exa eab.symm)
  obtain ⟨p,hp,h0,ht⟩ := rooted4 H hx
  obtain ⟨q,hq,q0,qt⟩ := extension (by decide) (U := fun z => ∃ j, z=H.c j) hp h0 ht
    exa.symm (by rintro v ⟨j,rfl⟩; exact ⟨ha.1 j,ha.2 j⟩)
  obtain ⟨r,hr,r0,rt⟩ := extension (by decide) (U := fun z => z=x ∨ ∃ j, z=H.c j) hq q0 qt eab.symm (by
    intro v hv
    rcases hv with rfl | ⟨j,rfl⟩
    · exact ⟨xbn.symm,fun e => noxb e.symm⟩
    · exact ⟨hb.1 j,hb.2 j⟩)
  obtain ⟨s,hs,_,_⟩ := extension (by decide) (U := fun z => z=a ∨ z=x ∨ ∃ j, z=H.c j) hr r0 rt ebc.symm (by
    intro v hv
    rcases hv with rfl | rfl | ⟨j,rfl⟩
    · exact ⟨can,eca⟩
    · exact ⟨cneX,fun e => noxc e.symm⟩
    · exact ⟨hc.1 j,hc.2 j⟩)
  exact h7 ⟨s,hs⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem no_far (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ p : Fin 7 → V, InducedPath G p)
    (h6 : ¬Nonempty (Hole G 6)) (conn : G.Connected)
    (hl : ∀ v, 2 ≤ localIndependence G v)
    {x : V} {i : Fin 7} (hx : IsProfile H x i) (b : V) : ¬OnlyFar H b := by
  classical
  have walkProp {u v : V} (p : G.Walk u v) (h : OnlyFar H v → G.Adj x v) :
      OnlyFar H u → G.Adj x u := by
    induction p with
    | nil => exact h
    | @cons u z v e p ih =>
      intro hu
      by_cases hz : Outside H.c z
      · by_cases hz' : OnlyFar H z
        · exact far_step H h4 h7 h6 hl hx hz' hu (ih h hz') e.symm
        · have contacts : ∃ j, G.Adj z (H.c j) := by
            by_contra n
            exact hz' ⟨hz,fun j ej => n ⟨j,ej⟩⟩
          obtain ⟨k,hk⟩ := classify H h4 h7 h6 hz contacts
          have eq := single_front H h4 h7 h6 hk hx
          exact eq ▸ e.symm
      · unfold Outside at hz
        push_neg at hz
        obtain ⟨j,rfl⟩ := hz
        exact (hu.2 j e).elim
  have allX (v : V) (hv : OnlyFar H v) : G.Adj x v := by
    obtain ⟨p⟩ := conn v x
    exact walkProp p (fun hf => (hf.2 i ((hx.2 i).mpr (Or.inl rfl))).elim) hv
  intro hf
  obtain ⟨c,hbc,hcn,hn⟩ := oma133_C7OnlyMain_side_neighbor h4 (allX b hf).symm (hl b)
  have cOut (j) : c ≠ H.c j := fun e => hf.2 j (e ▸ hbc)
  apply hn
  apply (allX c ⟨cOut,?_⟩).symm
  intro j e
  obtain ⟨k,hk⟩ := classify H h4 h7 h6 cOut ⟨j,e⟩
  exact hcn (single_front H h4 h7 h6 hk hx)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem covered_null (H : Hole G 7) (conn : G.Connected)
    (hn : ¬∃ x, Outside H.c x ∧ ∃ i, G.Adj x (H.c i)) (v : V) :
    ∃ i, v=H.c i := by
  classical
  have walkProp {u v : V} (p : G.Walk u v) (h : ∃ i, v=H.c i) :
      ∃ i, u=H.c i := by
    induction p with
    | nil => exact h
    | @cons u z v e p ih =>
      obtain ⟨i,hi⟩ := ih h
      by_contra bad
      push_neg at bad
      exact hn ⟨u,bad,i,hi ▸ e⟩
  obtain ⟨p⟩ := conn v (H.c 0)
  exact walkProp p ⟨0,rfl⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem cyclic_indices : ∀ i j : Fin 7, Cyclic i j → j=i+1 ∨ j=i+6 := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
private theorem profile_avoids_next : ∀ i : Fin 7, ¬Profile i (i+1) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
theorem sum_lt_three_of_hole_seven_no_six
    (H : Hole G 7) (h4 : FourCycleFree G)
    (h7 : ¬∃ p : Fin 7 → V, InducedPath G p)
    (h6 : ¬Nonempty (Hole G 6)) (conn : G.Connected)
    (hl : ∀ v, 2 ≤ localIndependence G v) :
    (∑ v : V, localIndependence G v) < 3 * Fintype.card V := by
  classical
  suffices (∀ v, localIndependence G v ≤ 3) ∧ ∃ v, localIndependence G v < 3 by
    obtain ⟨le, v, lt⟩ := this
    calc
      _ < ∑ _ : V, (3:ℕ) := Finset.sum_lt_sum (fun w _ => le w) ⟨v,Finset.mem_univ v,lt⟩
      _ = _ := by simp [Nat.mul_comm]
  by_cases hn : ∃ x, Outside H.c x ∧ ∃ i, G.Adj x (H.c i)
  · obtain ⟨x,hxo,has⟩ := hn
    obtain ⟨k,hx⟩ := classify H h4 h7 h6 hxo has
    have cover (v : V) : v=x ∨ ∃ i, v=H.c i := by
      by_cases hw : Outside H.c v
      · by_cases ha : ∃ i, G.Adj v (H.c i)
        · obtain ⟨i,hi⟩ := classify H h4 h7 h6 hw ha
          exact Or.inl (single_front H h4 h7 h6 hi hx)
        · push_neg at ha
          exact (no_far H h4 h7 h6 conn hl hx v ⟨hw,ha⟩).elim
      · unfold Outside at hw
        push_neg at hw
        exact Or.inr hw
    have cycleN (i j : Fin 7) (e : G.Adj (H.c i) (H.c j)) :
        j=i+1 ∨ j=i+6 := cyclic_indices _ _ ((H.adj _ _).mp e)
    constructor
    · intro v
      rcases cover v with rfl | ⟨i,rfl⟩
      · refine (local_bound ({H.c k,H.c (k+3),H.c (k+4)} : Finset V) ?_).trans ?_
        · intro w hw
          rcases cover w with rfl | ⟨i,rfl⟩
          · exact (G.loopless.irrefl _ hw).elim
          · rcases (hx.2 _).mp hw with rfl | rfl | rfl <;> simp
        · exact (Finset.card_insert_le _ _).trans
            (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
      · refine (local_bound ({x,H.c (i+1),H.c (i+6)} : Finset V) ?_).trans ?_
        · intro w hw
          rcases cover w with rfl | ⟨j,rfl⟩
          · simp
          · rcases cycleN _ _ hw with rfl | rfl <;> simp
        · exact (Finset.card_insert_le _ _).trans
            (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
    · refine ⟨H.c (k+1), lt_of_le_of_lt ((local_bound
          ({H.c (k+1+1),H.c (k+1+6)} : Finset V) ?_).trans ?_) (by decide : 2 < 3)⟩
      · intro w hw
        rcases cover w with rfl | ⟨j,rfl⟩
        · exact (profile_avoids_next k ((hx.2 _).mp hw.symm)).elim
        · rcases cycleN _ _ hw with rfl | rfl <;> simp
      · exact (Finset.card_insert_le _ _).trans (by simp)
  · have le (v : V) : localIndependence G v ≤ 2 := by
      obtain ⟨i,rfl⟩ := covered_null H conn hn v
      refine (local_bound ({H.c (i+1),H.c (i+6)} : Finset V) ?_).trans
        ((Finset.card_insert_le _ _).trans (by simp))
      intro w hw
      obtain ⟨j,rfl⟩ := covered_null H conn hn w
      rcases cyclic_indices _ _ ((H.adj _ _).mp hw) with rfl | rfl <;> simp
    exact ⟨fun v => (le v).trans (by decide),H.c 0,(le (H.c 0)).trans_lt (by decide : 2 < 3)⟩

end Graffiti133C7Only

end OMA133_C7OnlyMain

section OMA133_HexFlattened133

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133NoFive Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem prepend_keep {k : ℕ} (hk : 0 < k) {p : Fin k → V} (hp : InducedPath G p)
    (x : V) (off : ∀ i, x ≠ p i) (h0 : G.Adj x (p ⟨0,hk⟩))
    (tail : ∀ i : Fin k, 0 < i.val → ¬G.Adj x (p i)) :
    ∃ q : Fin (k+1) → V, InducedPath G q ∧ q ⟨0,by omega⟩=x ∧
      (∀ i : Fin (k+1), 0 < i.val → ∃ j, q i=p j) := by
  obtain ⟨q,hq,h0,ht⟩ := prepend_induced_with_positions hk hp x off h0 tail
  exact ⟨q,hq,h0,fun i hi => ⟨_,ht i hi⟩⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem tail_union {k : ℕ} (hk : 0 < k) {p : Fin k → V} {x : V}
    (head : p ⟨0,hk⟩=x) (Q : V → Prop) (rest : ∀ i, 0 < i.val → Q (p i)) :
    ∀ i, p i=x ∨ Q (p i) := by
  intro i
  by_cases h : i.val = 0
  · have eq : i = ⟨0,hk⟩ := Fin.ext h
    exact Or.inl (eq.symm ▸ head)
  · exact Or.inr (rest i (Nat.pos_of_ne_zero h))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem far_not_opp {x y : V} {i : Fin 3} (hx : F.Opp x i) (hy : F.Far y) :
    y ≠ x := by
  intro eq
  exact hy.2 (frontInd i) (eq.symm ▸ (hx.2 _).mpr (Or.inl rfl))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
theorem far_P3_middle {x a b c : V} {i : Fin 3} (hx : F.Opp x i)
    (ha : F.Far a) (hb : F.Far b) (hc : F.Far c)
    (xa : G.Adj x a) (ab : G.Adj a b) (bc : G.Adj b c)
    (ac : ¬G.Adj a c) (acne : a ≠ c) : G.Adj x b := by
  classical
  apply Classical.byContradiction
  intro nxb
  have nxc : ¬G.Adj x c := by
    intro xc
    exact acne (F.h4 x b a c (F.far_not_opp hx hb).symm xa ab.symm xc bc)
  obtain ⟨p,hp,h0,ht⟩ := F.rooted4 hx
  change p (0:Fin 4)=x at h0
  have hpAll (i : Fin 4) : p i = x ∨ ∃ j, p i = F.c j :=
    tail_union (by decide) h0 (fun v => ∃ j, v=F.c j) ht i
  have offA (i : Fin 4) : a ≠ p i := by
    intro eq
    rcases hpAll i with ex | ⟨j,ej⟩
    · exact (F.far_not_opp hx ha) (eq.trans ex)
    · exact ha.1 j (eq.trans ej)
  have aTail (i : Fin 4) (hi : 0 < i.val) : ¬G.Adj a (p i) := by
    obtain ⟨j,hj⟩ := ht i hi
    exact fun e => ha.2 j (hj ▸ e)
  obtain ⟨q,hq,q0,qt⟩ := prepend_keep (by decide) hp a offA (h0.symm ▸ xa.symm) aTail
  change q (0:Fin 5)=a at q0
  have qAll := tail_union (by decide) q0 (fun v => ∃ j, v=p j) qt
  have offB (i : Fin 5) : b ≠ q i := by
    intro eq
    rcases qAll i with ea | ⟨j,ej⟩
    · exact ab.ne (eq.trans ea).symm
    · have h := eq.trans ej
      rcases hpAll j with ex | ⟨k,ek⟩
      · exact (F.far_not_opp hx hb) (h.trans ex)
      · exact hb.1 k (h.trans ek)
  have bTail (i : Fin 5) (hi : 0 < i.val) : ¬G.Adj b (q i) := by
    intro h
    obtain ⟨j,hj⟩ := qt i hi
    have h' : G.Adj b (p j) := hj ▸ h
    rcases hpAll j with ex | ⟨k,ek⟩
    · exact nxb (ex ▸ h'.symm)
    · exact hb.2 k (ek ▸ h')
  obtain ⟨r,hr,r0,rt⟩ := prepend_keep (by decide) hq b offB (q0.symm ▸ ab.symm) bTail
  change r (0:Fin 6)=b at r0
  have rAll := tail_union (by decide) r0 (fun v => ∃ j, v=q j) rt
  have offC (i : Fin 6) : c ≠ r i := by
    intro eq
    rcases rAll i with eb | ⟨j,ej⟩
    · exact bc.ne (eq.trans eb).symm
    · have h := eq.trans ej
      rcases qAll j with ea | ⟨k,ek⟩
      · exact acne (h.trans ea).symm
      · have h' := h.trans ek
        rcases hpAll k with ex | ⟨l,el⟩
        · exact (F.far_not_opp hx hc) (h'.trans ex)
        · exact hc.1 l (h'.trans el)
  have cTail (i : Fin 6) (hi : 0 < i.val) : ¬G.Adj c (r i) := by
    intro h
    obtain ⟨j,hj⟩ := rt i hi
    have h' : G.Adj c (q j) := hj ▸ h
    rcases qAll j with ea | ⟨k,ek⟩
    · exact ac (ea ▸ h'.symm)
    · have h'' : G.Adj c (p k) := ek ▸ h'
      rcases hpAll k with ex | ⟨l,el⟩
      · exact nxc (ex ▸ h''.symm)
      · exact hc.2 l (el ▸ h'')
  obtain ⟨s,hs,_,_⟩ := prepend_keep (by decide) hr c offC (r0.symm ▸ bc.symm) cTail
  exact F.no7 ⟨s,hs⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem independent_pair (x : V) (h : 2 ≤ localIndependence G x) :
    ∃ y z, y ≠ z ∧ G.Adj x y ∧ G.Adj x z ∧ ¬G.Adj y z := by
  classical
  obtain ⟨A,hA,hc⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
  obtain ⟨y,hy,z,hz,hD⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  exact ⟨y,z,hD,hN _ hy,hN _ hz,hI _ hy _ hz⟩

include F in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private theorem oma133_HexFlattened133_side_neighbor {x y : V} (e : G.Adj x y) (h : 2 ≤ localIndependence G x) :
    ∃ z, G.Adj x z ∧ y ≠ z ∧ ¬G.Adj y z := by
  obtain ⟨a,b,ab,ha,hb,nab⟩ := independent_pair x h
  by_cases ay : a=y
  · exact ⟨b,hb,ay ▸ ab,ay ▸ nab⟩
  by_cases by' : b=y
  · exact ⟨a,ha,(by' ▸ ab).symm,fun e => nab (by' ▸ e.symm)⟩
  by_cases ey : G.Adj y a
  · have hB : ¬G.Adj y b := fun e' => ab (F.h4 x y a b e.ne ha ey hb e')
    exact ⟨b,hb,fun e => by' e.symm,hB⟩
  · exact ⟨a,ha,fun e => ay e.symm,ey⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
theorem far_neighbor_opp {x y : V} (hy : F.Far y) (ey : G.Adj x y)
    (hx : ¬ F.Far x) : ∃ i, F.Opp x i := by
  classical
  have out : Outside F.c x := fun i e => hy.2 i ((e ▸ ey).symm)
  have nh : ∃ i, G.Adj x (F.c i) := by
    apply Classical.byContradiction
    intro no
    exact hx ⟨out,fun i e => no ⟨i,e⟩⟩
  exact F.far_edge_opposite ⟨out,nh⟩ hy ey

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
theorem far_has_opp (hc : G.Connected) (hmin : ∀ v, 2 ≤ localIndependence G v) :
    ∀ v, F.Far v → ∃ x i, F.Opp x i ∧ G.Adj x v := by
  classical
  let prop (v : V) : Prop := F.Far v → ∃ x i, F.Opp x i ∧ G.Adj x v
  have step (a b : V) (e : G.Adj a b) (hA : prop a) : prop b := by
    intro hb
    by_cases ha : F.Far a
    · obtain ⟨x,i,hx,xa⟩ := hA ha
      by_cases got : G.Adj x b
      · exact ⟨x,i,hx,got⟩
      · obtain ⟨c,bc,ane,nac⟩ := F.oma133_HexFlattened133_side_neighbor e.symm (hmin b)
        by_cases hh : F.Far c
        · exact (got (F.far_P3_middle hx ha hb hh xa e bc nac ane)).elim
        · obtain ⟨j,hj⟩ := F.far_neighbor_opp hb bc.symm hh
          exact ⟨c,j,hj,bc.symm⟩
    · obtain ⟨i,hi⟩ := F.far_neighbor_opp hb e ha
      exact ⟨a,i,hi,e⟩
  intro v
  obtain ⟨p⟩ := hc (F.c 0) v
  have hwalk {a b : V} (p : G.Walk a b) (ha : prop a) : prop b := by
    induction p with
    | nil => exact ha
    | cons e p ih => exact ih (step _ _ e ha)
  exact hwalk p (fun h => (h.1 0 rfl).elim)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma anti_ne : ∀ i : Fin 3, frontInd i ≠ frontInd i+3 := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
theorem opp_unique {x y : V} {i : Fin 3} (hx : F.Opp x i) (hy : F.Opp y i) : x=y := by
  exact F.h4 (F.c (frontInd i)) (F.c (frontInd i+3)) x y
    (F.inj.ne (anti_ne i)) ((hx.2 _).mpr (Or.inl rfl)).symm ((hx.2 _).mpr (Or.inr rfl)).symm
    ((hy.2 _).mpr (Or.inl rfl)).symm ((hy.2 _).mpr (Or.inr rfl)).symm

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
private lemma opp_adj_site : ∀ i j : Fin 3, i ≠ j →
    ∃ a b : Fin 6, (a=frontInd i ∨ a=frontInd i+3) ∧
      (b=frontInd j ∨ b=frontInd j+3) ∧ Cyclic a b := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
theorem opp_independent {x y : V} {i j : Fin 3} (hx : F.Opp x i) (hy : F.Opp y j) :
    ¬ G.Adj x y := by
  by_cases he : i=j
  · have e := F.opp_unique hx (he.symm ▸ hy)
    exact fun h => h.ne e
  · obtain ⟨a,b,ha,hb,ee⟩ := opp_adj_site i j he
    exact fun e => F.contact_forbid hx.1 hy.1 e ((hx.2 _).mpr ha) ((hy.2 _).mpr hb) ee

end Frame
end Graffiti133Hex

namespace Graffiti133Hex
open SimpleGraph Graffiti133 Graffiti133NoFive

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def SmallRel {k : ℕ} (B : Fin k → Fin 6 → Bool) (E : Fin k → Fin k → Bool)
    (x y : Fin (6+k)) : Prop :=
  if hx : x.val < 6 then
    if hy : y.val < 6 then Cyclic ⟨x.val,hx⟩ ⟨y.val,hy⟩
    else B ⟨y.val-6,by omega⟩ ⟨x.val,hx⟩ = true
  else if hy : y.val < 6 then B ⟨x.val-6,by omega⟩ ⟨y.val,hy⟩ = true
  else E ⟨x.val-6,by omega⟩ ⟨y.val-6,by omega⟩ = true

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
noncomputable instance {k : ℕ} (B : Fin k → Fin 6 → Bool) (E : Fin k → Fin k → Bool) :
    DecidableRel (SmallRel B E) := by
  intro i j
  unfold SmallRel
  split <;> split <;> infer_instance

inductive SmallCert (n : ℕ)
| four (i j a b : Fin n)
| path (p : Fin 7 → Fin n)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def CertTrue {n : ℕ} (R : Fin n → Fin n → Prop) : SmallCert n → Prop
| .four i j a b => i ≠ j ∧ a ≠ b ∧ R i a ∧ R j a ∧ R i b ∧ R j b
| .path p => (∀ i j, p i = p j → i = j) ∧ ∀ i j, i < j → (R (p i) (p j) ↔ i.val+1=j.val)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
noncomputable instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    DecidablePred (CertTrue R) := by
  intro e
  cases e <;> unfold CertTrue <;> infer_instance

namespace Frame
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem reject_small {k : ℕ} {B : Fin k → Fin 6 → Bool} {E : Fin k → Fin k → Bool}
    (e : Fin k → V) (inj : Function.Injective e) (off : ∀ i, Outside F.c (e i))
    (hB : ∀ u j, B u j=true ↔ G.Adj (e u) (F.c j))
    (hE : ∀ u v, E u v=true ↔ G.Adj (e u) (e v))
    (cert : SmallCert (6+k)) (checked : CertTrue (SmallRel B E) cert) : False := by
  let g (i : Fin (6+k)) : V :=
    if hi : i.val < 6 then F.c ⟨i.val,hi⟩ else e ⟨i.val-6,by omega⟩
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < 6 <;> by_cases hB : b.val < 6
    · have he := F.inj (show F.c ⟨a.val,hA⟩ = F.c ⟨b.val,hB⟩ by
        simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun z : Fin 6 => z.val) he)
    · exact (off ⟨b.val-6,by omega⟩ ⟨a.val,hA⟩
        (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm)).elim
    · exact (off ⟨a.val-6,by omega⟩ ⟨b.val,hB⟩
        (by simpa only [g,dif_neg hA,dif_pos hB] using eq)).elim
    · have he := inj (show e ⟨a.val-6,by omega⟩ = e ⟨b.val-6,by omega⟩ by
        simpa only [g,dif_neg hA,dif_neg hB] using eq)
      apply Fin.ext
      have hh := congrArg (fun z : Fin k => z.val) he
      change a.val-6=b.val-6 at hh
      omega
  have lift (a b : Fin (6+k)) : G.Adj (g a) (g b) ↔ SmallRel B E a b := by
    by_cases hA : a.val < 6 <;> by_cases hD : b.val < 6
    · simpa only [g,SmallRel,dif_pos hA,dif_pos hD] using F.adj ⟨a.val,hA⟩ ⟨b.val,hD⟩
    · simpa only [g,SmallRel,dif_pos hA,dif_neg hD,G.adj_comm] using (hB ⟨b.val-6,by omega⟩ ⟨a.val,hA⟩).symm
    · simpa only [g,SmallRel,dif_neg hA,dif_pos hD] using (hB ⟨a.val-6,by omega⟩ ⟨b.val,hD⟩).symm
    · simpa only [g,SmallRel,dif_neg hA,dif_neg hD] using (hE ⟨a.val-6,by omega⟩ ⟨b.val-6,by omega⟩).symm
  cases cert with
  | four i j a b =>
    obtain ⟨ne,nb,ia,ja,ib,jb⟩ := checked
    exact nb (ginj (F.h4 _ _ _ _ (fun h => ne (ginj h)) ((lift _ _).mpr ia)
      ((lift _ _).mpr ja) ((lift _ _).mpr ib) ((lift _ _).mpr jb)))
  | path p =>
    obtain ⟨hi,he⟩ := checked
    exact F.no7 ⟨g ∘ p,ginj.comp hi,fun i j ht => (lift _ _).trans (he i j ht)⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
def contact (t : Fin 15) (i : Fin 6) : Prop :=
  if h : t.val < 6 then i = (⟨t.val,h⟩ : Fin 6)
  else if h' : t.val < 12 then i = (⟨t.val-6,by omega⟩ : Fin 6) ∨
    i = (⟨t.val-6,by omega⟩ : Fin 6)+1
  else i = (⟨t.val-12,by have := t.isLt; omega⟩ : Fin 6) ∨
    i = (⟨t.val-12,by have := t.isLt; omega⟩ : Fin 6)+3

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
noncomputable instance (t : Fin 15) : DecidablePred (contact t) := by
  intro i
  unfold contact
  split
  · infer_instance
  · split <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
noncomputable def contactsB (t : Fin 15) (i : Fin 6) : Bool := decide (contact t i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem profile_exists {x : V} (h : F.Near x) :
    ∃ t, ∀ i, contactsB t i=true ↔ G.Adj x (F.c i) := by
  classical
  rcases F.classify h with a | b | c
  · obtain ⟨i,hi⟩ := a
    use ⟨i.val,by have := i.isLt; omega⟩
    intro j
    have he := i.isLt
    simp [contactsB,contact,he,hi.2]
  · obtain ⟨i,hi⟩ := b
    use ⟨i.val+6,by have := i.isLt; omega⟩
    intro j
    have hL : ¬i.val+6<6 := by omega
    have hU : i.val+6<12 := by have := i.isLt; omega
    have hi' : (⟨i.val+6-6,by omega⟩ : Fin 6)=i := Fin.ext (by simp)
    simp [contactsB,contact,hL,hU,hi',hi.2]
  · obtain ⟨i,hi⟩ := c
    use ⟨i.val+12,by have := i.isLt; omega⟩
    intro j
    have hL : ¬i.val+12<6 := by omega
    have hU : ¬i.val+12<12 := by omega
    have hi' : (⟨i.val+12-12,by have := i.isLt; omega⟩ : Fin 6)=frontInd i := Fin.ext (by simp [frontInd])
    rw [contactsB,decide_eq_true_eq,contact,dif_neg hL,dif_neg hU,hi']
    exact (hi.2 j).symm

end Frame
end Graffiti133Hex

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
private noncomputable def oppB (i : Fin 4) : Fin 6 → Bool :=
  if h : i.val<3 then contactsB ⟨12+i.val,by omega⟩ else fun _ => false

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
private def oppE (k : Fin 3) (i j : Fin 4) : Bool :=
  decide ((i=3 ∧ j.val<3 ∧ j.val≠k.val) ∨ (j=3 ∧ i.val<3 ∧ i.val≠k.val))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
private def pathThree (k : Fin 3) : Fin 7 → Fin 10 := match k.val with
| 0 => ![0,6,3,2,8,9,7]
| 1 => ![1,7,4,3,6,9,8]
| _ => ![2,8,5,0,6,9,7]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
private lemma checkedThree : ∀ k : Fin 3, CertTrue (SmallRel oppB (oppE k)) (.path (pathThree k)) := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
private lemma oppB_spec : ∀ a : Fin 3, ∀ j : Fin 6,
    oppB (a.castLE (by decide)) j=true ↔ j=frontInd a ∨ j=frontInd a+3 := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
theorem far_forbid_two_of_three {x : V} (hx : F.Far x)
    (o : Fin 3 → V) (ho : ∀ i, F.Opp (o i) i)
    (k : Fin 3) (hA : ∀ i, G.Adj x (o i) ↔ i ≠ k) :
    False := by
  classical
  let e (i : Fin 4) := if h : i.val<3 then o ⟨i.val,h⟩ else x
  have eo (i : Fin 3) : e (i.castLE (by decide)) = o i := by simp [e,i.isLt]
  have ex : e 3=x := rfl
  have decomp : ∀ i : Fin 4, (∃ a : Fin 3, i=a.castLE (by decide)) ∨ i=3 := by decide
  have oinj : Function.Injective o := by
    intro i j eq
    have hh : G.Adj (o j) (F.c (frontInd i)) := eq ▸ ((ho i).2 _).mpr (Or.inl rfl)
    have key : ∀ i j : Fin 3, frontInd i=frontInd j ∨ frontInd i=frontInd j+3 → i=j := by decide
    exact key i j ((ho j).2 _ |>.mp hh)
  have noX (i : Fin 3) : x ≠ o i := by
    intro eq
    exact hx.2 (frontInd i) (eq.symm ▸ ((ho i).2 _ |>.mpr (Or.inl rfl)))
  have einj : Function.Injective e := by
    intro a b eq
    rcases decomp a with ⟨i,rfl⟩ | rfl <;> rcases decomp b with ⟨j,rfl⟩ | rfl
    · rw [eo,eo] at eq
      exact congrArg (Fin.castLE (by decide : 3≤4)) (oinj eq)
    · rw [eo,ex] at eq
      exact (noX _ eq.symm).elim
    · rw [ex,eo] at eq
      exact (noX _ eq).elim
    · rfl
  have off (i : Fin 4) : Outside F.c (e i) := by
    rcases decomp i with ⟨j,rfl⟩ | rfl
    · rw [eo]
      exact (ho j).1
    · rw [ex]
      exact hx.1
  have hB (i : Fin 4) (j : Fin 6) : oppB i j=true ↔ G.Adj (e i) (F.c j) := by
    rcases decomp i with ⟨a,rfl⟩ | rfl
    · rw [eo]
      exact (oppB_spec _ _).trans ((ho a).2 _).symm
    · rw [ex]
      change false = true ↔ G.Adj x (F.c j)
      simp [hx.2 j]
  have hE (u v : Fin 4) : oppE k u v=true ↔ G.Adj (e u) (e v) := by
    rcases decomp u with ⟨a,rfl⟩ | rfl <;> rcases decomp v with ⟨b,rfl⟩ | rfl
    · rw [eo,eo]
      have n : ¬G.Adj (o a) (o b) := F.opp_independent (ho a) (ho b)
      have ne : ∀ a : Fin 3, a.castLE (of_decide_eq_true rfl : 3≤4) ≠ (3 : Fin 4) := by decide
      simp [oppE,ne,n]
    · rw [eo,ex,G.adj_comm,hA]
      have ht (a : Fin 3) : a.castLE (of_decide_eq_true rfl : 3≤4) ≠ (3 : Fin 4) :=
        (by decide : ∀ a : Fin 3, a.castLE (of_decide_eq_true rfl : 3≤4) ≠ (3 : Fin 4)) a
      simp [oppE,ht,a.isLt,Fin.ext_iff]
    · rw [ex,eo,hA]
      have ht (a : Fin 3) : a.castLE (of_decide_eq_true rfl : 3≤4) ≠ (3 : Fin 4) :=
        (by decide : ∀ a : Fin 3, a.castLE (of_decide_eq_true rfl : 3≤4) ≠ (3 : Fin 4)) a
      simp [oppE,ht,b.isLt,Fin.ext_iff]
    · rw [ex]
      have n : ¬((3 : Fin 4).val<3) := by decide
      simp [oppE,n,G.loopless.irrefl]
  exact F.reject_small e einj off hB hE (.path (pathThree k)) (checkedThree k)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
noncomputable def oppSet : Finset V := by
  classical exact Finset.univ.filter (fun x => ∃ i, F.Opp x i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
theorem mem_oppSet (v : V) : v ∈ F.oppSet ↔ ∃ i, F.Opp v i := by
  classical simp [oppSet]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
noncomputable def oppNeighbors (v : V) : Finset V := by
  classical exact F.oppSet.filter (G.Adj v)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
theorem mem_oppNeighbors (v x : V) : x ∈ F.oppNeighbors v ↔ x ∈ F.oppSet ∧ G.Adj v x := by
  classical simp [oppNeighbors]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
private noncomputable def oppIndex (v : V) : Fin 3 := by
  classical exact if h : ∃ i, F.Opp v i then Classical.choose h else 0

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
private theorem oppIndex_valid {v : V} (hv : v ∈ F.oppSet) : F.Opp v (F.oppIndex v) := by
  classical
  have h := (F.mem_oppSet v).mp hv
  unfold oppIndex
  rw [dif_pos h]
  exact Classical.choose_spec h

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
private theorem oppIndex_inj : Set.InjOn F.oppIndex (↑F.oppSet : Set V) := by
  intro x hx y hy he
  exact F.opp_unique (F.oppIndex_valid hx) (he.symm ▸ F.oppIndex_valid hy)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
theorem card_oppSet : F.oppSet.card ≤ 3 := by
  classical
  have h := Finset.card_le_card_of_injOn F.oppIndex
    (t:=(Finset.univ : Finset (Fin 3))) (fun _ _ => Finset.mem_univ _) F.oppIndex_inj
  simpa using h

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
private theorem all_opp_present (hC : F.oppSet.card=3) :
    ∃ o : Fin 3 → V, (∀ i, F.Opp (o i) i) ∧ ∀ x, x∈F.oppSet → ∃ i, o i=x := by
  classical
  have hc : (F.oppSet.image F.oppIndex).card=3 := by
    rw [Finset.card_image_of_injOn F.oppIndex_inj,hC]
  have eq : F.oppSet.image F.oppIndex = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hc])
  have choices (i : Fin 3) : ∃ x, F.Opp x i := by
    obtain ⟨x,hx,hi⟩ := Finset.mem_image.mp (show i ∈ F.oppSet.image F.oppIndex by simp [eq])
    exact ⟨x,hi ▸ F.oppIndex_valid hx⟩
  let o (i : Fin 3) := Classical.choose (choices i)
  have ho (i : Fin 3) : F.Opp (o i) i := Classical.choose_spec (choices i)
  refine ⟨o,ho,?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := (F.mem_oppSet x).mp hx
  exact ⟨j,F.opp_unique (ho j) hj⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
theorem far_one_or_all (hc : G.Connected) (hmin : ∀ v, 2 ≤ localIndependence G v)
    {v : V} (hv : F.Far v) :
    (F.oppNeighbors v).card=1 ∨ F.oppNeighbors v=F.oppSet := by
  classical
  let N := F.oppNeighbors v
  have sub : N ⊆ F.oppSet := Finset.filter_subset _ _
  have cb := Finset.card_le_card sub
  have cf := F.card_oppSet
  obtain ⟨x,i,hi,e⟩ := F.far_has_opp hc hmin v hv
  have pos : 0 < N.card := Finset.card_pos.mpr
    ⟨x,(F.mem_oppNeighbors v x).mpr ⟨(F.mem_oppSet x).mpr ⟨i,hi⟩,e.symm⟩⟩
  by_cases hl : N.card = 1
  · exact Or.inl hl
  by_cases he : N=F.oppSet
  · exact Or.inr he
  have hlt : N.card < F.oppSet.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,he⟩)
  have h2 : N.card=2 := by omega
  have h3 : F.oppSet.card=3 := by omega
  obtain ⟨o,ho,cover⟩ := F.all_opp_present h3
  have hole : ∃ y, y∈F.oppSet ∧ y∉N := by
    apply Classical.byContradiction
    intro no
    exact he (Finset.Subset.antisymm sub (fun y hy => Classical.byContradiction
      (fun no' => no ⟨y,hy,no'⟩)))
  obtain ⟨y,hy,hyn⟩ := hole
  obtain ⟨k,ey⟩ := cover y hy
  have hNotK : ¬G.Adj v (o k) := by
    rw [ey]
    exact fun e' => hyn ((F.mem_oppNeighbors v y).mpr ⟨hy,e'⟩)
  have hAll (i : Fin 3) : G.Adj v (o i) ↔ i≠k := by
    refine ⟨fun e h => hNotK (h ▸ e),?_⟩
    intro hik
    apply Classical.byContradiction
    intro hNotI
    have oI : o i ∈ F.oppSet := (F.mem_oppSet _).mpr ⟨i,ho i⟩
    have ni : o i ∉ N := fun h => hNotI ((F.mem_oppNeighbors _ _).mp h).2
    have oK : o k ∈ F.oppSet := (F.mem_oppSet _).mpr ⟨k,ho k⟩
    have nk : o k ∉ N := fun h => hNotK ((F.mem_oppNeighbors _ _).mp h).2
    have oNe : o i ≠ o k := by
      intro he'
      have hh := (ho k).2 (frontInd i) |>.mp (he' ▸ (ho i).2 _ |>.mpr (Or.inl rfl))
      exact hik ((by decide : ∀ i k : Fin 3, frontInd i=frontInd k ∨ frontInd i=frontInd k+3 → i=k) i k hh)
    have addSub : insert (o i) (insert (o k) N) ⊆ F.oppSet :=
      Finset.insert_subset oI (Finset.insert_subset oK sub)
    have cc := Finset.card_le_card addSub
    rw [Finset.card_insert_of_notMem (by simp [oNe,ni]),Finset.card_insert_of_notMem nk] at cc
    omega
  exact (F.far_forbid_two_of_three hv o ho k hAll).elim

end Frame
end Graffiti133Hex

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem far_seat_bound (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r)
    {v : V} (hv : F.Far v) :
    localIndependence G v ≤ max 2 (F.oppNeighbors v).card := by
  classical
  obtain ⟨A,hA,hcard⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  have farOr (a : V) (ha : a ∈ A) :
      F.Far a ∨ a ∈ F.oppNeighbors v := by
    by_cases ht : F.Far a
    · exact Or.inl ht
    · obtain ⟨i,hi⟩ := F.far_neighbor_opp hv (hN _ ha).symm ht
      exact Or.inr ((F.mem_oppNeighbors _ _).mpr ⟨(F.mem_oppSet _).mpr ⟨i,hi⟩,hN _ ha⟩)
  rcases F.far_one_or_all hc hm hv with hOne | hAll
  · let B := A.filter F.Far
    have hb : B.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨haA,haf⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbA,hbf⟩ := Finset.mem_filter.mp hb
      by_contra hne
      obtain ⟨o,i,hoi,hoa⟩ := F.far_has_opp hc hm a haf
      obtain ⟨p,j,hpj,hpb⟩ := F.far_has_opp hc hm b hbf
      have ov := F.far_P3_middle hoi haf hv hbf hoa (hN _ haA).symm (hN _ hbA) (hI _ haA _ hbA) hne
      have pv := F.far_P3_middle hpj hbf hv haf hpb (hN _ hbA).symm (hN _ haA)
        (hI _ hbA _ haA) (fun q => hne q.symm)
      have ho := (F.mem_oppNeighbors v o).mpr ⟨(F.mem_oppSet o).mpr ⟨i,hoi⟩,ov.symm⟩
      have hp := (F.mem_oppNeighbors v p).mpr ⟨(F.mem_oppSet p).mpr ⟨j,hpj⟩,pv.symm⟩
      have eq := Finset.card_le_one.mp (show (F.oppNeighbors v).card ≤ 1 by omega) o ho p hp
      have ne : v ≠ o := fun e => hv.2 (frontInd i) (e.symm ▸ (hoi.2 _).mpr (Or.inl rfl))
      exact hne (F.h4 v o a b ne (hN _ haA) hoa (hN _ hbA) (eq.symm ▸ hpb))
    have sub : A ⊆ B ∪ F.oppNeighbors v := by
      intro a ha
      exact Finset.mem_union.mpr ((farOr a ha).imp (fun h => Finset.mem_filter.mpr ⟨ha,h⟩) id)
    have hh := (Finset.card_le_card sub).trans (Finset.card_union_le B (F.oppNeighbors v))
    omega
  · have chooseSeat (a : V) (ha : a ∈ A) :
        ∃ o ∈ F.oppNeighbors v, a = o ∨ G.Adj a o := by
      rcases farOr a ha with hf | hn
      · obtain ⟨o,i,hoi,hoa⟩ := F.far_has_opp hc hm a hf
        exact ⟨o, hAll.symm ▸ (F.mem_oppSet o).mpr ⟨i,hoi⟩, Or.inr hoa.symm⟩
      · exact ⟨a,hn,Or.inl rfl⟩
    let seat (a : V) := if h : a∈A then Classical.choose (chooseSeat a h) else v
    have hs {a : V} (ha : a∈A) :
        seat a ∈ F.oppNeighbors v ∧ (a=seat a ∨ G.Adj a (seat a)) := by
      simp only [seat,dif_pos ha]
      exact Classical.choose_spec (chooseSeat a ha)
    have hinj : Set.InjOn seat (↑A : Set V) := by
      intro a ha b hb e
      rcases (hs ha).2 with ha' | ha' <;> rcases (hs hb).2 with hb' | hb'
      · exact ha'.trans (e.trans hb'.symm)
      · exfalso
        exact hI _ ha _ hb ((ha'.trans e).symm ▸ hb'.symm)
      · exfalso
        exact hI _ ha _ hb ((hb'.trans e.symm).symm ▸ ha')
      · have hsv : G.Adj v (seat a) := ((F.mem_oppNeighbors _ _).mp (hs ha).1).2
        exact F.h4 v (seat a) a b hsv.ne (hN _ ha) ha'.symm (hN _ hb) (e.symm ▸ hb'.symm)
    exact hcard ▸ (Finset.card_le_card_of_injOn seat (fun _ ha => (hs ha).1) hinj).trans (le_max_right _ _)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
noncomputable def farSet : Finset V := by
  classical exact Finset.univ.filter F.Far

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem mem_farSet (v : V) : v ∈ F.farSet ↔ F.Far v := by
  classical simp [farSet]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem far_global_budget (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r) :
    (∑ r ∈ F.farSet, (localIndependence G r + (F.oppNeighbors r).card))
      ≤ 3 * F.farSet.card + 3 := by
  classical
  let K (r : V) := (F.oppNeighbors r).offDiag
  have hsub : F.farSet.biUnion K ⊆ F.oppSet.offDiag := by
    intro p hp
    obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨ha,hb,hn⟩ := Finset.mem_offDiag.mp hr
    exact Finset.mem_offDiag.mpr ⟨((F.mem_oppNeighbors _ _).mp ha).1,
      ((F.mem_oppNeighbors _ _).mp hb).1,hn⟩
  have hd : (↑F.farSet : Set V).PairwiseDisjoint K := by
    intro r _ s _ rs
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨ha,hb,hn⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨ha',hb',_⟩ := Finset.mem_offDiag.mp hq
    exact rs (F.h4 p.1 p.2 r s hn ((F.mem_oppNeighbors _ _).mp ha).2.symm
      ((F.mem_oppNeighbors _ _).mp hb).2.symm ((F.mem_oppNeighbors _ _).mp ha').2.symm
      ((F.mem_oppNeighbors _ _).mp hb').2.symm)
  have h6 : F.oppSet.offDiag.card ≤ 6 := by
    rw [Finset.offDiag_card]
    have h := F.card_oppSet
    have cases : F.oppSet.card=0 ∨ F.oppSet.card=1 ∨ F.oppSet.card=2 ∨ F.oppSet.card=3 := by omega
    rcases cases with z | z | z | z <;> rw [z] <;> decide
  have hK : (∑ r ∈ F.farSet, (K r).card) ≤ 6 := by
    rw [← Finset.card_biUnion hd]
    exact (Finset.card_le_card hsub).trans h6
  have step (r : V) (hr : r∈F.farSet) :
      2 * (localIndependence G r + (F.oppNeighbors r).card) ≤ 6 + (K r).card := by
    have hv := (F.mem_farSet r).mp hr
    have hs := F.far_seat_bound hc hm hv
    obtain ⟨x,i,hi,e⟩ := F.far_has_opp hc hm r hv
    have hp : 0 < (F.oppNeighbors r).card := Finset.card_pos.mpr
      ⟨x,(F.mem_oppNeighbors r x).mpr ⟨(F.mem_oppSet x).mpr ⟨i,hi⟩,e.symm⟩⟩
    have ht := (Finset.card_le_card (Finset.filter_subset (G.Adj r) F.oppSet)).trans F.card_oppSet
    change (F.oppNeighbors r).card ≤ 3 at ht
    dsimp [K]
    rw [Finset.offDiag_card]
    have cases : (F.oppNeighbors r).card=1 ∨ (F.oppNeighbors r).card=2 ∨
      (F.oppNeighbors r).card=3 := by omega
    rcases cases with z | z | z <;> rw [z] at hs ⊢ <;> norm_num at hs ⊢ <;> omega
  have hsum := Finset.sum_le_sum step
  simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul] at hsum ⊢
  omega

end Frame
end Graffiti133Hex

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem exists_cycle {x : V} (hx : ¬Outside F.c x) : ∃ i, x=F.c i := by
  by_contra! h
  exact hx h

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem find_near {y : V} (hy : Outside F.c y) (hn : ¬ F.Far y) : F.Near y := by
  refine ⟨hy,?_⟩
  by_contra! h
  exact hn ⟨hy,h⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma double_seats : ∀ i j : Fin 6, ¬Cyclic i j → ¬Cyclic (i+1) j →
    j=i+3 ∨ j=i+4 := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma opp_seats : ∀ i : Fin 3, ∀ j : Fin 6,
    ¬Cyclic (frontInd i) j → ¬Cyclic (frontInd i+3) j →
    j=frontInd i ∨ j=frontInd i+3 := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma rooted_edge : ∀ i : Fin 6, Cyclic i (i+1) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem local_double_bound {x : V} {i : Fin 6} (hx : F.Double x i) :
    localIndependence G x ≤ 3 := by
  classical
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let T : Finset (Fin 6) := {i,i+3,i+4}
  have seat (y : V) (hy : y∈A) : ∃ j ∈ T, y=F.c j ∨ G.Adj y (F.c j) := by
    have e := hN _ hy
    by_cases out : Outside F.c y
    · have near : F.Near y := F.find_near out (fun hf => by
        obtain ⟨a,ha⟩ := F.far_edge_opposite ⟨hx.1,⟨i,(hx.2 _).mpr (Or.inl rfl)⟩⟩ hf e
        have neq : ∀ o : Fin 3, ∀ j : Fin 6,
            (j=frontInd o ∨ j=frontInd o+3) →
            ¬(j+1=frontInd o ∨ j+1=frontInd o+3) := by decide
        exact neq a i ((ha.2 _).mp ((hx.2 _).mpr (Or.inl rfl)))
          ((ha.2 _).mp ((hx.2 _).mpr (Or.inr rfl))))
      obtain ⟨j,hj⟩ := near.2
      have hj1 := fun c => F.contact_forbid hx.1 out e ((hx.2 _).mpr (Or.inl rfl)) hj c
      have hj2 := fun c => F.contact_forbid hx.1 out e ((hx.2 _).mpr (Or.inr rfl)) hj c
      rcases double_seats i j hj1 hj2 with rfl | rfl
      · exact ⟨i+3,by simp [T],Or.inr hj⟩
      · exact ⟨i+4,by simp [T],Or.inr hj⟩
    · obtain ⟨j,rfl⟩ := F.exists_cycle out
      refine ⟨i,by simp [T],?_⟩
      rcases (hx.2 j).mp e with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ((F.adj _ _).mpr (rooted_edge i)).symm
  let f (y : V) := if h : y∈A then Classical.choose (seat y h) else i
  have hs {y : V} (h : y∈A) : f y∈T ∧ (y=F.c (f y) ∨ G.Adj y (F.c (f y))) := by
    simpa only [f,dif_pos h] using Classical.choose_spec (seat y h)
  have inj : Set.InjOn f (↑A : Set V) := by
    intro y hy z hz he
    exact F.stamp_uniq (hx.1 (f y)) (hN _ hy) (hN _ hz) (hI _ hy _ hz)
      (hs hy).2 (he.symm ▸ (hs hz).2)
  have hT : T.card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans (by simp)) 1)
  exact eq ▸ (Finset.card_le_card_of_injOn f (fun _ h => (hs h).1) inj).trans hT

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
noncomputable def farNeighbors (x : V) : Finset V := by
  classical exact F.farSet.filter (G.Adj x)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem local_opp_bound {x : V} {i : Fin 3} (hx : F.Opp x i) :
    localIndependence G x ≤ 2 + (F.farNeighbors x).card := by
  classical
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let R := F.farNeighbors x
  let B := A \ R
  let T : Finset (Fin 6) := {frontInd i,frontInd i+3}
  have seat (y : V) (hy : y∈B) : ∃ j ∈ T, y=F.c j ∨ G.Adj y (F.c j) := by
    obtain ⟨hy,hn⟩ := Finset.mem_sdiff.mp hy
    have e := hN _ hy
    by_cases out : Outside F.c y
    · have near := F.find_near out (fun hf => hn (Finset.mem_filter.mpr ⟨(F.mem_farSet y).mpr hf,e⟩))
      obtain ⟨j,hj⟩ := near.2
      have hj1 := fun c => F.contact_forbid hx.1 out e ((hx.2 _).mpr (Or.inl rfl)) hj c
      have hj2 := fun c => F.contact_forbid hx.1 out e ((hx.2 _).mpr (Or.inr rfl)) hj c
      have ha := opp_seats i j hj1 hj2
      exact ⟨j,by simpa [T] using ha,Or.inr hj⟩
    · obtain ⟨j,rfl⟩ := F.exists_cycle out
      exact ⟨j,by simpa [T] using (hx.2 j).mp e,Or.inl rfl⟩
  let f (y : V) := if h : y∈B then Classical.choose (seat y h) else frontInd i
  have hs {y : V} (h : y∈B) : f y∈T ∧ (y=F.c (f y) ∨ G.Adj y (F.c (f y))) := by
    simpa only [f,dif_pos h] using Classical.choose_spec (seat y h)
  have inj : Set.InjOn f (↑B : Set V) := by
    intro y hy z hz he
    have hy' := (Finset.mem_sdiff.mp hy).1
    have hz' := (Finset.mem_sdiff.mp hz).1
    exact F.stamp_uniq (hx.1 _) (hN _ hy') (hN _ hz') (hI _ hy' _ hz')
      (hs hy).2 (he.symm ▸ (hs hz).2)
  have hT : T.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have hB := (Finset.card_le_card_of_injOn f (fun _ h => (hs h).1) inj).trans hT
  have hInt := Finset.card_le_card (show A ∩ R ⊆ R from Finset.inter_subset_right)
  have hC := Finset.card_sdiff_add_card_inter A R
  change B.card + (A ∩ R).card = A.card at hC
  change localIndependence G x ≤ 2 + R.card
  omega

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
noncomputable def singleSite (i : Fin 6) : Finset V := by
  classical exact Finset.univ.filter (fun v => F.Single v i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
noncomputable def oppSite (i : Fin 6) : Finset V := by
  classical exact F.oppSet.filter (fun v => G.Adj v (F.c i))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma oma133_HexFlattened133_cyc6_ne : ∀ i j : Fin 6, Cyclic i j → i ≠ j := by decide
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private lemma oma133_HexFlattened133_cyc6_sites : ∀ i j : Fin 6, Cyclic i j ↔ j=i+1 ∨ j=i+5 := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem local_cycle_bound (i : Fin 6) :
    localIndependence G (F.c i) ≤ 2 + (F.singleSite i).card + (F.oppSite i).card := by
  classical
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) (F.c i)
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let U := F.singleSite i ∪ F.oppSite i
  let B := A \ U
  let T : Finset (Fin 6) := {i+1,i+5}
  have seat (y : V) (hy : y∈B) : ∃ j, Cyclic i j ∧ (y=F.c j ∨ G.Adj y (F.c j)) := by
    obtain ⟨hy,hn⟩ := Finset.mem_sdiff.mp hy
    have e := hN _ hy
    by_cases out : Outside F.c y
    · rcases F.classify (x:=y) ⟨out,i,e.symm⟩ with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨j,hj⟩
      · have h := (hj.2 i).mp e.symm
        exact (hn (Finset.mem_union_left _ (by simpa [singleSite,h] using hj))).elim
      · rcases (hj.2 i).mp e.symm with h | h
        · exact ⟨j+1,by simpa [h] using rooted_edge j,Or.inr ((hj.2 _).mpr (Or.inr rfl))⟩
        · exact ⟨j,(cyclic_symm _ _).mpr (by simpa [h] using rooted_edge j),
            Or.inr ((hj.2 _).mpr (Or.inl rfl))⟩
      · have hw := (F.mem_oppSet y).mpr ⟨j,hj⟩
        exact (hn (Finset.mem_union_right _ (by simp [oppSite,hw,e.symm]))).elim
    · obtain ⟨j,rfl⟩ := F.exists_cycle out
      exact ⟨j,(F.adj _ _).mp e,Or.inl rfl⟩
  let f (y : V) := if h : y∈B then Classical.choose (seat y h) else i
  have hs {y : V} (h : y∈B) : Cyclic i (f y) ∧ (y=F.c (f y) ∨ G.Adj y (F.c (f y))) := by
    simpa only [f,dif_pos h] using Classical.choose_spec (seat y h)
  have inT {y : V} (hy : y∈B) : f y∈T := by
    simpa [T] using (oma133_HexFlattened133_cyc6_sites _ _).mp (hs hy).1
  have inj : Set.InjOn f (↑B : Set V) := by
    intro y hy z hz he
    have hy' := (Finset.mem_sdiff.mp hy).1
    have hz' := (Finset.mem_sdiff.mp hz).1
    exact F.stamp_uniq (F.inj.ne (oma133_HexFlattened133_cyc6_ne _ _ (hs hy).1)) (hN _ hy') (hN _ hz') (hI _ hy' _ hz')
      (hs hy).2 (he.symm ▸ (hs hz).2)
  have hT : T.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have hB := (Finset.card_le_card_of_injOn f (fun _ h => inT h) inj).trans hT
  have hInt := (Finset.card_le_card (show A ∩ U ⊆ U from Finset.inter_subset_right)).trans
    (Finset.card_union_le (F.singleSite i) (F.oppSite i))
  have hC := Finset.card_sdiff_add_card_inter A U
  change B.card + (A ∩ U).card = A.card at hC
  omega

end Frame
end Graffiti133Hex

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
noncomputable def singleSet : Finset V := by
  classical exact Finset.univ.filter (fun x => ∃ i, F.Single x i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
noncomputable def cycleSet : Finset V := by
  classical exact Finset.univ.image F.c

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem single_site_sum : (∑ i, (F.singleSite i).card) = F.singleSet.card := by
  classical
  have ht : ((Finset.univ : Finset (Fin 6)).biUnion F.singleSite) = F.singleSet := by
    ext x
    simp [singleSet,singleSite]
  have hd : (↑(Finset.univ : Finset (Fin 6)) : Set (Fin 6)).PairwiseDisjoint F.singleSite := by
    intro a _ b _ ne
    apply Finset.disjoint_left.mpr
    intro x ha hb
    have sa : F.Single x a := by simpa [singleSite] using ha
    have sb : F.Single x b := by simpa [singleSite] using hb
    exact ne ((sb.2 a).mp ((sa.2 a).mpr rfl))
  rw [← Finset.card_biUnion hd, ht]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem opp_site_sum : (∑ i, (F.oppSite i).card) = 2 * F.oppSet.card := by
  classical
  simp only [oppSite,Finset.card_filter]
  rw [Finset.sum_comm]
  have step (x : V) (hx : x∈F.oppSet) : (∑ j : Fin 6, if G.Adj x (F.c j) then 1 else 0) = 2 := by
    obtain ⟨i,hi⟩ := (F.mem_oppSet x).mp hx
    simp_rw [hi.2]
    have aux : ∀ i : Fin 3, (∑ j : Fin 6, if j=frontInd i ∨ j=frontInd i+3 then (1:ℕ) else 0) = 2 := by decide
    exact aux i
  calc
    (∑ x ∈ F.oppSet, ∑ i : Fin 6, if G.Adj x (F.c i) then 1 else 0)
        = ∑ _x ∈ F.oppSet, 2 := Finset.sum_congr rfl step
    _ = 2 * F.oppSet.card := by simp [Nat.mul_comm]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem inc_symm :
    (∑ x ∈ F.oppSet, (F.farNeighbors x).card) =
      ∑ r ∈ F.farSet, (F.oppNeighbors r).card := by
  classical
  simp only [farNeighbors,oppNeighbors,Finset.card_filter]
  rw [Finset.sum_comm]
  simp only [G.adj_comm]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem low_hex_budget (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r)
    (low : ∀ x i, F.Single x i → localIndependence G x ≤ 2) :
    (∑ x, localIndependence G x) ≤ 3 * Fintype.card V := by
  classical
  let A := F.cycleSet
  let S := F.singleSet
  let O := F.oppSet
  let R := F.farSet
  let D := Finset.univ \ (A ∪ S ∪ O ∪ R)
  have cyc (x : V) : x ∈ A ↔ ∃ i, x = F.c i := by
    constructor
    · intro h
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
      exact ⟨i,hi.symm⟩
    · rintro ⟨i,rfl⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have sm (x : V) : x∈S ↔ ∃ i, F.Single x i := by simp [S,singleSet]
  have so : Disjoint S O := by
    apply Finset.disjoint_left.mpr
    intro x hs ho
    obtain ⟨i,hi⟩ := (sm x).mp hs
    obtain ⟨j,hj⟩ := (F.mem_oppSet x).mp ho
    have h1 := (hi.2 _).mp ((hj.2 _).mpr (Or.inl rfl))
    have h2 := (hi.2 _).mp ((hj.2 _).mpr (Or.inr rfl))
    exact (by decide : ∀ j : Fin 3, frontInd j ≠ frontInd j+3) j (h1.trans h2.symm)
  have aS : Disjoint A S := by
    apply Finset.disjoint_left.mpr
    intro x ha hs
    obtain ⟨i,hi⟩ := (cyc x).mp ha
    obtain ⟨j,hj⟩ := (sm x).mp hs
    exact hj.1 i hi
  have aO : Disjoint A O := by
    apply Finset.disjoint_left.mpr
    intro x ha hs
    obtain ⟨i,hi⟩ := (cyc x).mp ha
    obtain ⟨j,hj⟩ := (F.mem_oppSet x).mp hs
    exact hj.1 i hi
  have aR : Disjoint A R := by
    apply Finset.disjoint_left.mpr
    intro x ha hr
    obtain ⟨i,hi⟩ := (cyc x).mp ha
    exact ((F.mem_farSet x).mp hr).1 i hi
  have sR : Disjoint S R := by
    apply Finset.disjoint_left.mpr
    intro x hs hr
    obtain ⟨i,hi⟩ := (sm x).mp hs
    exact ((F.mem_farSet x).mp hr).2 i ((hi.2 i).mpr rfl)
  have oR : Disjoint O R := by
    apply Finset.disjoint_left.mpr
    intro x ho hr
    obtain ⟨i,hi⟩ := (F.mem_oppSet x).mp ho
    exact ((F.mem_farSet x).mp hr).2 (frontInd i) ((hi.2 _).mpr (Or.inl rfl))
  have d1 : Disjoint (A ∪ S) O := Finset.disjoint_union_left.mpr ⟨aO,so⟩
  have d2 : Disjoint (A ∪ S ∪ O) R := Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨aR,sR⟩,oR⟩
  have d3 : Disjoint (A ∪ S ∪ O ∪ R) D := by
    apply Finset.disjoint_left.mpr
    exact fun x hx hd => (Finset.mem_sdiff.mp hd).2 hx
  have u : A ∪ S ∪ O ∪ R ∪ D = Finset.univ := by
    ext x
    by_cases h : x ∈ A ∪ S ∪ O ∪ R <;> simp [D,h]
  have ca : A.card=6 := by simp [A,cycleSet,Finset.card_image_of_injective _ F.inj]
  have co := F.card_oppSet
  change O.card ≤ 3 at co
  have ns : Fintype.card V = 6+S.card+O.card+R.card+D.card := by
    rw [← Finset.card_univ,←u,Finset.card_union_of_disjoint d3,Finset.card_union_of_disjoint d2,
      Finset.card_union_of_disjoint d1,Finset.card_union_of_disjoint aS,ca]
  let f := localIndependence G
  have splits : (∑ x, f x) =
      (∑ x ∈ A,f x)+(∑ x ∈ S,f x)+(∑ x ∈ O,f x)+(∑ x ∈ R,f x)+(∑ x ∈ D,f x) := by
    rw [←u,Finset.sum_union d3,Finset.sum_union d2,Finset.sum_union d1,Finset.sum_union aS]
  have bA : (∑ x∈A,f x) ≤ 12+S.card+2*O.card := by
    change (∑ x∈Finset.univ.image F.c,f x) ≤ _
    rw [Finset.sum_image (fun _ _ _ _ e => F.inj e)]
    apply (Finset.sum_le_sum (fun i _ => F.local_cycle_bound i)).trans
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      Nat.nsmul_eq_mul,single_site_sum,opp_site_sum,S,O]
    omega
  have bS : (∑ x∈S,f x) ≤ 2*S.card := by
    calc
      (∑ x ∈ S, f x) ≤ ∑ _x ∈ S, (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨i,hi⟩ := (sm x).mp hx
        exact low x i hi
      _ = 2*S.card := by simp [Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm]
  let inc := ∑ r∈R,(F.oppNeighbors r).card
  have bO : (∑ x∈O,f x) ≤ 2*O.card+inc := by
    have h := Finset.sum_le_sum (s:=O) (fun x hx => by
      obtain ⟨i,hi⟩ := (F.mem_oppSet x).mp hx
      exact F.local_opp_bound hi)
    simpa [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm,
      inc,O,R,F.inc_symm] using h
  have bR : (∑ x∈R,f x)+inc ≤ 3*R.card+3 := by
    simpa only [Finset.sum_add_distrib] using F.far_global_budget hc hm
  have bD : (∑ x∈D,f x) ≤ 3*D.card := by
    have step (x : V) (hx : x∈D) : f x ≤ 3 := by
      have hn := (Finset.mem_sdiff.mp hx).2
      have out : Outside F.c x := fun i h => hn (by simp [(cyc x).mpr ⟨i,h⟩])
      have hf : ¬F.Far x := fun h => hn (Finset.mem_union_right _ ((F.mem_farSet x).mpr h))
      have hnear : F.Near x := by
        refine ⟨out,?_⟩
        apply Classical.byContradiction
        intro h
        exact hf ⟨out,fun i e => h ⟨i,e⟩⟩
      rcases F.classify hnear with ⟨i,hi⟩ | ⟨i,hi⟩ | ⟨i,hi⟩
      · exact (hn (by simp [(sm x).mpr ⟨i,hi⟩])).elim
      · exact F.local_double_bound hi
      · exact (hn (by simp [show x∈O from (F.mem_oppSet x).mpr ⟨i,hi⟩])).elim
    calc
      (∑ x ∈ D, f x) ≤ ∑ _x ∈ D, (3 : ℕ) := Finset.sum_le_sum step
      _ = 3*D.card := by simp [Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm]
  rw [splits,ns]
  omega

end Frame
end Graffiti133Hex

namespace Graffiti133Hex
open Frame
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
private def anchorTable (a b : Fin 15) : Option (SmallCert 9) :=
  match a.val, b.val with
  | 1, 1 => some (.four 0 7 1 6)
  | 1, 2 => some (.four 0 7 1 6)
  | 1, 3 => some (.four 0 7 1 6)
  | 1, 4 => some (.four 0 7 1 6)
  | 1, 5 => some (.four 0 7 1 6)
  | 1, 7 => some (.four 0 7 1 6)
  | 1, 8 => some (.four 0 7 1 6)
  | 1, 9 => some (.four 0 7 1 6)
  | 1, 10 => some (.four 0 7 1 6)
  | 1, 13 => some (.four 0 7 1 6)
  | 1, 14 => some (.four 0 7 1 6)
  | 2, 1 => some (.four 0 8 1 6)
  | 2, 2 => some (.four 2 6 7 8)
  | 2, 4 => some (.path ![1,2,7,6,8,4,5])
  | 2, 5 => some (.four 0 8 5 6)
  | 2, 7 => some (.four 0 8 1 6)
  | 2, 8 => some (.four 2 6 7 8)
  | 2, 9 => some (.path ![1,2,7,6,8,4,5])
  | 2, 10 => some (.four 0 8 5 6)
  | 2, 13 => some (.four 0 8 1 6)
  | 2, 14 => some (.four 0 8 5 6)
  | 3, 1 => some (.four 0 8 1 6)
  | 3, 3 => some (.four 3 6 7 8)
  | 3, 5 => some (.four 0 8 5 6)
  | 3, 7 => some (.four 0 8 1 6)
  | 3, 8 => some (.four 3 6 7 8)
  | 3, 9 => some (.four 3 6 7 8)
  | 3, 10 => some (.four 0 8 5 6)
  | 3, 13 => some (.four 0 8 1 6)
  | 3, 14 => some (.four 0 8 5 6)
  | 4, 1 => some (.four 0 8 1 6)
  | 4, 2 => some (.path ![1,2,8,6,7,4,5])
  | 4, 4 => some (.four 4 6 7 8)
  | 4, 5 => some (.four 0 8 5 6)
  | 4, 7 => some (.four 0 8 1 6)
  | 4, 8 => some (.path ![1,2,8,6,7,4,5])
  | 4, 9 => some (.four 4 6 7 8)
  | 4, 10 => some (.four 0 8 5 6)
  | 4, 13 => some (.four 0 8 1 6)
  | 4, 14 => some (.four 0 8 5 6)
  | 5, 1 => some (.four 0 7 5 6)
  | 5, 2 => some (.four 0 7 5 6)
  | 5, 3 => some (.four 0 7 5 6)
  | 5, 4 => some (.four 0 7 5 6)
  | 5, 5 => some (.four 0 7 5 6)
  | 5, 7 => some (.four 0 7 5 6)
  | 5, 8 => some (.four 0 7 5 6)
  | 5, 9 => some (.four 0 7 5 6)
  | 5, 10 => some (.four 0 7 5 6)
  | 5, 13 => some (.four 0 7 5 6)
  | 5, 14 => some (.four 0 7 5 6)
  | 7, 1 => some (.four 0 7 1 6)
  | 7, 2 => some (.four 0 7 1 6)
  | 7, 3 => some (.four 0 7 1 6)
  | 7, 4 => some (.four 0 7 1 6)
  | 7, 5 => some (.four 0 7 1 6)
  | 7, 7 => some (.four 0 7 1 6)
  | 7, 8 => some (.four 0 7 1 6)
  | 7, 9 => some (.four 0 7 1 6)
  | 7, 10 => some (.four 0 7 1 6)
  | 7, 13 => some (.four 0 7 1 6)
  | 7, 14 => some (.four 0 7 1 6)
  | 8, 1 => some (.four 0 8 1 6)
  | 8, 2 => some (.four 2 6 7 8)
  | 8, 3 => some (.four 3 6 7 8)
  | 8, 4 => some (.path ![1,2,7,6,8,4,5])
  | 8, 5 => some (.four 0 8 5 6)
  | 8, 7 => some (.four 0 8 1 6)
  | 8, 8 => some (.four 2 3 7 8)
  | 8, 9 => some (.four 3 6 7 8)
  | 8, 10 => some (.four 0 8 5 6)
  | 8, 13 => some (.four 0 8 1 6)
  | 8, 14 => some (.four 0 8 5 6)
  | 9, 1 => some (.four 0 8 1 6)
  | 9, 2 => some (.path ![1,2,8,6,7,4,5])
  | 9, 3 => some (.four 3 6 7 8)
  | 9, 4 => some (.four 4 6 7 8)
  | 9, 5 => some (.four 0 8 5 6)
  | 9, 7 => some (.four 0 8 1 6)
  | 9, 8 => some (.four 3 6 7 8)
  | 9, 9 => some (.four 3 4 7 8)
  | 9, 10 => some (.four 0 8 5 6)
  | 9, 13 => some (.four 0 8 1 6)
  | 9, 14 => some (.four 0 8 5 6)
  | 10, 1 => some (.four 0 7 5 6)
  | 10, 2 => some (.four 0 7 5 6)
  | 10, 3 => some (.four 0 7 5 6)
  | 10, 4 => some (.four 0 7 5 6)
  | 10, 5 => some (.four 0 7 5 6)
  | 10, 7 => some (.four 0 7 5 6)
  | 10, 8 => some (.four 0 7 5 6)
  | 10, 9 => some (.four 0 7 5 6)
  | 10, 10 => some (.four 0 7 5 6)
  | 10, 13 => some (.four 0 7 5 6)
  | 10, 14 => some (.four 0 7 5 6)
  | 13, 1 => some (.four 0 7 1 6)
  | 13, 2 => some (.four 0 7 1 6)
  | 13, 3 => some (.four 0 7 1 6)
  | 13, 4 => some (.four 0 7 1 6)
  | 13, 5 => some (.four 0 7 1 6)
  | 13, 7 => some (.four 0 7 1 6)
  | 13, 8 => some (.four 0 7 1 6)
  | 13, 9 => some (.four 0 7 1 6)
  | 13, 10 => some (.four 0 7 1 6)
  | 13, 13 => some (.four 0 7 1 6)
  | 13, 14 => some (.four 0 7 1 6)
  | 14, 1 => some (.four 0 7 5 6)
  | 14, 2 => some (.four 0 7 5 6)
  | 14, 3 => some (.four 0 7 5 6)
  | 14, 4 => some (.four 0 7 5 6)
  | 14, 5 => some (.four 0 7 5 6)
  | 14, 7 => some (.four 0 7 5 6)
  | 14, 8 => some (.four 0 7 5 6)
  | 14, 9 => some (.four 0 7 5 6)
  | 14, 10 => some (.four 0 7 5 6)
  | 14, 13 => some (.four 0 7 5 6)
  | 14, 14 => some (.four 0 7 5 6)
  | _, _ => none
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
private def extraTable (a : Fin 15) (b : Fin 8) : Option (SmallCert 10) :=
  match a.val, b.val with
  | 0, 0 => some (.path ![4,3,2,7,6,0,9])
  | 0, 1 => some (.path ![5,4,3,2,7,6,9])
  | 0, 2 => some (.four 0 7 6 9)
  | 0, 3 => some (.four 0 7 6 9)
  | 0, 4 => some (.four 0 8 6 9)
  | 0, 5 => some (.four 0 8 6 9)
  | 0, 6 => some (.four 0 7 6 9)
  | 0, 7 => some (.four 0 7 6 9)
  | 1, 0 => some (.path ![4,3,8,6,0,1,9])
  | 1, 1 => some (.four 0 9 1 6)
  | 1, 2 => some (.four 1 7 2 9)
  | 1, 3 => some (.four 0 9 1 6)
  | 1, 5 => some (.four 0 9 1 6)
  | 1, 6 => some (.four 1 7 2 9)
  | 1, 7 => some (.four 0 9 1 6)
  | 2, 0 => some (.path ![4,5,0,6,7,2,9])
  | 2, 1 => some (.four 2 6 7 9)
  | 2, 2 => some (.path ![3,4,5,0,6,7,9])
  | 2, 3 => some (.four 2 6 7 9)
  | 2, 4 => some (.four 2 8 3 9)
  | 2, 5 => some (.four 2 6 7 9)
  | 2, 6 => some (.four 2 8 3 9)
  | 2, 7 => some (.four 2 6 7 9)
  | 3, 0 => some (.path ![5,0,6,7,2,3,9])
  | 3, 1 => some (.four 3 6 8 9)
  | 3, 2 => some (.four 2 9 3 7)
  | 3, 3 => some (.four 2 9 3 7)
  | 3, 4 => some (.path ![5,0,6,7,2,3,9])
  | 3, 5 => some (.four 3 6 8 9)
  | 3, 6 => some (.four 2 9 3 7)
  | 3, 7 => some (.four 2 9 3 7)
  | 4, 0 => some (.path ![0,6,7,2,3,4,9])
  | 4, 1 => some (.path ![1,2,7,6,9,4,5])
  | 4, 2 => some (.path ![1,0,6,7,9,4,3])
  | 4, 4 => some (.four 3 9 4 8)
  | 4, 5 => some (.four 3 9 4 8)
  | 4, 6 => some (.four 3 9 4 8)
  | 4, 7 => some (.four 3 9 4 8)
  | 5, 0 => some (.path ![2,3,8,6,0,5,9])
  | 5, 1 => some (.four 0 9 5 6)
  | 5, 2 => some (.path ![0,5,9,7,2,3,8])
  | 5, 3 => some (.four 0 9 5 6)
  | 5, 4 => some (.path ![0,5,9,8,3,2,7])
  | 5, 5 => some (.four 0 9 5 6)
  | 5, 6 => some (.four 6 9 7 8)
  | 5, 7 => some (.four 0 9 5 6)
  | 6, 0 => some (.path ![4,3,2,7,6,0,9])
  | 6, 1 => some (.four 0 9 1 6)
  | 6, 2 => some (.four 0 7 6 9)
  | 6, 3 => some (.four 0 7 6 9)
  | 6, 4 => some (.four 0 8 6 9)
  | 6, 5 => some (.four 0 8 6 9)
  | 6, 6 => some (.four 0 7 6 9)
  | 6, 7 => some (.four 0 7 6 9)
  | 7, 0 => some (.path ![4,3,8,6,0,1,9])
  | 7, 1 => some (.four 0 9 1 6)
  | 7, 2 => some (.four 1 7 2 9)
  | 7, 3 => some (.four 0 9 1 6)
  | 7, 4 => some (.four 2 8 3 9)
  | 7, 5 => some (.four 0 9 1 6)
  | 7, 6 => some (.four 1 7 2 9)
  | 7, 7 => some (.four 0 9 1 6)
  | 8, 0 => some (.path ![4,5,0,6,7,2,9])
  | 8, 1 => some (.four 2 6 7 9)
  | 8, 2 => some (.four 2 9 3 7)
  | 8, 3 => some (.four 2 6 7 9)
  | 8, 4 => some (.four 2 8 3 9)
  | 8, 5 => some (.four 2 6 7 9)
  | 8, 6 => some (.four 2 8 3 9)
  | 8, 7 => some (.four 2 6 7 9)
  | 9, 0 => some (.path ![2,7,6,0,5,4,9])
  | 9, 1 => some (.four 3 6 8 9)
  | 9, 2 => some (.four 2 9 3 7)
  | 9, 3 => some (.four 2 9 3 7)
  | 9, 4 => some (.four 3 9 4 8)
  | 9, 5 => some (.four 3 6 8 9)
  | 9, 6 => some (.four 2 9 3 7)
  | 9, 7 => some (.four 2 9 3 7)
  | 10, 0 => some (.path ![0,6,7,2,3,4,9])
  | 10, 1 => some (.four 0 9 5 6)
  | 10, 2 => some (.path ![0,5,9,7,2,3,8])
  | 10, 3 => some (.four 0 9 5 6)
  | 10, 4 => some (.four 3 9 4 8)
  | 10, 5 => some (.four 0 9 5 6)
  | 10, 6 => some (.four 3 9 4 8)
  | 10, 7 => some (.four 0 9 5 6)
  | 11, 0 => some (.path ![4,3,2,7,6,0,9])
  | 11, 1 => some (.four 0 9 5 6)
  | 11, 2 => some (.four 0 7 6 9)
  | 11, 3 => some (.four 0 7 6 9)
  | 11, 4 => some (.four 0 8 6 9)
  | 11, 5 => some (.four 0 8 6 9)
  | 11, 6 => some (.four 0 7 6 9)
  | 11, 7 => some (.four 0 7 6 9)
  | 12, 1 => some (.four 3 6 8 9)
  | 12, 2 => some (.four 0 7 6 9)
  | 12, 3 => some (.four 0 7 6 9)
  | 12, 4 => some (.four 0 8 6 9)
  | 12, 5 => some (.four 0 8 6 9)
  | 12, 6 => some (.four 0 7 6 9)
  | 12, 7 => some (.four 0 7 6 9)
  | 13, 0 => some (.path ![0,6,7,2,3,4,9])
  | 13, 1 => some (.four 0 9 1 6)
  | 13, 2 => some (.four 1 7 2 9)
  | 13, 3 => some (.four 0 9 1 6)
  | 13, 4 => some (.four 3 9 4 8)
  | 13, 5 => some (.four 0 9 1 6)
  | 13, 6 => some (.four 1 7 2 9)
  | 13, 7 => some (.four 0 9 1 6)
  | 14, 0 => some (.path ![4,5,9,2,7,6,8])
  | 14, 1 => some (.four 0 9 5 6)
  | 14, 3 => some (.four 0 9 5 6)
  | 14, 4 => some (.four 2 8 3 9)
  | 14, 5 => some (.four 0 9 5 6)
  | 14, 6 => some (.four 2 8 3 9)
  | 14, 7 => some (.four 0 9 5 6)
  | _, _ => none
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
def CertCheck {n : ℕ} (R : Fin n → Fin n → Prop) : Option (SmallCert n) → Prop
| none => False
| some c => CertTrue R c

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
noncomputable instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (c : Option (SmallCert n)) :
    Decidable (CertCheck R c) := by
  cases c <;> unfold CertCheck <;> infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem certCheck_elim {n : ℕ} {R : Fin n → Fin n → Prop} {C : Option (SmallCert n)}
    (h : CertCheck R C) : ∃ c, CertTrue R c := by
  cases C with
  | none => exact h.elim
  | some c => exact ⟨c,h⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
noncomputable def anchorB (a b : Fin 15) : Fin 3 → Fin 6 → Bool :=
  fun i => contactsB (![0,a,b] i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
def anchorE (i j : Fin 3) : Bool := decide
  ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem anchor_cert (a b : Fin 15) :
    contactsB a 0 = false → contactsB b 0 = false →
    ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3)) ∨
      CertCheck (SmallRel (anchorB a b) anchorE) (anchorTable a b) := by
  revert a b
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
noncomputable def extraB (a : Fin 15) : Fin 4 → Fin 6 → Bool :=
  fun i => contactsB (![0,2,3,a] i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
def extraE (mask : Fin 8) (i j : Fin 4) : Bool :=
  if i.val < 3 then
    if j.val < 3 then decide ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0))
    else mask.val.testBit i.val
  else if j.val < 3 then mask.val.testBit j.val else false

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem extra_cert (a : Fin 15) (b : Fin 8) :
    ((a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 3) ∨ (a = 12 ∧ b = 0) ∨ (a = 14 ∧ b = 2)) ∨
      CertCheck (SmallRel (extraB a) (extraE b)) (extraTable a b) := by
  revert a b
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
def optionProfiles (i : Fin 4) : Fin 15 := ![1,4,12,14] i
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
def optionMasks (i : Fin 4) : Fin 8 := ![4,3,0,2] i

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
noncomputable def doubleExtraB (a b : Fin 4) : Fin 5 → Fin 6 → Bool :=
  fun i => contactsB (![0,2,3,optionProfiles a,optionProfiles b] i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
def doubleExtraE (a b : Fin 4) (edge : Bool) (i j : Fin 5) : Bool :=
  if i.val < 3 then
    if j.val < 3 then decide ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0))
    else (optionMasks (if j.val = 3 then a else b)).val.testBit i.val
  else if j.val < 3 then (optionMasks (if i.val = 3 then a else b)).val.testBit j.val
  else if i=j then false else edge

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
private def doubleTable (a b : Fin 4) (e : Bool) : Option (SmallCert 11) :=
  match a.val, b.val, e with
  | 0, 1, false => some (.path ![0,1,9,8,3,4,10])
  | 0, 1, true => some (.four 6 9 8 10)
  | 0, 2, true => some (.four 0 9 1 10)
  | 0, 3, false => some (.path ![0,5,10,2,3,8,9])
  | 0, 3, true => some (.four 1 10 2 9)
  | 1, 2, false => some (.path ![1,0,10,3,4,9,7])
  | 1, 2, true => some (.four 0 9 6 10)
  | 1, 3, false => some (.path ![0,6,9,4,3,2,10])
  | 1, 3, true => some (.four 2 9 7 10)
  | 2, 3, false => some (.path ![4,3,9,0,6,7,10])
  | 2, 3, true => some (.four 0 10 5 9)
  | _, _, _ => none

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 24000 in
theorem double_extra_cert (a b : Fin 4) (e : Bool) : a < b →
    (a = 0 ∧ b = 2 ∧ e = false) ∨
    CertCheck (SmallRel (doubleExtraB a b) (doubleExtraE a b e)) (doubleTable a b e) := by
  revert a b e
  decide
end Graffiti133Hex

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private def relabelIndex (a : Fin 6) (rev : Bool) (j : Fin 6) :=
  if rev then a-j else a+j

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private lemma relabelIndex_inj (a : Fin 6) (rev : Bool) : Function.Injective (relabelIndex a rev) := by
  intro i j
  have h : ∀ a rev (i j : Fin 6), relabelIndex a rev i = relabelIndex a rev j → i=j := by decide
  exact h a rev i j

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private lemma relabelIndex_adj : ∀ a rev (i j : Fin 6),
    Cyclic (relabelIndex a rev i) (relabelIndex a rev j) ↔ Cyclic i j := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
def relabel (a : Fin 6) (rev : Bool) : Frame G where
  c := F.c ∘ relabelIndex a rev
  inj := F.inj.comp (relabelIndex_inj a rev)
  adj i j := (F.adj _ _).trans (relabelIndex_adj a rev i j)
  h4 := F.h4
  no7 := F.no7

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private lemma stay_out {x : V} (hx : Outside F.c x) (a : Fin 6) (rev : Bool) :
    Outside (F.relabel a rev).c x := fun _ => hx _

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private lemma change_single {x : V} {i : Fin 6} (hx : F.Single x (relabelIndex a rev i)) :
    (F.relabel a rev).Single x i := by
  refine ⟨F.stay_out hx.1 a rev,fun j => ?_⟩
  change G.Adj x (F.c (relabelIndex a rev j)) ↔ _
  rw [hx.2]
  exact ⟨fun e => relabelIndex_inj a rev e,congrArg _⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private lemma profile_one (a : Fin 6) :
    ∀ j : Fin 6, contactsB ⟨a.val,by omega⟩ j=true ↔ j=a := by
  intro j
  simp [contactsB,contact,a.isLt]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private lemma anchor_patterns {x y z : V} (hx : F.Single x 0)
    (hy : F.Near y) (hz : F.Near z)
    (exy : G.Adj x y) (exz : G.Adj x z) (eyz : ¬G.Adj y z) (nyz : y ≠ z)
    (cy : ¬G.Adj y (F.c 0)) (cz : ¬G.Adj z (F.c 0)) :
    (F.Single y 2 ∧ F.Single z 3) ∨ (F.Single y 3 ∧ F.Single z 2) ∨
    (F.Single y 3 ∧ F.Single z 4) ∨ (F.Single y 4 ∧ F.Single z 3) := by
  classical
  obtain ⟨a,ha⟩ := F.profile_exists hy
  obtain ⟨b,hb⟩ := F.profile_exists hz
  have ac : contactsB a 0=false := Bool.eq_false_iff.mpr (fun e => cy ((ha _).mp e))
  have bc : contactsB b 0=false := Bool.eq_false_iff.mpr (fun e => cz ((hb _).mp e))
  rcases anchor_cert a b ac bc with ok | bad
  · have H (a : Fin 15) (u : V) (hu : Outside F.c u)
        (h : ∀ j, contactsB a j=true ↔ G.Adj u (F.c j)) (i : Fin 6) (eq : a.val=i.val) :
        F.Single u i := by
      refine ⟨hu,fun j => (h j).symm.trans ?_⟩
      have tt : a = ⟨i.val,by omega⟩ := Fin.ext eq
      exact tt.symm ▸ profile_one i j
    rcases ok with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨H 2 y hy.1 ha 2 rfl,H 3 z hz.1 hb 3 rfl⟩
    · exact Or.inr (Or.inl ⟨H 3 y hy.1 ha 3 rfl,H 2 z hz.1 hb 2 rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨H 3 y hy.1 ha 3 rfl,H 4 z hz.1 hb 4 rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨H 4 y hy.1 ha 4 rfl,H 3 z hz.1 hb 3 rfl⟩))
  · obtain ⟨cert,hcert⟩ := certCheck_elim bad
    let e : Fin 3 → V := ![x,y,z]
    have ei : Function.Injective e := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp [e,exy.ne,Ne.symm exy.ne,exz.ne,Ne.symm exz.ne,nyz,Ne.symm nyz] at h ⊢
    have off (i : Fin 3) : Outside F.c (e i) := by
      fin_cases i
      · exact hx.1
      · exact hy.1
      · exact hz.1
    have hB (i : Fin 3) (j : Fin 6) : anchorB a b i j=true ↔ G.Adj (e i) (F.c j) := by
      fin_cases i
      · simpa [anchorB,e] using (profile_one 0 j).trans ((hx.2 j).symm)
      · simpa [anchorB,e] using ha j
      · simpa [anchorB,e] using hb j
    have hE (i j : Fin 3) : anchorE i j=true ↔ G.Adj (e i) (e j) := by
      fin_cases i <;> fin_cases j <;>
        simp [anchorE,e,G.loopless.irrefl,exy,exy.symm,exz,exz.symm,eyz,show ¬G.Adj z y from fun h => eyz h.symm]
    exact (F.reject_small e ei off hB hE cert hcert).elim

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private theorem high_neighbors {x : V} (high : 3 ≤ localIndependence G x)
    {i : Fin 6} (hx : F.Single x i) :
    ∃ y z, y ≠ z ∧ G.Adj x y ∧ G.Adj x z ∧ ¬G.Adj y z ∧
      F.Near y ∧ F.Near z ∧ ¬G.Adj y (F.c i) ∧ ¬G.Adj z (F.c i) := by
  classical
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let B := A.filter (fun w => w=F.c i ∨ G.Adj w (F.c i))
  have cb : B.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,ha'⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,hb'⟩ := Finset.mem_filter.mp hb
    exact F.stamp_uniq (hx.1 i) (hN _ ha) (hN _ hb) (hI _ ha _ hb) ha' hb'
  let C := A \ B
  have Bsub : B ⊆ A := Finset.filter_subset _ _
  have sum := Finset.card_sdiff_add_card_eq_card Bsub
  have c2 : 1 < C.card := by
    change C.card+B.card=A.card at sum
    omega
  obtain ⟨y,hy,z,hz,yz⟩ := Finset.one_lt_card.mp c2
  have eY := hN y (Finset.mem_sdiff.mp hy).1
  have eZ := hN z (Finset.mem_sdiff.mp hz).1
  have nch (u : V) (hu : u∈C) : u ≠ F.c i ∧ ¬G.Adj u (F.c i) := by
    obtain ⟨hu,hb⟩ := Finset.mem_sdiff.mp hu
    exact ⟨fun h => hb (Finset.mem_filter.mpr ⟨hu,Or.inl h⟩),
      fun h => hb (Finset.mem_filter.mpr ⟨hu,Or.inr h⟩)⟩
  have near (u : V) (hu : u∈C) : F.Near u := by
    have e := hN u (Finset.mem_sdiff.mp hu).1
    have out : Outside F.c u := by
      intro j he
      have h := (hx.2 j).mp (he ▸ e)
      exact (nch u hu).1 (he.trans (congrArg F.c h))
    refine ⟨out,?_⟩
    apply Classical.byContradiction
    intro bad
    have fu : F.Far u := ⟨out,fun j h => bad ⟨j,h⟩⟩
    obtain ⟨j,hj⟩ := F.far_edge_opposite ⟨hx.1,⟨i,(hx.2 _).mpr rfl⟩⟩ fu e
    have e1 := (hx.2 _).mp ((hj.2 (frontInd j)).mpr (Or.inl rfl))
    have e2 := (hx.2 _).mp ((hj.2 (frontInd j+3)).mpr (Or.inr rfl))
    exact (by decide : ∀ j : Fin 3, frontInd j ≠ frontInd j+3) j (e1.trans e2.symm)
  exact ⟨y,z,yz,eY,eZ,hI _ (Finset.mem_sdiff.mp hy).1 _ (Finset.mem_sdiff.mp hz).1,
    near y hy,near z hz,(nch y hy).2,(nch z hz).2⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
structure Anchor (F : Frame G) where
  x : V
  y : V
  z : V
  sx : F.Single x 0
  sy : F.Single y 2
  sz : F.Single z 3
  xy : G.Adj x y
  xz : G.Adj x z
  yz : ¬G.Adj y z
  nd : y ≠ z

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
theorem high_has_anchor {x : V} {i : Fin 6} (hx : F.Single x i)
    (hhigh : 3 ≤ localIndependence G x) : ∃ H : Frame G, Nonempty (Anchor H) := by
  let H := F.relabel i false
  have h0 : relabelIndex i false 0=i := by simp [relabelIndex]
  have hx' : H.Single x 0 := F.change_single (h0.symm ▸ hx)
  obtain ⟨y,z,nes,ex,ez,eyz,hy,hz,cy,cz⟩ := H.high_neighbors hhigh hx'
  rcases H.anchor_patterns hx' hy hz ex ez eyz nes cy cz with t | t | t | t
  · exact ⟨H,⟨⟨x,y,z,hx',t.1,t.2,ex,ez,eyz,nes⟩⟩⟩
  · exact ⟨H,⟨⟨x,z,y,hx',t.2,t.1,ez,ex,fun e => eyz e.symm,nes.symm⟩⟩⟩
  · exact ⟨H.relabel 0 true,⟨⟨x,z,y,H.change_single hx',H.change_single t.2,
      H.change_single t.1,ez,ex,fun e => eyz e.symm,nes.symm⟩⟩⟩
  · exact ⟨H.relabel 0 true,⟨⟨x,y,z,H.change_single hx',H.change_single t.1,
      H.change_single t.2,ex,ez,eyz,nes⟩⟩⟩

end Frame
end Graffiti133Hex

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {F : Frame G}

namespace Anchor
variable (A : Anchor F)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
def station (i : Fin 3) : V := ![A.x,A.y,A.z] i

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
lemma station_inj : Function.Injective A.station := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [station,A.xy.ne,Ne.symm A.xy.ne,A.xz.ne,Ne.symm A.xz.ne,A.nd,Ne.symm A.nd] at h ⊢

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
lemma station_out (i : Fin 3) : Outside F.c (A.station i) := by
  fin_cases i
  · exact A.sx.1
  · exact A.sy.1
  · exact A.sz.1

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
lemma station_profile (i : Fin 3) (j : Fin 6) :
    anchorB 2 3 i j=true ↔ G.Adj (A.station i) (F.c j) := by
  fin_cases i
  · exact (by
      simp [station,anchorB,contactsB,contact,A.sx.2,show (0:Fin 15).val<6 by decide])
  · exact (by
      simp [station,anchorB,contactsB,contact,A.sy.2,show (2:Fin 15).val<6 by decide])
  · exact (by
      simp [station,anchorB,contactsB,contact,A.sz.2,show (3:Fin 15).val<6 by decide])

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
lemma station_edges (i j : Fin 3) :
    anchorE i j=true ↔ G.Adj (A.station i) (A.station j) := by
  fin_cases i <;> fin_cases j <;>
    simp [station,anchorE,G.loopless.irrefl,A.xy,A.xy.symm,A.xz,A.xz.symm,A.yz,
      show ¬G.Adj A.z A.y from fun h => A.yz h.symm]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
def Extra (v : V) (i : Fin 4) : Prop :=
  (∀ j, contactsB (optionProfiles i) j=true ↔ G.Adj v (F.c j)) ∧
  (∀ j : Fin 3, (optionMasks i).val.testBit j.val=true ↔ G.Adj v (A.station j))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private def mask3 (c : Fin 3 → Bool) : Fin 8 :=
  ⟨(if c 0 then 1 else 0)+(if c 1 then 2 else 0)+(if c 2 then 4 else 0),by split <;> split <;> split <;> decide⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private lemma mask3_spec : ∀ (c : Fin 3 → Bool) (i : Fin 3),
    (mask3 c).val.testBit i.val = c i := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
theorem extra_classify {v : V} (hv : F.Near v) (nv : ∀ i, v ≠ A.station i) :
    ∃ i, A.Extra v i := by
  classical
  obtain ⟨t,ht⟩ := F.profile_exists hv
  let c : Fin 3 → Bool := fun i => decide (G.Adj v (A.station i))
  let b := mask3 c
  have bm (i : Fin 3) : b.val.testBit i.val=true ↔ G.Adj v (A.station i) := by
    rw [mask3_spec c i]
    simp [c]
  rcases extra_cert t b with ok | bad
  · have form (i : Fin 4) (hp : optionProfiles i=t) (hm : optionMasks i=b) : A.Extra v i :=
      ⟨fun j => hp.symm ▸ ht j,fun j => hm.symm ▸ bm j⟩
    rcases ok with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨0,form 0 h1.symm h2.symm⟩
    · exact ⟨1,form 1 h1.symm h2.symm⟩
    · exact ⟨2,form 2 h1.symm h2.symm⟩
    · exact ⟨3,form 3 h1.symm h2.symm⟩
  · obtain ⟨cert,hcert⟩ := certCheck_elim bad
    let e : Fin 4 → V := ![A.x,A.y,A.z,v]
    have nX : v ≠ A.x := nv 0
    have nY : v ≠ A.y := nv 1
    have nZ : v ≠ A.z := nv 2
    have ei : Function.Injective e := by
      intro i j h
      fin_cases i <;> fin_cases j <;>
        simp [e,A.xy.ne,Ne.symm A.xy.ne,A.xz.ne,Ne.symm A.xz.ne,A.nd,Ne.symm A.nd,
          nX,Ne.symm nX,nY,Ne.symm nY,nZ,Ne.symm nZ] at h ⊢
    have hO (i : Fin 4) : Outside F.c (e i) := by
      fin_cases i
      · exact A.sx.1
      · exact A.sy.1
      · exact A.sz.1
      · exact hv.1
    have hB (i : Fin 4) (j : Fin 6) : extraB t i j=true ↔ G.Adj (e i) (F.c j) := by
      fin_cases i
      · exact A.station_profile 0 j
      · exact A.station_profile 1 j
      · exact A.station_profile 2 j
      · simpa [extraB,e] using ht j
    have hE (i j : Fin 4) : extraE b i j=true ↔ G.Adj (e i) (e j) := by
      have mb (i : Fin 3) := bm i
      fin_cases i <;> fin_cases j <;>
        first | exact mb 0 | exact mb 1 | exact mb 2 |
          (first | exact (mb 0).trans ⟨fun h => h.symm, fun h => h.symm⟩ | exact (mb 1).trans ⟨fun h => h.symm, fun h => h.symm⟩ |
            exact (mb 2).trans ⟨fun h => h.symm, fun h => h.symm⟩) |
          (simp [extraE,e,G.loopless.irrefl,A.xy,A.xy.symm,A.xz,A.xz.symm,A.yz,
            show ¬G.Adj A.z A.y from fun h => A.yz h.symm])
    exact (F.reject_small e ei hO hB hE cert hcert).elim

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
theorem extra_unique {v w : V} (i : Fin 4) (hv : A.Extra v i) (hw : A.Extra w i) : v=w := by
  have hs : ∀ i : Fin 4,
      (∃ j k : Fin 6, j≠k ∧ contactsB (optionProfiles i) j=true ∧ contactsB (optionProfiles i) k=true) ∨
      ∃ j : Fin 6, ∃ a : Fin 3, contactsB (optionProfiles i) j=true ∧
        (optionMasks i).val.testBit a.val=true := by decide
  rcases hs i with ⟨j,k,n,hj,hk⟩ | ⟨j,a,hj,ha⟩
  · exact F.h4 (F.c j) (F.c k) v w (F.inj.ne n) ((hv.1 _).mp hj).symm
      ((hv.1 _).mp hk).symm ((hw.1 _).mp hj).symm ((hw.1 _).mp hk).symm
  · exact F.h4 (F.c j) (A.station a) v w (Ne.symm (A.station_out a j))
      ((hv.1 _).mp hj).symm ((hv.2 _).mp ha).symm
      ((hw.1 _).mp hj).symm ((hw.2 _).mp ha).symm

end Anchor
end Frame
end Graffiti133Hex

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {F : Frame G}

namespace Anchor
variable (A : Anchor F)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
theorem extra_pair {v w : V} {a b : Fin 4}
    (ha : A.Extra v a) (hb : A.Extra w b) (hab : a < b)
    (hv : Outside F.c v) (hw : Outside F.c w)
    (nv : ∀ i, v ≠ A.station i) (nw : ∀ i, w ≠ A.station i) :
    a = 0 ∧ b = 2 ∧ ¬ G.Adj v w := by
  classical
  let p : Bool := decide (G.Adj v w)
  have hp : p=true ↔ G.Adj v w := by simp [p]
  rcases double_extra_cert a b p hab with approved | bad
  · exact ⟨approved.1,approved.2.1,fun e => by simp [approved.2.2] at hp; exact hp e⟩
  · obtain ⟨cert,hcert⟩ := certCheck_elim bad
    have nV : v ≠ w := by
      intro eq
      have h : ∀ j, contactsB (optionProfiles a) j = contactsB (optionProfiles b) j := by
        intro j
        exact Bool.eq_iff_iff.mpr ((ha.1 j).trans (eq.symm ▸ (hb.1 j).symm))
      have distinct : ∀ a b : Fin 4, a < b →
          ¬(∀ j, contactsB (optionProfiles a) j = contactsB (optionProfiles b) j) := by decide
      exact distinct a b hab h
    let e : Fin 5 → V := ![A.x,A.y,A.z,v,w]
    have nX : v ≠ A.x := nv 0
    have nY : v ≠ A.y := nv 1
    have nZ : v ≠ A.z := nv 2
    have nX' : w ≠ A.x := nw 0
    have nY' : w ≠ A.y := nw 1
    have nZ' : w ≠ A.z := nw 2
    have hI : Function.Injective e := by
      intro i j h
      fin_cases i <;> fin_cases j <;>
        simp [e,A.xy.ne,Ne.symm A.xy.ne,A.xz.ne,Ne.symm A.xz.ne,A.nd,Ne.symm A.nd,
          nX,Ne.symm nX,nY,Ne.symm nY,nZ,Ne.symm nZ,
          nX',Ne.symm nX',nY',Ne.symm nY',nZ',Ne.symm nZ',nV,Ne.symm nV] at h ⊢
    have hO (i : Fin 5) : Outside F.c (e i) := by
      fin_cases i
      · exact A.sx.1
      · exact A.sy.1
      · exact A.sz.1
      · exact hv
      · exact hw
    have hB (i : Fin 5) (j : Fin 6) : doubleExtraB a b i j=true ↔ G.Adj (e i) (F.c j) := by
      fin_cases i
      · simpa [doubleExtraB,e,anchorB,station] using A.station_profile 0 j
      · simpa [doubleExtraB,e,anchorB,station] using A.station_profile 1 j
      · simpa [doubleExtraB,e,anchorB,station] using A.station_profile 2 j
      · simpa [doubleExtraB,e] using ha.1 j
      · simpa [doubleExtraB,e] using hb.1 j
    have hE (i j : Fin 5) : doubleExtraE a b p i j=true ↔ G.Adj (e i) (e j) := by
      have pb (i : Fin 3) := hb.2 i
      have pa (i : Fin 3) := ha.2 i
      fin_cases i <;> fin_cases j <;>
        first | exact pa 0 | exact pa 1 | exact pa 2 |
          exact pb 0 | exact pb 1 | exact pb 2 | exact hp | exact (show p = true ↔ G.Adj w v from ⟨fun h => (hp.mp h).symm,fun h => hp.mpr h.symm⟩) |
          (first | exact (pa 0).trans ⟨fun h => h.symm, fun h => h.symm⟩ | exact (pa 1).trans ⟨fun h => h.symm, fun h => h.symm⟩ |
            exact (pa 2).trans ⟨fun h => h.symm, fun h => h.symm⟩ | exact (pb 0).trans ⟨fun h => h.symm, fun h => h.symm⟩ |
            exact (pb 1).trans ⟨fun h => h.symm, fun h => h.symm⟩ | exact (pb 2).trans ⟨fun h => h.symm, fun h => h.symm⟩ |
            exact (hp).trans ⟨fun h => h.symm, fun h => h.symm⟩) |
          (simp [doubleExtraE,e,G.loopless.irrefl,A.xy,A.xy.symm,A.xz,A.xz.symm,A.yz,
            show ¬G.Adj A.z A.y from fun h => A.yz h.symm])
    exact (F.reject_small e hI hO hB hE cert hcert).elim

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private noncomputable def farModelB (i : Fin 5) : Fin 6 → Bool :=
  if i=4 then fun _ => false else contactsB (![0,2,3,14,0] i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private def farModelE (i j : Fin 5) : Bool := decide
  ((i=0 ∧ (j=1 ∨ j=2)) ∨ (j=0 ∧ (i=1 ∨ i=2)) ∨
   (i=1 ∧ j=3) ∨ (i=3 ∧ j=1) ∨ (i=3 ∧ j=4) ∨ (i=4 ∧ j=3))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
private lemma far_model_cert :
    CertTrue (SmallRel farModelB farModelE) (.path ![0,6,8,3,2,9,10]) := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
theorem no_far_extra_three {v r : V} (hv : A.Extra v 3) (ho : Outside F.c v)
    (nv : ∀ i, v ≠ A.station i) (hr : F.Far r) (ev : G.Adj v r) : False := by
  classical
  let e : Fin 5 → V := ![A.x,A.y,A.z,v,r]
  have nX : v ≠ A.x := nv 0
  have nY : v ≠ A.y := nv 1
  have nZ : v ≠ A.z := nv 2
  have rX : r ≠ A.x := fun he => hr.2 0 (he.symm ▸ (A.sx.2 0).mpr rfl)
  have rY : r ≠ A.y := fun he => hr.2 2 (he.symm ▸ (A.sy.2 2).mpr rfl)
  have rZ : r ≠ A.z := fun he => hr.2 3 (he.symm ▸ (A.sz.2 3).mpr rfl)
  have rx : ¬G.Adj A.x r := by
    intro he
    obtain ⟨k,hk⟩ := F.far_edge_opposite ⟨A.sx.1,⟨0,(A.sx.2 0).mpr rfl⟩⟩ hr he
    have h := ((A.sx.2 _).mp ((hk.2 _).mpr (Or.inl rfl))).trans
      ((A.sx.2 _).mp ((hk.2 _).mpr (Or.inr rfl))).symm
    exact (by decide : ∀ k : Fin 3, frontInd k ≠ frontInd k+3) k h
  have ry : ¬G.Adj A.y r := by
    intro he
    obtain ⟨k,hk⟩ := F.far_edge_opposite ⟨A.sy.1,⟨2,(A.sy.2 2).mpr rfl⟩⟩ hr he
    have h := ((A.sy.2 _).mp ((hk.2 _).mpr (Or.inl rfl))).trans
      ((A.sy.2 _).mp ((hk.2 _).mpr (Or.inr rfl))).symm
    exact (by decide : ∀ k : Fin 3, frontInd k ≠ frontInd k+3) k h
  have rz : ¬G.Adj A.z r := by
    intro he
    obtain ⟨k,hk⟩ := F.far_edge_opposite ⟨A.sz.1,⟨3,(A.sz.2 3).mpr rfl⟩⟩ hr he
    have h := ((A.sz.2 _).mp ((hk.2 _).mpr (Or.inl rfl))).trans
      ((A.sz.2 _).mp ((hk.2 _).mpr (Or.inr rfl))).symm
    exact (by decide : ∀ k : Fin 3, frontInd k ≠ frontInd k+3) k h
  have hI : Function.Injective e := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [e,A.xy.ne,Ne.symm A.xy.ne,A.xz.ne,Ne.symm A.xz.ne,A.nd,Ne.symm A.nd,
        nX,Ne.symm nX,nY,Ne.symm nY,nZ,Ne.symm nZ,rX,Ne.symm rX,rY,Ne.symm rY,rZ,Ne.symm rZ,
        ev.ne,Ne.symm ev.ne] at h ⊢
  have hO (i : Fin 5) : Outside F.c (e i) := by
    fin_cases i
    · exact A.sx.1
    · exact A.sy.1
    · exact A.sz.1
    · exact ho
    · exact hr.1
  have hB (i : Fin 5) (j : Fin 6) : farModelB i j=true ↔ G.Adj (e i) (F.c j) := by
    fin_cases i
    · simpa [farModelB,e,anchorB,station] using A.station_profile 0 j
    · simpa [farModelB,e,anchorB,station] using A.station_profile 1 j
    · simpa [farModelB,e,anchorB,station] using A.station_profile 2 j
    · exact hv.1 j
    · simp [farModelB,e,hr.2 j]
  have hE (i j : Fin 5) : farModelE i j=true ↔ G.Adj (e i) (e j) := by
    have pe (i : Fin 3) := hv.2 i
    fin_cases i <;> fin_cases j <;>
      first |
        exact pe 0 | exact pe 1 | exact pe 2 |
        (first | exact (pe 0).trans ⟨fun h => h.symm, fun h => h.symm⟩ | exact (pe 1).trans ⟨fun h => h.symm, fun h => h.symm⟩ |
          exact (pe 2).trans ⟨fun h => h.symm, fun h => h.symm⟩) |
        (simp [farModelE,e,G.loopless.irrefl,A.xy,A.xy.symm,A.xz,A.xz.symm,A.yz,ev,ev.symm,rx,ry,rz,
          show ¬G.Adj A.z A.y from fun h => A.yz h.symm,
          show ¬G.Adj r A.x from fun h => rx h.symm,
          show ¬G.Adj r A.y from fun h => ry h.symm,
          show ¬G.Adj r A.z from fun h => rz h.symm])
  exact F.reject_small e hI hO hB hE _ far_model_cert

end Anchor
end Frame
end Graffiti133Hex

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {F : Frame G}

namespace Anchor
variable (A : Anchor F)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
theorem opp_not_station {x : V} {i : Fin 3} (hi : F.Opp x i) :
    ∀ s, x ≠ A.station s := by
  have ns {j : Fin 6} (h : F.Single x j) : False := by
    have h1 := (h.2 _).mp ((hi.2 _).mpr (Or.inl rfl))
    have h2 := (h.2 _).mp ((hi.2 _).mpr (Or.inr rfl))
    exact (by decide : ∀ i : Fin 3, frontInd i ≠ frontInd i+3) i (h1.trans h2.symm)
  intro s eq
  fin_cases s
  · change x=A.x at eq
    exact ns (eq.symm ▸ A.sx)
  · change x=A.y at eq
    exact ns (eq.symm ▸ A.sy)
  · change x=A.z at eq
    exact ns (eq.symm ▸ A.sz)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
theorem any_far_opp_is_two {o r : V} {j : Fin 3} (ho : F.Opp o j)
    (hr : F.Far r) (e : G.Adj o r) : A.Extra o 2 := by
  have nv := A.opp_not_station ho
  obtain ⟨k,hk⟩ := A.extra_classify ⟨ho.1,frontInd j,(ho.2 _).mpr (Or.inl rfl)⟩ nv
  have check : ∀ a : Fin 4, ∀ i : Fin 3,
      (∀ l, contactsB (optionProfiles a) l=true ↔ l=frontInd i ∨ l=frontInd i+3) →
      a=2 ∨ a=3 := by decide
  rcases check k j (fun l => (hk.1 l).trans (ho.2 l)) with rfl | rfl
  · exact hk
  · exact (A.no_far_extra_three hk ho.1 nv hr e).elim

include A in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
theorem high_no_far (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r) :
    ∀ r, ¬F.Far r := by
  classical
  intro r hr
  obtain ⟨o,i,hoi,hor⟩ := F.far_has_opp hc hm r hr
  have hO := A.any_far_opp_is_two hoi hr hor
  have allSides (a : V) (ha : G.Adj r a) : F.Far a ∨ a=o := by
    by_cases f : F.Far a
    · exact Or.inl f
    · obtain ⟨j,hj⟩ := F.far_neighbor_opp hr ha.symm f
      exact Or.inr (A.extra_unique 2 (A.any_far_opp_is_two hj hr ha.symm) hO)
  have allFar (a : V) (ha : F.Far a) : G.Adj o a := by
    obtain ⟨w,j,hw,ewa⟩ := F.far_has_opp hc hm a ha
    exact A.extra_unique 2 (A.any_far_opp_is_two hw ha ewa) hO ▸ ewa
  obtain ⟨S,hS,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) r
  obtain ⟨nh,ih⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hS
  have least := hm r
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (show 1<S.card by omega)
  have ra := nh a ha
  have rb := nh b hb
  rcases allSides a ra with fA | rfl <;> rcases allSides b rb with fB | rfl
  · exact ab (F.h4 r o a b hor.ne.symm ra (allFar _ fA) rb (allFar _ fB))
  · exact ih a ha _ hb (allFar _ fA).symm
  · exact ih _ ha b hb (allFar _ fB)
  · exact ab rfl

end Anchor
end Frame
end Graffiti133Hex

namespace Graffiti133Hex
open Frame
open Graffiti133NoFive Finset
open scoped BigOperators

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
abbrev HighSlot := Fin 6 ⊕ (Fin 3 ⊕ Fin 4)
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
def cSlot (i : Fin 6) : HighSlot := .inl i
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
def sSlot (i : Fin 3) : HighSlot := .inr (.inl i)
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
def eSlot (i : Fin 4) : HighSlot := .inr (.inr i)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
def SlotAdj : HighSlot → HighSlot → Prop
| .inl i, .inl j => Cyclic i j
| .inl j, .inr (.inl i) => anchorB 2 3 i j = true
| .inr (.inl i), .inl j => anchorB 2 3 i j = true
| .inl j, .inr (.inr i) => contactsB (optionProfiles i) j = true
| .inr (.inr i), .inl j => contactsB (optionProfiles i) j = true
| .inr (.inl i), .inr (.inl j) => anchorE i j = true
| .inr (.inr i), .inr (.inl j) => (optionMasks i).val.testBit j.val = true
| .inr (.inl j), .inr (.inr i) => (optionMasks i).val.testBit j.val = true
| .inr (.inr _), .inr (.inr _) => False

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
noncomputable instance : DecidableRel SlotAdj := by
  intro i j
  cases i with
  | inl i => cases j with
      | inl j => unfold SlotAdj; infer_instance
      | inr j => cases j <;> unfold SlotAdj <;> infer_instance
  | inr i =>
    cases i <;> cases j
    all_goals first | (unfold SlotAdj; infer_instance) | (rename_i q; cases q <;> unfold SlotAdj <;> infer_instance)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
def SlotActive (b : Fin 4 → Bool) : HighSlot → Bool
| .inl _ | .inr (.inl _) => true
| .inr (.inr i) => b i

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
def activeSlots (b : Fin 4 → Bool) : Finset HighSlot :=
  Finset.univ.filter (fun i => SlotActive b i=true)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
noncomputable def slotDegree (S : Finset HighSlot) (i : HighSlot) : ℕ :=
  (S.filter (SlotAdj i)).card

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
def Legal (b : Fin 4 → Bool) : Prop :=
  ∀ i j : Fin 4, i<j → b i = true → b j = true → i=0 ∧ j=2

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
instance (b : Fin 4 → Bool) : Decidable (Legal b) := by
  unfold Legal
  infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 30000 in
theorem model_budget (b : Fin 4 → Bool) (hb : Legal b) :
    (∑ i∈activeSlots b, slotDegree (activeSlots b) i) ≤ 3*(activeSlots b).card := by
  revert b
  decide

end Graffiti133Hex

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {F : Frame G}

namespace Anchor
variable (A : Anchor F)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private def Label (v : V) : HighSlot → Prop
| .inl i => v=F.c i
| .inr (.inl i) => v=A.station i
| .inr (.inr i) => Outside F.c v ∧ (∀ j, v ≠ A.station j) ∧ A.Extra v i

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private theorem label_exists (noFar : ∀ v, ¬F.Far v) (v : V) : ∃ i, A.Label v i := by
  classical
  by_cases out : Outside F.c v
  · by_cases station : ∃ i, v=A.station i
    · obtain ⟨i,hi⟩ := station
      exact ⟨sSlot i,hi⟩
    · have no (i : Fin 3) : v ≠ A.station i := fun h => station ⟨i,h⟩
      have near : F.Near v := by
        refine ⟨out,?_⟩
        apply Classical.byContradiction
        intro h
        exact noFar v ⟨out,fun i e => h ⟨i,e⟩⟩
      obtain ⟨i,hi⟩ := A.extra_classify near no
      exact ⟨eSlot i,out,no,hi⟩
  · obtain ⟨i,hi⟩ := F.exists_cycle out
    exact ⟨cSlot i,hi⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private theorem oma133_HexFlattened133_label_inj {v w : V} {i : HighSlot} (h : A.Label v i) (hw : A.Label w i) : v=w := by
  rcases i with i | i
  · exact h.trans hw.symm
  · rcases i with i | i
    · exact h.trans hw.symm
    · exact A.extra_unique i h.2.2 hw.2.2

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private theorem label_functional {v : V} {i j : HighSlot}
    (h : A.Label v i) (hj : A.Label v j) : i=j := by
  have cp : ∀ a b : Fin 4,
      (∀ i, (contactsB (optionProfiles a) i=true ↔ contactsB (optionProfiles b) i=true)) →
      a=b := by decide
  cases i with
  | inl a =>
    cases j with
    | inl b => exact congrArg cSlot (F.inj (h.symm.trans hj))
    | inr j =>
      cases j with
      | inl b => exact (A.station_out b a (hj.symm.trans h)).elim
      | inr b => exact (hj.1 a h).elim
  | inr i =>
    cases i with
    | inl a =>
      cases j with
      | inl b => exact (A.station_out a b (h.symm.trans hj)).elim
      | inr j =>
        cases j with
        | inl b => exact congrArg sSlot (A.station_inj (h.symm.trans hj))
        | inr b => exact (hj.2.1 a h).elim
    | inr a =>
      cases j with
      | inl b => exact (h.1 b hj).elim
      | inr j =>
        cases j with
        | inl b => exact (h.2.1 b hj).elim
        | inr b =>
          exact congrArg eSlot (cp a b (fun l => (h.2.2.1 l).trans (hj.2.2.1 l).symm))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private theorem label_adjacency {v w : V} {i j : HighSlot}
    (hi : A.Label v i) (hj : A.Label w j) : G.Adj v w ↔ SlotAdj i j := by
  rcases i with a | a
  · rcases j with b | b
    · change v=F.c a at hi
      change w=F.c b at hj
      simpa only [hi,hj,SlotAdj] using F.adj a b
    · rcases b with b | b
      · change v=F.c a at hi
        change w=A.station b at hj
        rw [hi,hj,G.adj_comm]
        exact (A.station_profile b a).symm
      · change v=F.c a at hi
        rw [hi,G.adj_comm]
        exact (hj.2.2.1 a).symm
  · rcases a with a | a
    · rcases j with b | b
      · change v=A.station a at hi
        change w=F.c b at hj
        rw [hi,hj]
        exact (A.station_profile a b).symm
      · rcases b with b | b
        · change v=A.station a at hi
          change w=A.station b at hj
          rw [hi,hj]
          exact (A.station_edges a b).symm
        · change v=A.station a at hi
          rw [hi,G.adj_comm]
          exact (hj.2.2.2 a).symm
    · rcases j with b | b
      · change w=F.c b at hj
        rw [hj]
        exact (hi.2.2.1 b).symm
      · rcases b with b | b
        · change w=A.station b at hj
          rw [hj]
          exact (hi.2.2.2 b).symm
        · refine ⟨fun h => ?_,False.elim⟩
          rcases lt_trichotomy a b with lt | eq | gt
          · exact (A.extra_pair hi.2.2 hj.2.2 lt hi.1 hj.1 hi.2.1 hj.2.1).2.2 h
          · subst b
            exact h.ne (A.oma133_HexFlattened133_label_inj hi hj)
          · exact (A.extra_pair hj.2.2 hi.2.2 gt hj.1 hi.1 hj.2.1 hi.2.1).2.2 h.symm

include A in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
theorem high_hex_budget (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r) :
    (∑ x, localIndependence G x) ≤ 3 * Fintype.card V := by
  classical
  let f (v : V) : HighSlot := Classical.choose (A.label_exists (A.high_no_far hc hm) v)
  have hf (v : V) : A.Label v (f v) := Classical.choose_spec (A.label_exists (A.high_no_far hc hm) v)
  have inj : Function.Injective f := by
    intro v w h
    exact A.oma133_HexFlattened133_label_inj (hf v) (h.symm ▸ hf w)
  let S := (Finset.univ : Finset V).image f
  have cover (i : HighSlot) : i∈S ↔ ∃ v, A.Label v i := by
    constructor
    · intro h
      obtain ⟨v,_,hv⟩ := Finset.mem_image.mp h
      exact ⟨v,hv ▸ hf v⟩
    · rintro ⟨v,hv⟩
      exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,A.label_functional (hf v) hv⟩
  let b (i : Fin 4) := decide (eSlot i∈S)
  have hb (i : Fin 4) : b i=true ↔ eSlot i ∈ S := by simp [b]
  have isActive : activeSlots b = S := by
    ext i
    rcases i with i | i
    · have hs := (cover (cSlot i)).mpr ⟨F.c i,rfl⟩
      rw [activeSlots, Finset.mem_filter]
      exact ⟨fun _ => hs, fun _ => ⟨Finset.mem_univ _, rfl⟩⟩
    · rcases i with i | i
      · have hs := (cover (sSlot i)).mpr ⟨A.station i,rfl⟩
        rw [activeSlots, Finset.mem_filter]
        exact ⟨fun _ => hs, fun _ => ⟨Finset.mem_univ _, rfl⟩⟩
      · rw [activeSlots, Finset.mem_filter]
        exact ⟨fun h => (hb i).mp h.2, fun h => ⟨Finset.mem_univ _, (hb i).mpr h⟩⟩
  have legal : Legal b := by
    intro i j hij hi hj
    obtain ⟨v,hv⟩ := (cover _).mp ((hb i).mp hi)
    obtain ⟨w,hw⟩ := (cover _).mp ((hb j).mp hj)
    exact ⟨(A.extra_pair hv.2.2 hw.2.2 hij hv.1 hw.1 hv.2.1 hw.2.1).1,
      (A.extra_pair hv.2.2 hw.2.2 hij hv.1 hw.1 hv.2.1 hw.2.1).2.1⟩
  have bound (v : V) : localIndependence G v ≤ slotDegree S (f v) := by
    obtain ⟨T,hT,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
    have near := (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hT).1
    have sub (w : V) (hw : w∈T) : f w∈S.filter (SlotAdj (f v)) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩,
        (A.label_adjacency (hf v) (hf w)).mp (near w hw)⟩
    rw [←eq]
    exact Finset.card_le_card_of_injOn f sub inj.injOn
  have bd := model_budget b legal
  rw [isActive] at bd
  calc
    (∑ v, localIndependence G v) ≤ ∑ v, slotDegree S (f v) :=
      Finset.sum_le_sum (fun v _ => bound v)
    _ = ∑ j∈S,slotDegree S j := by
      symm
      exact Finset.sum_image (fun _ _ _ _ h => inj h)
    _ ≤ 3*S.card := bd
    _ = 3*Fintype.card V := by simp [S,Finset.card_image_of_injective _ inj]

end Anchor

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
theorem hex_budget (F : Frame G) (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r) :
    (∑ x, localIndependence G x) ≤ 3 * Fintype.card V := by
  by_cases low : ∀ x i, F.Single x i → localIndependence G x ≤ 2
  · exact F.low_hex_budget hc hm low
  · push_neg at low
    obtain ⟨x,i,hx,hhigh⟩ := low
    obtain ⟨H,⟨anchor⟩⟩ := F.high_has_anchor hx (by omega)
    exact anchor.high_hex_budget hc hm

end Frame
end Graffiti133Hex

namespace Graffiti133FarPentagon
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133NoFive Finset
open scoped BigOperators
universe u

variable {V : Type u} [Fintype V]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 30000 in
private def HasP7 (G : SimpleGraph V) : Prop :=
  ∃ f : Fin 7 → V, InducedPath G f

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 30000 in
private theorem connected_peel_P7_strict (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G)
    (hD : 3*Fintype.card V < (∑ v, localIndependence G v))
    (core : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W), J.Connected →
      FourCycleFree J → (∀ v, 2 ≤ localIndependence J v) →
      3*Fintype.card W < (∑ v, localIndependence J v) →
      HasP7 J) :
    HasP7 G := by
  classical
  let Claim (n : ℕ) := ∀ (W : Type u) [Fintype W] (J : SimpleGraph W),
    Fintype.card W=n → J.Connected → FourCycleFree J →
    3*Fintype.card W < (∑ v, localIndependence J v) →
    HasP7 J
  have aux (n : ℕ) : Claim n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ G hn hC h4 dens
      letI := hC.nonempty
      by_cases hmin : ∀ v, 2 ≤ localIndependence G v
      · exact core W G hC h4 hmin dens
      push_neg at hmin
      obtain ⟨v,hv⟩ := hmin
      let S : Set W := {w | w ≠ v}
      let H := G.induce S
      have hpos : 0 < Fintype.card W := Fintype.card_pos
      have hS : Fintype.card S + 1 = Fintype.card W := by
        have hs : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card {x : W // ¬ x = v} = _
          rw [Fintype.card_subtype_compl]
          rw [show Fintype.card {x : W // x = v} = 1 from Fintype.card_unique]
        omega
      have h4' : FourCycleFree H := by
        intro a b x y hab hax hbx hay hby
        apply Subtype.ext
        exact h4 _ _ _ _ (fun h => hab (Subtype.ext h)) hax hbx hay hby
      have non : Nonempty S := by
        have pos : 0 < (∑ v, localIndependence G v) := by omega
        obtain ⟨a,b,ab⟩ : ∃ a b, G.Adj a b := by
          apply Classical.byContradiction
          intro no
          have eq : ∀ x, localIndependence G x = 0 := by
            intro x
            obtain ⟨A,hA,hc⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
            rw [← hc,Finset.card_eq_zero]
            apply Finset.not_nonempty_iff_eq_empty.mp
            rintro ⟨a,ha⟩
            exact no ⟨x,a,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 a ha⟩
          simp [eq] at pos
        by_cases ha : a=v
        · exact ⟨⟨b,(ha ▸ ab.ne).symm⟩⟩
        · exact ⟨⟨a,ha⟩⟩
      have hConn : H.Connected := connected_delete_low_local G hC v (by omega) non
      have loss := local_sum_delete_bound G h4 v
      have dH : 3*Fintype.card S < (∑ w, localIndependence H w) := by
        rw [← hS,Nat.mul_add,Nat.mul_one] at dens
        change (∑ w, localIndependence G w) ≤ (∑ w : S, localIndependence H w) +
          2*localIndependence G v at loss
        omega
      have witness := ih _ (by omega : Fintype.card S < n) S H rfl hConn h4' dH
      obtain ⟨f,hf⟩ := witness
      exact ⟨fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
  exact aux (Fintype.card V) V G rfl hc h4 hD

open Graffiti133Hex in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 30000 in
theorem strict_mean_three_using_holes (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (hmean : 3 < averageLocal G)
    (six : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (_F : Graffiti133Hex.Frame J),
      J.Connected → (∀ r, 2 ≤ localIndependence J r) →
      (∑ r, localIndependence J r) ≤ 3*Fintype.card W)
    (seven : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W), J.Connected →
      FourCycleFree J → (∀ r, 2 ≤ localIndependence J r) →
      ¬HasP7 J → ¬Nonempty (Hole J 6) → Hole J 7 →
      (∑ r, localIndependence J r) ≤ 3*Fintype.card W) :
    ∃ f : Fin 7 → V, InducedPath G f := by
  classical
  letI := hc.nonempty
  have dens : 3*Fintype.card V < (∑ r, localIndependence G r) := by
    unfold averageLocal at hmean
    have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α:=V)
    have h := (lt_div_iff₀ hpos).mp hmean
    rw [← Nat.cast_sum] at h
    exact_mod_cast h
  apply connected_peel_P7_strict G hc h4 dens
  intro W _ J hJ h4 hm hsum
  letI := hJ.nonempty
  have av : 3 ≤ averageLocal J := by
    unfold averageLocal
    have hpos : (0 : ℚ) < Fintype.card W := by exact_mod_cast Fintype.card_pos (α:=W)
    apply (le_div_iff₀ hpos).mpr
    rw [← Nat.cast_sum]
    exact_mod_cast hsum.le
  by_cases p : HasP7 J
  · exact p
  by_cases hh : Nonempty (Hole J 6)
  · obtain ⟨H⟩ := hh
    exact ((not_lt_of_ge (six W J ⟨H,h4,p⟩ hJ hm)) hsum).elim
  rcases local_mean_three_path_or_hole J hJ h4 av with xx | xx | xx
  · exact xx
  · exact (hh xx).elim
  · obtain ⟨H⟩ := xx
    exact ((not_lt_of_ge (seven W J hJ h4 hm p hh H)) hsum).elim

end Graffiti133FarPentagon

namespace Graffiti133Revisit
open Graffiti133 Graffiti133FarPentagon SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 30000 in
theorem P7_of_strict_mean_three (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (ha : 3 < averageLocal G) :
    ∃ f : Fin 7 → V, InducedPath G f := by
  apply strict_mean_three_using_holes G hc h4 ha
  · intro W _ J F c m
    exact Graffiti133Hex.Frame.hex_budget F c m
  · intro W _ J c h4 m no7 no6 H
    exact (Graffiti133C7Only.sum_lt_three_of_hole_seven_no_six H h4 no7 no6 c m).le

end Graffiti133Revisit

end OMA133_HexFlattened133

namespace OMA133Port
open SimpleGraph Finset
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

def inducedList (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ ∀ i j : Fin p.length, G.Adj (p.get i) (p.get j) ↔
    i.val+1=j.val ∨ j.val+1=i.val

theorem inducedList_ofFn (G : SimpleGraph V) {n : ℕ} (f : Fin n→V)
    (hf : Graffiti133.InducedPath G f) : inducedList G (List.ofFn f) := by
  refine ⟨List.nodup_ofFn.mpr hf.1,?_⟩
  intro i j
  have hi : i.val<n := by simpa using i.isLt
  have hj : j.val<n := by simpa using j.isLt
  let a : Fin n := ⟨i.val,hi⟩
  let b : Fin n := ⟨j.val,hj⟩
  have ha : (List.ofFn f).get i=f a := by simp [a,List.get_eq_getElem]
  have hb : (List.ofFn f).get j=f b := by simp [b,List.get_eq_getElem]
  rw [ha,hb]
  rcases lt_trichotomy a b with ab|same|ba
  · rw [hf.2 _ _ ab]
    have ab' : i.val < j.val := ab
    change i.val+1=j.val ↔ _
    omega
  · have eq : i.val=j.val := congrArg (fun t : Fin n => t.val) same
    rw [same]
    simp [show i.val+1≠j.val by omega,show j.val+1≠i.val by omega]
  · rw [SimpleGraph.adj_comm,hf.2 _ _ ba]
    have ba' : j.val < i.val := ba
    change j.val+1=i.val ↔ _
    omega

theorem neighborhood_indepNum_eq (G : SimpleGraph V) (v : V) :
    (G.induce (G.neighborSet v)).indepNum = Graffiti133.localIndependence G v := by
  classical
  let H := G.induce (G.neighborSet v)
  have setMem (T : Finset V) : T∈Graffiti133.localIndependentSets G v ↔
      (∀ x∈T,G.Adj v x) ∧ ∀ x∈T,∀ y∈T,¬ G.Adj x y := by
    simp only [Graffiti133.localIndependentSets, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_iff, Finset.mem_univ, true_and]
  apply le_antisymm
  · obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
    let T := s.map (Function.Embedding.subtype _)
    have Tm : T ∈ Graffiti133.localIndependentSets G v := (setMem T).mpr (by
      constructor
      · intro x hx
        obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hx
        exact y.2
      · intro x hx y hy ad
        obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hy
        have ane : a≠b := fun eq=>ad.ne (congrArg Subtype.val eq)
        exact hs.isIndepSet ha hb ane ad)
    have tl : T.card ≤ Graffiti133.localIndependence G v := Finset.le_sup (f := Finset.card) Tm
    rwa [Finset.card_map, hs.card_eq] at tl
  · apply Finset.sup_le_iff.mpr
    intro T Tm
    obtain ⟨tb,ti⟩ := (setMem T).mp Tm
    let U : Finset (G.neighborSet v) := T.subtype (fun x=>x∈G.neighborSet v)
    have eq : U.card=T.card := by
      rw [Finset.card_subtype]
      congr 1
      exact Finset.filter_true_of_mem (fun x hx=>tb x hx)
    rw [←eq]
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    intro a ha b hb _
    exact ti _ (Finset.mem_subtype.mp ha) _ (Finset.mem_subtype.mp hb)

noncomputable def meanReal (G : SimpleGraph V) : ℝ :=
  (∑ v, ((G.induce (G.neighborSet v)).indepNum : ℝ))/Fintype.card V

theorem meanReal_eq (G : SimpleGraph V) : meanReal G=(Graffiti133.averageLocal G : ℝ) := by
  unfold meanReal Graffiti133.averageLocal
  have hs := map_sum (Rat.castHom ℝ)
    (fun v : V => (Graffiti133.localIndependence G v : ℚ)) (Finset.univ : Finset V)
  simp only [Rat.castHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] at hs
  rw [Rat.cast_div, hs, Rat.cast_natCast]
  simp only [neighborhood_indepNum_eq, Rat.cast_natCast]

theorem radius_three_path_six_bound (G : SimpleGraph V) (hc : G.Connected)
    (h4 : ¬ ∃ a b c d : V, a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)
    (path : ℕ) (pathUpper : ∀ p : List V, inducedList G p→p.length≤path) (hp : path=6) :
    meanReal G≤3 := by
  by_contra hh
  have ha : 3 < Graffiti133.averageLocal G := by
    have hreal : (3:ℝ) < (Graffiti133.averageLocal G : ℝ) := by
      rw [← meanReal_eq]
      exact lt_of_not_ge hh
    exact_mod_cast hreal
  obtain ⟨f,hf⟩ := Graffiti133Revisit.P7_of_strict_mean_three G hc ((Graffiti133.fourCycleFree_iff G).mpr h4) ha
  have hl := pathUpper (List.ofFn f) (inducedList_ofFn G f hf)
  simp [hp] at hl

end OMA133Port

-- Credit: @vjdad4m
-- This proof ports the earlier induced-seven theorem from vjdad4m/maths.
theorem OMA.solution :
    OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1.H1 := by
  intro V _ _ _ G hc h4 _ hp _ _
  exact OMA133Port.radius_three_path_six_bound G hc h4 (SimpleGraph.path G)
    (fun p h => SimpleGraph.length_le_path_of_isInducedPath G p h) hp
