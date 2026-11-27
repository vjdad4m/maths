import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! A small reflected obstruction for Graffiti.pc #183's 7-cycle case.
Labels 0..6 are cyclic, 7 is the 4-run vertex, 8 and 9 its left and right blockers. -/
namespace Graffiti183.Run4Cert
open SimpleGraph
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

def halfAdj (l r e : Bool) (x y : Fin 10) : Prop :=
  (y.val < 7 ∧ (x.val+1=y.val ∨ (x.val=0 ∧ y.val=6))) ∨
  (y.val=7 ∧ x.val≤3) ∨
  (y.val=8 ∧ (x.val=6 ∨ x.val≤1 ∨ (l=true ∧ x.val=2))) ∨
  (y.val=9 ∧ (2≤x.val ∧ x.val≤4 ∨ (r=true ∧ x.val=1) ∨ (e=true ∧ x.val=8)))

instance (l r e : Bool) (x y : Fin 10) : Decidable (halfAdj l r e x y) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def adj (l r e : Bool) (x y : Fin 10) : Prop :=
  halfAdj l r e x y ∨ halfAdj l r e y x

instance (l r e : Bool) (x y : Fin 10) : Decidable (adj l r e x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

def Claw (l r e : Bool) (c x y z : Fin 10) : Prop :=
  adj l r e c x ∧ adj l r e c y ∧ adj l r e c z ∧
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
  ¬ adj l r e x y ∧ ¬ adj l r e x z ∧ ¬ adj l r e y z

instance (l r e : Bool) (c x y z : Fin 10) : Decidable (Claw l r e c x y z) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem claw_classification (l r e : Bool) :
    (l=false ∧ r=false ∧ e=false) ∨
    (l=true ∧ r=true ∧ e=true) ∨
    ∃ c x y z, Claw l r e c x y z := by
  cases l <;> cases r <;> cases e
  · exact Or.inl ⟨rfl,rfl,rfl⟩
  · exact Or.inr (Or.inr ⟨8,1,6,9,by decide⟩)
  · exact Or.inr (Or.inr ⟨1,7,8,9,by decide⟩)
  · exact Or.inr (Or.inr ⟨9,2,4,8,by decide⟩)
  · exact Or.inr (Or.inr ⟨2,7,8,9,by decide⟩)
  · exact Or.inr (Or.inr ⟨8,1,6,9,by decide⟩)
  · exact Or.inr (Or.inr ⟨1,7,8,9,by decide⟩)
  · exact Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)

def row (k : Fin 4) (i : Fin 7) : Fin 10 :=
  ([[5,4,9,2,7,0,8],[5,6,8,1,7,3,9],[7,1,8,6,5,4,9],[7,2,9,4,5,6,8]] :
    List (List (Fin 10))).getD k.val [] |>.getD i.val 0

def IsIndPath {W : Type*} (E : W → W → Prop) (f : Fin 7 → W) : Prop :=
  Function.Injective f ∧ ∀ i j, E (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val

instance {W : Type*} [DecidableEq W] (E : W → W → Prop) [DecidableRel E]
    (f : Fin 7 → W) : Decidable (IsIndPath E f) :=
  inferInstanceAs (Decidable ((∀ i j, f i = f j → i = j) ∧ _))

theorem row_path (k : Fin 4) : IsIndPath (adj false false false) (row k) := by
  fin_cases k <;> decide +kernel

def close (x y : Fin 10) : Prop :=
  x=y ∨ adj false false false x y ∨
    ∃ z : Fin 10, adj false false false x z ∧ adj false false false z y

instance (x y : Fin 10) : Decidable (close x y) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def cyc (x : Fin 7) : Fin 10 := Fin.castLE (by decide) x

theorem covered_far_pair : ∀ x y : Fin 7, ¬ close (cyc x) (cyc y) →
    ∃ k : Fin 4, (∃ i, row k i = cyc x) ∧ (∃ j, row k j = cyc y) := by
  decide +kernel

/-- An induced copy of the displayed ten-vertex graph either has both
extras and the blocker edge, contains a claw, or has an induced seven-path
containing any prescribed cycle pair at distance greater than two. -/
theorem lift {W : Type*} (H : SimpleGraph W) (f : Fin 10 ↪ W)
    (l r e : Bool) (model : ∀ x y, H.Adj (f x) (f y) ↔ adj l r e x y)
    (clawfree : ∀ {c x y z : W}, H.Adj c x → H.Adj c y → H.Adj c z →
      x ≠ y → x ≠ z → y ≠ z → ¬ H.Adj x y → ¬ H.Adj x z → H.Adj y z)
    (x y : Fin 7) (far : 2 < H.dist (f (cyc x)) (f (cyc y))) :
    (l=true ∧ r=true ∧ e=true) ∨
      ∃ p : Fin 7 ↪ W,
        (∀ i j, H.Adj (p i) (p j) ↔ i.val+1=j.val ∨ j.val+1=i.val) ∧
        (∃ i, p i = f (cyc x)) ∧ (∃ j, p j = f (cyc y)) := by
  rcases claw_classification l r e with h | h | h
  · rcases h with ⟨rfl,rfl,rfl⟩
    have nf : ¬ close (cyc x) (cyc y) := by
      rintro (eq | h | ⟨z,a,b⟩)
      · rw [eq,SimpleGraph.dist_self] at far
        omega
      · have du := (model _ _).mpr h
        rw [dist_eq_one_iff_adj.mpr du] at far
        omega
      · have du := H.dist_le (Walk.cons ((model _ _).mpr a) ((model _ _).mpr b).toWalk)
        change H.dist (f (cyc x)) (f (cyc y)) ≤ 2 at du
        omega
    obtain ⟨k,⟨i,hi⟩,⟨j,hj⟩⟩ := covered_far_pair x y nf
    have hp := row_path k
    right
    refine ⟨⟨f ∘ row k,f.injective.comp hp.1⟩,?_,⟨i,congrArg f hi⟩,⟨j,congrArg f hj⟩⟩
    exact fun a b => (model _ _).trans (hp.2 a b)
  · exact Or.inl h
  · obtain ⟨c,a,b,d,h1,h2,h3,nab,nad,nbd,gab,gad,gbd⟩ := h
    exact (gbd ((model _ _).mp (clawfree
      ((model _ _).mpr h1) ((model _ _).mpr h2) ((model _ _).mpr h3)
      (f.injective.ne nab) (f.injective.ne nad) (f.injective.ne nbd)
      (fun w => gab ((model _ _).mp w)) (fun w => gad ((model _ _).mp w))))).elim

#print axioms lift
end Graffiti183.Run4Cert
