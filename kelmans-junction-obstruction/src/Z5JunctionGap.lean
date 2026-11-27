import TinyClosedReflection
import CenteredJunctionZ5Geometry

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.Z5JunctionGap
open Substitute
abbrev V := Fin 10

def rawEdges : List (V × V) :=
  [(0,4),(0,6),(0,7),(1,8),(1,5),(1,7),(2,8),(2,9),(2,5),
    (3,9),(3,6),(3,7),(4,8),(4,9),(5,6)]

def H : SimpleGraph V where
  Adj u v := (u,v) ∈ rawEdges ∨ (v,u) ∈ rawEdges
  symm := fun _ _ h=>h.elim Or.inr Or.inl
  loopless := by
    have no : ∀ u : V, (u,u) ∉ rawEdges := by decide
    intro u h
    exact h.elim (no u) (no u)

instance : DecidableRel H.Adj := fun _ _=>inferInstanceAs (Decidable (_ ∈ rawEdges ∨ _∈rawEdges))

theorem cubic : ∀ v,H.degree v=3 := by decide

def core : Finset V := univ\{0,3,2}
private theorem ports : ∀ u : V,H.Adj 2 u→u=5 ∨ u=8 ∨ u=9 := by decide

private instance (T : Finset V) : Decidable (KelmansStarter.IsTile H T) := by
  unfold KelmansStarter.IsTile
  infer_instance

private def anchorTest (S : Finset V) (a : V) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, KelmansStarter.IsTile H {a,u,v} ∧ KelmansStarter.IsTile H (S\{a,u,v})

private instance (S : Finset V) (a : V) : Decidable (anchorTest S a) := by
  unfold anchorTest
  infer_instance

set_option maxRecDepth 3500 in
set_option maxHeartbeats 3000000 in
theorem no_loan : ¬ ∃ u,H.Adj 2 u ∧ Closed H (core.erase u) := by
  rintro ⟨u,hu,fu⟩
  rcases ports u hu with rfl|rfl|rfl
  · have ht := (closed_six_iff_anchor (G:=H) (S:=core.erase 5) (a:=6) (by decide) (by decide)).mp fu
    exact (by decide : ¬ anchorTest (core.erase 5) 6) ht
  · have ht := (closed_six_iff_anchor (G:=H) (S:=core.erase 8) (a:=4) (by decide) (by decide)).mp fu
    exact (by decide : ¬ anchorTest (core.erase 8) 4) ht
  · have ht := (closed_six_iff_anchor (G:=H) (S:=core.erase 9) (a:=7) (by decide) (by decide)).mp fu
    exact (by decide : ¬ anchorTest (core.erase 9) 7) ht

private def pairTest (p q : V) : Prop :=
  ∃ a∈core, ∃ b∈core, ({p,a}:Finset V)⊆core ∧ ({q,b}:Finset V)⊆core ∧
    Disjoint ({p,a}:Finset V) {q,b} ∧ H.Adj p a ∧ H.Adj q b ∧
      KelmansStarter.IsTile H (core\({p,a}∪{q,b}))

private instance (p q : V) : Decidable (pairTest p q) := by
  unfold pairTest
  infer_instance

private theorem pairTest_iff (p q : V) : CenteredGeometry H core p q ↔ pairTest p q := by
  have size (a b : V) (ap : ({p,a}:Finset V)⊆core) (bq : ({q,b}:Finset V)⊆core)
      (d : Disjoint ({p,a}:Finset V) {q,b}) (e1 : H.Adj p a) (e2 : H.Adj q b) :
      (core\({p,a}∪{q,b})).card=3 := by
    have c : core.card=7 := by decide
    rw [card_sdiff (union_subset ap bq),card_union_of_disjoint d,c]
    simp [e1.ne,e2.ne]
  constructor
  · rintro ⟨a,b,ap,bq,d,e1,e2,closed⟩
    exact ⟨a,ap (by simp),b,bq (by simp),ap,bq,d,e1,e2,
      (closed_three_iff_tile (size a b ap bq d e1 e2)).mp closed⟩
  · rintro ⟨a,_,b,_,ap,bq,d,e1,e2,til⟩
    exact ⟨a,b,ap,bq,d,e1,e2,tile_closed til⟩

private theorem pairSymm {p q : V} : CenteredGeometry H core p q →
    CenteredGeometry H core q p := by
  rintro ⟨a,b,ap,bq,d,e1,e2,closed⟩
  rw [union_comm] at closed
  exact ⟨b,a,bq,ap,d.symm,e2,e1,closed⟩

set_option maxRecDepth 3500 in
set_option maxHeartbeats 2500000 in
theorem unique_centered_pair {p q : V} (hp : H.Adj 2 p) (hq : H.Adj 2 q) (ne : p≠q) :
    CenteredGeometry H core p q ↔ ({p,q}:Finset V) = {5,9} := by
  have no58 : ¬CenteredGeometry H core 5 8 := fun h=>
    (by decide : ¬pairTest 5 8) ((pairTest_iff _ _).mp h)
  have no89 : ¬CenteredGeometry H core 8 9 := fun h=>
    (by decide : ¬pairTest 8 9) ((pairTest_iff _ _).mp h)
  have yes59 : CenteredGeometry H core 5 9 := (pairTest_iff _ _).mpr (by decide)
  rcases ports _ hp with h|h|h <;> rcases ports _ hq with k|k|k <;> rw [h,k] at ne ⊢
  · exact (ne rfl).elim
  · exact iff_of_false no58 (by decide)
  · exact iff_of_true yes59 (by decide)
  · exact iff_of_false (fun h=>no58 (pairSymm h)) (by decide)
  · exact (ne rfl).elim
  · exact iff_of_false no89 (by decide)
  · exact iff_of_true (pairSymm yes59) (by decide)
  · exact iff_of_false (fun h=>no89 (pairSymm h)) (by decide)
  · exact (ne rfl).elim

#print axioms no_loan
#print axioms unique_centered_pair
end KelmansCactus.AtomicBridge.Z5JunctionGap
