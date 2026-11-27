import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset

namespace Kelmans
open Finset
variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edges between the two ends are allowed. The tiling uses a path,
not necessarily an induced path. -/
def HasCenter (T : Finset V) := ∃ c ∈ T, ∀ x ∈ T, x ≠ c → G.Adj c x

instance centerDec (T : Finset V) : Decidable (HasCenter G T) := by
  unfold HasCenter
  infer_instance

omit [DecidableRel G.Adj] in
theorem tile_iff_path (T : Finset V) (h : T.card = 3) :
    HasCenter G T ↔ ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.Adj a b ∧ G.Adj b c ∧ T = {a,b,c} := by
  constructor
  · rintro ⟨b,hb,mid⟩
    have he : (T.erase b).card = 2 := by rw [card_erase_of_mem hb,h]
    obtain ⟨a,c,ac,ec⟩ := card_eq_two.mp he
    have am : a ∈ T.erase b := ec.symm ▸ mem_insert_self _ _
    have cm : c ∈ T.erase b := ec.symm ▸ mem_insert_of_mem (mem_singleton_self _)
    obtain ⟨ab,at'⟩ := mem_erase.mp am
    obtain ⟨cb,ct⟩ := mem_erase.mp cm
    refine ⟨a,b,c,ab,ac,cb.symm,(mid a at' ab).symm,mid c ct cb,?_⟩
    rw [← insert_erase hb,ec,insert_comm]
  · rintro ⟨a,b,c,ab,ac,bc,e1,e2,rfl⟩
    refine ⟨b,by simp,?_⟩
    intro x hx diff
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact e1.symm
    · exact (diff rfl).elim
    · exact e2

/-- A factor consisting of exactly k vertex-disjoint 3-vertex paths. -/
inductive Tiles : ℕ → Finset V → Prop where
  | empty : Tiles 0 ∅
  | add {k S T} (sub : T ⊆ S) (three : T.card = 3) (center : HasCenter G T)
      (rest : Tiles k (S \ T)) : Tiles (k+1) S

def solve : ℕ → Finset V → Bool
  | 0, S => decide (S = ∅)
  | k+1, S => decide (∃ T ∈ S.powersetCard 3, HasCenter G T ∧ solve k (S \ T) = true)

theorem solve_iff (k : ℕ) (S : Finset V) : solve G k S = true ↔ Tiles G k S := by
  induction k generalizing S with
  | zero =>
    simp only [solve,decide_eq_true_eq]
    exact ⟨fun h => h.symm ▸ Tiles.empty, fun h => by cases h; rfl⟩
  | succ k ih =>
    simp only [solve,decide_eq_true_eq,mem_powersetCard,ih]
    constructor
    · rintro ⟨T,⟨hs,hc⟩,hmid,rest⟩
      exact Tiles.add hs hc hmid rest
    · intro h
      cases h with
      | add sub three center rest =>
          exact ⟨_,⟨sub,three⟩,center,rest⟩

#print axioms tile_iff_path
#print axioms solve_iff
end Kelmans
