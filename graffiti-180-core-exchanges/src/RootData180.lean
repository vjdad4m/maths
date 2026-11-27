import Example180
import AllTips180
set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180
namespace Case12
theorem old_root_data : J.Connected ∧ (∀ i,J.dist i 0=G.dist i 0) ∧ J.dist 7 0=J.dist 8 0 ∧
    parity J 0 false=P ∧ (∃ a b,J.Adj 0 a ∧ J.Adj 0 b ∧ a≠b) ∧ Indep J A := by
  have old : J.Connected ∧ ∀ i,J.dist i 0=d i 0 := by
    apply layers J 0 (fun i => d i 0) (by decide)
    · intro i j; exact (show ∀ a b,J.Adj a b → d a 0≤d b 0+1 by decide) i j
    · decide
  refine ⟨old.1,fun i => (old.2 i).trans ((dist_data 0).2 i).symm,?_,?_,⟨6,9,by decide,by decide,by decide⟩,?_⟩
  · rw [old.2,old.2]; decide
  · ext i; rw [mem_parity,old.2]; exact (show ∀ j : V,d j 0%2=false.toNat ↔ j∈P by decide) i
  · unfold Indep; decide
#print axioms old_root_data
end Case12
namespace Case14
theorem old_root_data : J.Connected ∧ (∀ i,J.dist i 11=G.dist i 11) ∧ J.dist 3 11=J.dist 4 11 ∧
    parity J 11 true=P ∧ (∃ a b,J.Adj 11 a ∧ J.Adj 11 b ∧ a≠b) ∧ Indep J A := by
  have old : J.Connected ∧ ∀ i,J.dist i 11=d i 11 := by
    apply layers J 11 (fun i => d i 11) (by decide)
    · intro i j; exact (show ∀ a b,J.Adj a b → d a 11≤d b 11+1 by decide) i j
    · decide
  refine ⟨old.1,fun i => (old.2 i).trans ((dist_data 11).2 i).symm,?_,?_,⟨9,10,by decide,by decide,by decide⟩,?_⟩
  · rw [old.2,old.2]; decide
  · ext i; rw [mem_parity,old.2]; exact (show ∀ j : V,d j 11%2=true.toNat ↔ j∈P by decide) i
  · unfold Indep; decide
#print axioms old_root_data
end Case14
end Minimal180
