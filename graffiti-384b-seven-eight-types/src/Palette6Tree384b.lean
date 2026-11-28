import SmallPalette384b
import Mathlib.Tactic.FinCases
namespace Graffiti384b.SmallPalette
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 500000

private def shape6_0 : Shape := ⟨true,4,4,2⟩
private def t6_0 : Tree 6 := (.split 0 (.tip (.small 0)) (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 1)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.rank 0)))))))
private theorem t6_0OK : treeOK shape6_0 0 0 t6_0=true := by decide

private def shape6_1 : Shape := ⟨true,4,4,3⟩
private def t6_1 : Tree 6 := (.split 0 (.split 1 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.tip (.rank 48)))) (.split 1 (.split 3 (.tip (.small 0)) (.tip (.rank 40))) (.split 3 (.tip (.rank 36)) (.tip (.rank 32)))))
private theorem t6_1OK : treeOK shape6_1 0 0 t6_1=true := by decide

private def shape6_2 : Shape := ⟨true,5,4,3⟩
private def t6_3 : Tree 6 := (.split 1 (.tip (.small 1)) (.split 3 (.tip (.small 1)) (.split 5 (.tip (.rank 33)) (.tip (.cover 1 2 3 5)))))
private theorem t6_3OK : treeOK shape6_2 0 1 t6_3=true := by decide

private def t6_4 : Tree 6 := (.split 1 (.split 3 (.tip (.small 1)) (.split 4 (.tip (.rank 33)) (.tip (.cover 1 2 4 5)))) (.split 3 (.split 2 (.tip (.rank 33)) (.tip (.cover 1 3 4 5))) (.tip (.rank 32))))
private theorem t6_4OK : treeOK shape6_2 1 0 t6_4=true := by decide

private def t6_2 : Tree 6 := .split 0 t6_3 t6_4
private theorem t6_2OK : treeOK shape6_2 0 0 t6_2=true := by
  change (treeOK shape6_2 0 (0 ||| 2^0) t6_3 && treeOK shape6_2 (0 ||| 2^0) 0 t6_4)=true
  rw [Bool.and_eq_true]
  exact ⟨t6_3OK,t6_4OK⟩

def forms6 : Fin 3 → Shape := ![⟨true,4,4,2⟩,⟨true,4,4,3⟩,⟨true,5,4,3⟩]

theorem check6 (i : Fin 3) (b : Nat→Bool)
    (H : Ranked (n:=6) (adj (forms6 i) b)) :
    ∃ a b' c d : Fin 6, Effective (adj (forms6 i) b) (adj (forms6 i) b) a b' c d := by
  fin_cases i
  · exact (checked_tree shape6_0 b H t6_0 t6_0OK)
  · exact (checked_tree shape6_1 b H t6_1 t6_1OK)
  · exact (checked_tree shape6_2 b H t6_2 t6_2OK)
#print axioms check6
end Graffiti384b.SmallPalette
