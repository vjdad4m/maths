import T11TenMotif384b
import Mathlib.Tactic.FinCases
import Init.Data.BitVec.Lemmas

namespace Graffiti384b.T11TenNormalize
open Finset
set_option maxHeartbeats 3000000

def maskSet (m : Nat) : Finset Label := Finset.univ.filter fun i => m.testBit i.val

@[simp] theorem mem_maskSet (m : Nat) (i : Label) : i∈maskSet m ↔ m.testBit i.val = true := by
  simp [maskSet]

private def bits (A : Finset Label) : List Bool :=
  [decide (0∈A),decide (1∈A),decide (2∈A),decide (3∈A),decide (4∈A),
    decide (5∈A),decide (6∈A),decide (7∈A),decide (8∈A),decide (9∈A)]

def encode (A : Finset Label) : Fin 1024 :=
  let z := BitVec.ofBoolListLE (bits A)
  ⟨z.toNat,by simpa only [bits,List.length_cons,List.length_nil] using z.isLt⟩

theorem maskSet_encode (A : Finset Label) : maskSet (encode A).val = A := by
  ext i
  rw [mem_maskSet]
  have eq : (encode A).val.testBit i.val = decide (i∈A) := by
    change (BitVec.ofBoolListLE (bits A)).getLsbD i.val = _
    rw [BitVec.getLsb_ofBoolListLE]
    fin_cases i <;> rfl
  simp [eq]

end Graffiti384b.T11TenNormalize
