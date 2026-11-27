import C9MaskCore133

namespace Graffiti133C9
set_option maxRecDepth 150000
set_option maxHeartbeats 0
theorem pairChunk0 : (List.range' 0 8).all pairRange = true := by decide
theorem pairChunk1 : (List.range' 8 8).all pairRange = true := by decide
theorem pairChunk2 : (List.range' 16 8).all pairRange = true := by decide
theorem pairChunk3 : (List.range' 24 8).all pairRange = true := by decide
theorem pairChunk4 : (List.range' 32 8).all pairRange = true := by decide
theorem pairChunk5 : (List.range' 40 8).all pairRange = true := by decide
theorem pairChunk6 : (List.range' 48 8).all pairRange = true := by decide
theorem pairChunk7 : (List.range' 56 1).all pairRange = true := by decide

theorem pairTests (i j : Fin 57) (e : Bool) : pairTest i.val j.val e = true := by
  have hr : pairRange i.val = true := by
    by_cases h0 : i.val < 8
    · exact List.all_eq_true.mp pairChunk0 _ (List.mem_range'.mpr ⟨i.val-0,by omega,by simp⟩)
    by_cases h1 : i.val < 16
    · exact List.all_eq_true.mp pairChunk1 _ (List.mem_range'.mpr ⟨i.val-8,by omega,by simp; omega⟩)
    by_cases h2 : i.val < 24
    · exact List.all_eq_true.mp pairChunk2 _ (List.mem_range'.mpr ⟨i.val-16,by omega,by simp; omega⟩)
    by_cases h3 : i.val < 32
    · exact List.all_eq_true.mp pairChunk3 _ (List.mem_range'.mpr ⟨i.val-24,by omega,by simp; omega⟩)
    by_cases h4 : i.val < 40
    · exact List.all_eq_true.mp pairChunk4 _ (List.mem_range'.mpr ⟨i.val-32,by omega,by simp; omega⟩)
    by_cases h5 : i.val < 48
    · exact List.all_eq_true.mp pairChunk5 _ (List.mem_range'.mpr ⟨i.val-40,by omega,by simp; omega⟩)
    by_cases h6 : i.val < 56
    · exact List.all_eq_true.mp pairChunk6 _ (List.mem_range'.mpr ⟨i.val-48,by omega,by simp; omega⟩)
    exact List.all_eq_true.mp pairChunk7 _ (List.mem_range'.mpr ⟨i.val-56,by omega,by simp; omega⟩)
  have ht := List.all_eq_true.mp hr j.val (List.mem_range.mpr j.isLt)
  cases e
  · exact ((Iff.of_eq (Bool.and_eq_true _ _)).mp ht).1
  · exact ((Iff.of_eq (Bool.and_eq_true _ _)).mp ht).2
#print axioms pairTests
end Graffiti133C9
