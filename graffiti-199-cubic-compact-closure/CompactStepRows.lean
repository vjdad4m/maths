import CompactExtensionBase

namespace Graffiti199Depleted.CompactOmission

private def stepCert (k : ℕ) (m : ℕ) (b : Bool) : Certificate 11 :=
  let certs : List ((ℕ × Bool) × (Certificate 11)) := match k with
    | 0 => [((0,false),.tree ![1,2,8,3,10,4]),
      ((0,true),.tree ![1,2,8,3,10,4]),
      ((54,false),.tree ![0,8,10,2,3,7]),
      ((54,true),.tree ![0,8,10,2,3,7]),
      ((85,false),.tree ![1,2,9,3,10,5]),
      ((85,true),.route [2,1,7,3,4,5,0,6] false),
      ((87,true),.route [2,1,7,3,4,5,0,6] false),
      ((117,true),.route [2,1,7,3,4,5,0,6] false),
      ((119,true),.route [2,1,7,3,4,5,0,6] false),
      ((87,false),.tree ![0,9,10,2,3,7]),
      ((117,false),.tree ![0,9,10,2,3,7]),
      ((119,false),.tree ![0,9,10,2,3,7]),
      ((99,false),.tree ![1,2,9,10,3,4])]
    | 1 => [((0,false),.tree ![1,2,8,3,10,4]),
      ((0,true),.tree ![1,2,8,3,10,4]),
      ((22,false),.tree ![0,8,10,2,3,7]),
      ((22,true),.tree ![0,8,10,2,3,7]),
      ((54,false),.tree ![0,8,10,2,3,7]),
      ((54,true),.tree ![0,8,10,2,3,7]),
      ((85,true),.route [2,1,7,3,4,5,0,6] false),
      ((87,true),.route [2,1,7,3,4,5,0,6] false),
      ((117,true),.route [2,1,7,3,4,5,0,6] false),
      ((119,true),.route [2,1,7,3,4,5,0,6] false),
      ((87,false),.tree ![0,9,10,2,3,7]),
      ((117,false),.tree ![0,9,10,2,3,7]),
      ((119,false),.tree ![0,9,10,2,3,7]),
      ((99,false),.tree ![1,2,9,10,3,4]),
      ((85,false),.tree ![1,9,5,4,3,10])]
    | 2 => [((52,false),.tree ![0,8,10,2,3,7]),
      ((52,true),.tree ![0,8,10,2,3,7]),
      ((54,false),.tree ![0,8,10,2,3,7]),
      ((54,true),.tree ![0,8,10,2,3,7]),
      ((85,false),.tree ![1,2,9,3,10,5]),
      ((87,false),.tree ![0,9,10,2,3,7]),
      ((117,false),.tree ![0,9,10,2,3,7]),
      ((119,false),.tree ![0,9,10,2,3,7]),
      ((0,false),.tree ![1,2,8,3,5,10]),
      ((0,true),.tree ![1,2,8,3,5,10]),
      ((85,true),.route [2,1,4,3,7,5,0,6] false),
      ((87,true),.route [2,1,4,3,7,5,0,6] false),
      ((117,true),.route [2,1,4,3,7,5,0,6] false),
      ((119,true),.route [2,1,4,3,7,5,0,6] false),
      ((99,false),.tree ![2,3,4,5,9,10])]
    | 3 => [((20,false),.tree ![0,8,10,2,3,7]),
      ((20,true),.tree ![0,8,10,2,3,7]),
      ((22,false),.tree ![0,8,10,2,3,7]),
      ((22,true),.tree ![0,8,10,2,3,7]),
      ((52,false),.tree ![0,8,10,2,3,7]),
      ((52,true),.tree ![0,8,10,2,3,7]),
      ((54,false),.tree ![0,8,10,2,3,7]),
      ((54,true),.tree ![0,8,10,2,3,7]),
      ((85,false),.tree ![0,9,10,2,3,7]),
      ((87,false),.tree ![0,9,10,2,3,7]),
      ((117,false),.tree ![0,9,10,2,3,7]),
      ((119,false),.tree ![0,9,10,2,3,7]),
      ((85,true),.route [2,1,4,3,7,5,0,6] false),
      ((87,true),.route [2,1,4,3,7,5,0,6] false),
      ((117,true),.route [2,1,4,3,7,5,0,6] false),
      ((119,true),.route [2,1,4,3,7,5,0,6] false),
      ((0,false),.tree ![1,2,4,7,8,10]),
      ((0,true),.tree ![1,2,4,7,8,10]),
      ((38,false),.tree ![0,8,10,2,3,4]),
      ((38,true),.tree ![0,8,10,2,3,4]),
      ((50,false),.tree ![0,8,10,4,3,2]),
      ((50,true),.tree ![0,8,10,4,3,2]),
      ((99,false),.tree ![1,2,4,7,9,10])]
    | 4 => [((108,true),.route [2,1,7,3,4,5,0,6] false),
      ((109,true),.route [2,1,7,3,4,5,0,6] false),
      ((0,false),.tree ![1,2,3,4,8,10]),
      ((0,true),.tree ![1,2,3,4,8,10]),
      ((56,false),.tree ![0,1,8,2,10,4]),
      ((56,true),.tree ![0,1,8,2,10,4]),
      ((105,false),.tree ![1,2,3,4,9,10]),
      ((108,false),.tree ![0,1,9,2,7,10]),
      ((109,false),.tree ![1,7,3,4,9,10])]
    | 5 => [((0,false),.tree ![1,2,4,8,5,10]),
      ((0,true),.tree ![1,2,4,8,5,10]),
      ((14,false),.tree ![2,10,8,6,5,4]),
      ((14,true),.tree ![2,10,8,6,5,4]),
      ((27,false),.tree ![1,2,7,9,10,5]),
      ((91,false),.tree ![1,2,7,9,10,5]),
      ((27,true),.route [4,1,2,3,7,5,6,0] false),
      ((91,true),.route [4,1,2,3,7,5,6,0] false),
      ((75,false),.tree ![1,2,4,9,10,5])]
    | _ => []
  (certs.lookup (m,b)).getD .pass

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem stepCoverage (k : Fin 6) :
    ∀ (i : Fin (profiles k).length) (b : Bool),
      let m := (profiles k).get i
      (stepCert k.val m.val b).Valid (stepEdge k m b) (StepRoute (stepEdge k m b))
        (m = boundary k ∧ b = true) := by
  fin_cases k <;> decide

theorem next_extension (k : Fin 6) (m : Profile) (b : Bool) (hm : m ∈ profiles k) :
    (∃ T, SixTree (stepEdge k m b) T) ∨ (∃ P front, StepRoute (stepEdge k m b) P front) ∨
      (m = boundary k ∧ b = true) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hm
  have valid := stepCoverage k i b
  dsimp only at valid
  cases hC : stepCert k.val ((profiles k).get i).val b with
  | tree T =>
    rw [hC] at valid
    exact Or.inl ⟨T,valid⟩
  | route P front =>
    rw [hC] at valid
    exact Or.inr (Or.inl ⟨P,front,valid⟩)
  | pass =>
    rw [hC] at valid
    exact Or.inr (Or.inr valid)

#print axioms next_extension

end Graffiti199Depleted.CompactOmission
