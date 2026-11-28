import Base189
namespace Issue189
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
/-- Concatenate P,x,Q,y,A,D,B,Z in that order. -/
def fullPath : G.Walk 9 33 :=
  .cons (v := 10) (by decide) <| .cons (v := 11) (by decide) <| .cons (v := 12) (by decide) <| .cons (v := 13) (by decide) <| .cons (v := 14) (by decide) <| .cons (v := 21) (by decide) <| .cons (v := 15) (by decide) <| .cons (v := 16) (by decide) <| .cons (v := 17) (by decide) <| .cons (v := 18) (by decide) <| .cons (v := 19) (by decide) <| .cons (v := 20) (by decide) <| .cons (v := 22) (by decide) <| .cons (v := 0) (by decide) <| .cons (v := 1) (by decide) <| .cons (v := 2) (by decide) <| .cons (v := 6) (by decide) <| .cons (v := 7) (by decide) <| .cons (v := 8) (by decide) <| .cons (v := 3) (by decide) <| .cons (v := 4) (by decide) <| .cons (v := 5) (by decide) <| .cons (v := 23) (by decide) <| .cons (v := 24) (by decide) <| .cons (v := 25) (by decide) <| .cons (v := 26) (by decide) <| .cons (v := 27) (by decide) <| .cons (v := 28) (by decide) <| .cons (v := 29) (by decide) <| .cons (v := 30) (by decide) <| .cons (v := 31) (by decide) <| .cons (v := 32) (by decide) <| .cons (v := 33) (by decide) <| .nil
theorem fullPath_isPath : fullPath.IsPath := .mk' (by decide : fullPath.support.Nodup)
theorem fullPath_hamiltonian : ∀ v : V, fullPath.support.count v = 1 := by decide
#print axioms fullPath_hamiltonian
end Issue189
