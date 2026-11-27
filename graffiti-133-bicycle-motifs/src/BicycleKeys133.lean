import BicycleCheck133

namespace Graffiti133Bicycle

def thetaKeys : List (Nat × Nat × Nat) :=
  [(1,4,4),(1,4,5),(2,3,3),(2,3,4),(2,3,5),(2,3,6),
    (2,4,4),(2,4,5),(3,3,3),(3,3,4),(3,3,5),(3,3,6),
    (3,4,4),(3,4,5),(4,4,4),(4,4,5)]
def dumbKeys : List (Nat × Nat × Nat) := [(5,5,0),(5,5,1),(5,6,0)]

private theorem theta_fin : ∀ a b c : Fin 7,
    1≤a.val → a.val≤b.val → b.val≤c.val → 5≤a.val+b.val → b.val+c.val≤9 →
    (a.val,b.val,c.val)∈thetaKeys := by decide

theorem theta_keys_complete (a b c : Nat)
    (ha : 1≤a) (ab : a≤b) (bc : b≤c) (low : 5≤a+b) (high : b+c≤9) :
    (a,b,c)∈thetaKeys := by
  have hb : 3≤b := by omega
  exact theta_fin ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨c,by omega⟩ ha ab bc low high

private theorem dumb_fin : ∀ a b : Fin 7, ∀ d : Fin 2,
    5≤a.val → a.val≤b.val → a.val+b.val+d.val≤11 →
    (a.val,b.val,d.val)∈dumbKeys := by decide

theorem dumb_keys_complete (a b d : Nat) (ha : 5≤a) (ab : a≤b) (high : a+b+d≤11) :
    (a,b,d)∈dumbKeys :=
  dumb_fin ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨d,by omega⟩ ha ab high

theorem key_counts : thetaKeys.Nodup ∧ thetaKeys.length=16 ∧ dumbKeys.Nodup ∧ dumbKeys.length=3 := by decide

#print axioms theta_keys_complete
#print axioms dumb_keys_complete
end Graffiti133Bicycle
