import AdjacentCutFiveTopArithmetic189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent.AdjProfile

def Singleton14Rows (a b c p q r : Nat) : Prop :=
     (a=2 ∧ b=2 ∧ c=2 ∧ p=1 ∧ q=1 ∧ r=3)
  ∨ (a=2 ∧ b=3 ∧ c=1 ∧ p=1 ∧ q=1 ∧ r=3)
  ∨ (a=2 ∧ b=3 ∧ c=1 ∧ p=1 ∧ q=2 ∧ r=2)
  ∨ (a=2 ∧ b=4 ∧ c=0 ∧ p=1 ∧ q=1 ∧ r=3)
  ∨ (a=2 ∧ b=4 ∧ c=0 ∧ p=1 ∧ q=2 ∧ r=2)
  ∨ (a=2 ∧ b=4 ∧ c=0 ∧ p=1 ∧ q=3 ∧ r=1)
  ∨ (a=3 ∧ b=3 ∧ c=0 ∧ p=1 ∧ q=1 ∧ r=3)
  ∨ (a=3 ∧ b=3 ∧ c=0 ∧ p=1 ∧ q=2 ∧ r=2)
  ∨ (a=3 ∧ b=3 ∧ c=0 ∧ p=2 ∧ q=2 ∧ r=1)
  ∨ (a=3 ∧ b=3 ∧ c=1 ∧ p=1 ∧ q=1 ∧ r=2)
  ∨ (a=3 ∧ b=4 ∧ c=0 ∧ p=1 ∧ q=1 ∧ r=2)
  ∨ (a=3 ∧ b=4 ∧ c=0 ∧ p=1 ∧ q=2 ∧ r=1)
  ∨ (a=4 ∧ b=4 ∧ c=0 ∧ p=1 ∧ q=1 ∧ r=1)

private theorem singleton14_sorted {a b c p q r : Nat}
    (sum : a+b+c+p+q+r=11) (odd : p+q+r≤5)
    (lc : a+c+q≤5) (rc : b+c+p≤5)
    (ah : a>0 → p>0) (bh : b>0 → q>0)
    (ord : a≤b) (tie : a=b → p≤q) :
    Singleton14Rows a b c p q r := by
  have a2 : 2≤a := by omega
  have b2 : 2≤b := by omega
  have p1 := ah (by omega)
  have q1 := bh (by omega)
  have aCase : a=2 ∨ a=3 ∨ a=4 := by omega
  have bCase : b=2 ∨ b=3 ∨ b=4 := by omega
  rcases aCase with h|h|h <;> rcases bCase with k|k|k <;>
    subst a <;> subst b <;> simp [Singleton14Rows] <;> omega

set_option maxHeartbeats 1000000 in
theorem compact_fourteen_singleton (y : AdjProfile) (sy : y.size=11)
    (ly : y.localOK) (cut : (⟨0,0,0,0,0,1⟩ : AdjProfile).cutOK y)
    (cx : (⟨0,0,0,0,0,1⟩ : AdjProfile).crossOK y) :
    Singleton14Rows y.ea y.eb y.ec y.oa y.ob y.oc ∨
    Singleton14Rows y.eb y.ea y.ec y.ob y.oa y.oc := by
  have sum : y.ea+y.eb+y.ec+y.oa+y.ob+y.oc=11 := sy
  have aq : y.ea+y.ec+y.ob≤5 := by simpa [cutOK] using cut.1
  have bp : y.eb+y.ec+y.oa≤5 := by simpa [cutOK] using cut.2
  have p : y.ea>0 → y.oa>0 := ly.2.2.2.2.1
  have q : y.eb>0 → y.ob>0 := ly.2.2.2.2.2.1
  have o : y.oa+y.ob+y.oc≤5 := cx.2.2.2.2.2 (by decide)
  by_cases f : y.ea≤y.eb ∧ (y.ea=y.eb → y.oa≤y.ob)
  · exact .inl (singleton14_sorted sum o aq bp p q f.1 f.2)
  apply Or.inr
  exact singleton14_sorted (by omega) (by omega) bp aq q p (by omega) (by omega)

#print axioms compact_fourteen_singleton
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent.AdjProfile
