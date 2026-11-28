import AdjacentCutFiveTopArithmetic189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent.AdjProfile

set_option maxHeartbeats 1000000 in
theorem compact_fifteen_singleton (y : AdjProfile) (sy : y.size=12)
    (ly : y.localOK) (cut : (⟨0,0,0,0,0,1⟩ : AdjProfile).cutOK y)
    (cx : (⟨0,0,0,0,0,1⟩ : AdjProfile).crossOK y)
    (_cy : y.crossOK ⟨0,0,0,0,0,1⟩) :
    (y.ea=3 ∧ y.eb=3 ∧ y.ec=1 ∧ y.oa=1 ∧ y.ob=1 ∧ y.oc=3) ∨
      (y.ea=3 ∧ y.eb=4 ∧ y.ec=0 ∧ y.oa=1 ∧ y.ob=1 ∧ y.oc=3) ∨
      (y.ea=3 ∧ y.eb=4 ∧ y.ec=0 ∧ y.oa=1 ∧ y.ob=2 ∧ y.oc=2) ∨
      (y.ea=4 ∧ y.eb=3 ∧ y.ec=0 ∧ y.oa=1 ∧ y.ob=1 ∧ y.oc=3) ∨
      (y.ea=4 ∧ y.eb=3 ∧ y.ec=0 ∧ y.oa=2 ∧ y.ob=1 ∧ y.oc=2) ∨
      (y.ea=4 ∧ y.eb=4 ∧ y.ec=0 ∧ y.oa=1 ∧ y.ob=1 ∧ y.oc=2) := by
  simp only [localOK,cutOK,crossOK,size] at sy ly cut cx ⊢
  have total := sy
  have cap₁ := cut.1
  have cap₂ := cut.2
  have cap₃ := cx.2.2.2.2.2 (by omega)
  have pos₁ := ly.2.2.2.2.1
  have pos₂ := ly.2.2.2.2.2.1
  clear sy ly cut cx
  have ec : y.ec≤1 := by omega
  have el : 2≤y.ea := by omega
  have er : 2≤y.eb := by omega
  have ol : 1≤y.oa := pos₁ (by omega)
  have or' : 1≤y.ob := pos₂ (by omega)
  clear pos₁ pos₂
  by_cases e0 : y.ec=0
  · by_cases left : y.oa=1
    · by_cases right : y.ob=1
      · by_cases le : y.ea=3
        · exact .inr (.inl ⟨le,by omega,e0,left,right,by omega⟩)
        · by_cases re : y.eb=3
          · exact .inr (.inr (.inr (.inl ⟨by omega,re,e0,left,right,by omega⟩)))
          · exact .inr (.inr (.inr (.inr (.inr ⟨by omega,by omega,e0,left,right,by omega⟩))))
      · exact .inr (.inr (.inl ⟨by omega,by omega,e0,left,by omega,by omega⟩))
    · exact .inr (.inr (.inr (.inr (.inl ⟨by omega,by omega,e0,by omega,by omega,by omega⟩))))
  · exact .inl ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

#print axioms compact_fifteen_singleton
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent.AdjProfile
