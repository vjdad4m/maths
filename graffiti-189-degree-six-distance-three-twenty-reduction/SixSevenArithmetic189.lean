import SixElevenArithmetic189
namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
set_option maxHeartbeats 30000000

/-- A linear obstruction for a seven-plus-eleven shore profile. -/
theorem impossible_seven_eleven_counts
    (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ)
    (orderSmall : x0+x1+x2+x3+x4+x5+x6+x7=7)
    (orderBig : y0+y1+y2+y3+y4+y5+y6+y7=11)
    (scount0 : a0≤x0)
    (scount1 : a1≤x1)
    (scount2 : a2≤x2)
    (scount3 : a3≤x3)
    (scount4 : a4≤x4)
    (scount5 : a5≤x5)
    (scount6 : a6≤x6)
    (scount7 : a7≤x7)
    (s0 : 1≤x0+x1 ∧ x0+x1≤5)
    (s1 : 1≤x2+x3 ∧ x2+x3≤5)
    (shigh0 : 0<a0 → 6≤x0+x1+x4+x6)
    (shigh1 : 0<a1 → 6≤x0+x1+x3+x4+x6)
    (shigh2 : 0<a2 → 6≤x2+x3+x5+x6)
    (shigh3 : 0<a3 → 6≤x1+x2+x3+x5+x6)
    (slow7 : 0<x7 → 3≤x4+x5+x6+x7)
    (tcount0 : b0≤y0)
    (tcount1 : b1≤y1)
    (tcount2 : b2≤y2)
    (tcount3 : b3≤y3)
    (tcount4 : b4≤y4)
    (tcount5 : b5≤y5)
    (tcount6 : b6≤y6)
    (tcount7 : b7≤y7)
    (t0 : 1≤y0+y1 ∧ y0+y1≤5)
    (t1 : 1≤y2+y3 ∧ y2+y3≤5)
    (thigh0 : 0<b0 → 6≤y0+y1+y4+y6)
    (thigh2 : 0<b2 → 6≤y2+y3+y5+y6)
    (thigh4 : 0<b4 → 7≤y0+y1+y4+y5+y6+y7)
    (thigh5 : 0<b5 → 7≤y2+y3+y4+y5+y6+y7)
    (oneLow : 17≤a0+a1+a2+a3+a4+a5+a6+a7+b0+b1+b2+b3+b4+b5+b6+b7)
    (smallDark : a4+a5+a7=0)
    (bigDeep : b7=0)
    (termA : 6≤x0+x1+y0+y1)
    (termB : 6≤x2+x3+y2+y3)
    (termEvenA : x3+x4+x6+y3+y4+y6≤6)
    (termEvenB : x1+x5+x6+y1+y5+y6≤6)
    (cost0 : 0<b0 → x0+x1+x2+x5+x7+b2+b3+b5+b7≤6)
    (cost1 : 0<b1 → x0+x1+1+x5+x7+b2+b5+b7≤6)
    (cost2 : 0<b2 → x2+x3+x0+x4+x7+b0+b1+b4+b7≤6)
    (cost3 : 0<b3 → x2+x3+1+x4+x7+b0+b4+b7≤6)
    (cost6 : 0<b6 → 2+a6≤6)
    : False := by
  have leftCases : x0+x1=1 ∨ x0+x1=2 ∨ x0+x1=3 ∨ x0+x1=4 ∨ x0+x1=5 := by omega
  have rightCases : x2+x3=1 ∨ x2+x3=2 ∨ x2+x3=3 ∨ x2+x3=4 ∨ x2+x3=5 := by omega
  rcases leftCases with lp|lp|lp|lp|lp <;> rcases rightCases with rp|rp|rp|rp|rp
  · clear bigDeep cost0 cost1 cost3 s0 s1 scount4 scount5 scount7 shigh0 shigh1 shigh2 shigh3 slow7 t0 tcount4 tcount5 thigh0
    by_cases pos2 : 0<b2
    · clear tcount0 tcount1 tcount7 termB termEvenA thigh4
      by_cases pos3 : 0<b5
      · have usethigh5 := thigh5 pos3
        clear cost2 cost6 oneLow orderSmall scount0 scount1 scount2 scount3 scount6 smallDark t1 tcount2 tcount3 tcount6 termEvenB thigh2 thigh5
        omega
      · clear orderBig termA thigh5
        by_cases pos4 : 0<b6
        · have usecost2 := cost2 pos2
          have usecost6 := cost6 pos4
          clear cost2 cost6 scount6 thigh2
          omega
        · have usethigh2 := thigh2 pos2
          have usecost2 := cost2 pos2
          clear cost2 cost6 orderSmall tcount6 thigh2
          omega
    · clear cost2 cost6 orderSmall t1 tcount2 termEvenB thigh2
      by_cases pos3 : 0<b4
      · have usethigh4 := thigh4 pos3
        clear oneLow scount0 scount1 scount2 scount3 scount6 smallDark tcount0 tcount1 tcount3 tcount6 tcount7 termA termEvenA thigh4 thigh5
        omega
      · clear thigh4
        by_cases pos4 : 0<b5
        · have usethigh5 := thigh5 pos4
          clear oneLow scount0 scount1 scount2 scount3 scount6 smallDark tcount0 tcount1 tcount3 tcount6 tcount7 termB termEvenA thigh5
          omega
        · clear termA thigh5
          omega
  · clear cost1 cost3 cost6 s0 s1 scount0 scount4 scount5 scount7 shigh1 shigh2 shigh3 slow7 t0 tcount5 tcount7 thigh0 thigh2 thigh4
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost0 cost2 oneLow orderBig scount1 scount2 scount3 scount6 shigh0 smallDark t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount6 termA termB termEvenA termEvenB thigh5
      omega
    · clear orderSmall shigh0
      by_cases pos3 : 0<b5
      · have usethigh5 := thigh5 pos3
        clear bigDeep cost0 cost2 oneLow scount1 scount2 scount3 scount6 smallDark t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount6 termB termEvenA termEvenB thigh5
        omega
      · clear termA thigh5
        by_cases pos4 : 0<b0
        · clear t1 tcount2 termEvenB
          by_cases pos5 : 0<b2
          · have usecost0 := cost0 pos4
            have usecost2 := cost2 pos5
            clear bigDeep cost0 cost2 orderBig tcount0 tcount1 tcount3 tcount4 termB
            omega
          · clear cost0 cost2
            omega
        · clear cost0 cost2 tcount0 termB
          omega
  · clear cost0 cost1 cost3 cost6 s0 s1 scount4 scount5 scount7 shigh0 shigh1 shigh2 shigh3 slow7 t1 tcount5 tcount7 termB termEvenB thigh0 thigh2 thigh4
    by_cases pos2 : 0<b5
    · have usethigh5 := thigh5 pos2
      clear bigDeep cost2 oneLow orderSmall scount0 scount1 scount2 scount3 scount6 smallDark t0 tcount0 tcount1 tcount2 tcount3 tcount4 tcount6 termEvenA thigh5
      omega
    · clear thigh5
      by_cases pos3 : 0<b2
      · have usecost2 := cost2 pos3
        clear bigDeep cost2 t0 tcount0 tcount1 tcount4 termEvenA
        omega
      · clear cost2 orderBig orderSmall tcount2 termA
        omega
  · clear cost0 cost1 cost6 s0 s1 scount0 shigh1 shigh2 shigh3 slow7 smallDark t0 tcount7 termEvenA thigh0 thigh2 thigh4 thigh5
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost2 cost3 oneLow orderBig scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termA termB termEvenB
      omega
    · clear shigh0
      by_cases pos3 : 0<b2
      · have usecost2 := cost2 pos3
        clear bigDeep cost2 cost3 t1 tcount0 tcount1 tcount4 termB termEvenB
        omega
      · clear cost2 tcount2 termA
        by_cases pos4 : 0<b3
        · have usecost3 := cost3 pos4
          clear bigDeep cost3 orderBig orderSmall tcount0 tcount4 termB
          omega
        · clear cost3 t1 tcount3 termEvenB
          omega
  · clear cost0 cost1 cost3 cost6 s0 s1 scount0 scount4 scount5 scount7 shigh2 shigh3 slow7 tcount5 tcount7 termB termEvenB thigh0 thigh2 thigh4
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost2 oneLow orderBig scount1 scount2 scount3 scount6 shigh0 shigh1 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount6 termA termEvenA thigh5
      omega
    · clear shigh0
      by_cases pos3 : 0<a1
      · by_cases pos4 : 0<b5
        · have usethigh5 := thigh5 pos4
          clear bigDeep cost2 oneLow orderSmall scount1 scount2 scount3 scount6 shigh1 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount6 termEvenA thigh5
          omega
        · clear orderBig termA thigh5
          by_cases pos5 : 0<b2
          · have useshigh1 := shigh1 pos3
            have usecost2 := cost2 pos5
            clear bigDeep cost2 shigh1 t0 tcount0 tcount1 tcount4
            omega
          · have useshigh1 := shigh1 pos3
            clear cost2 shigh1 t1 tcount2
            omega
      · clear scount1 shigh1 t1
        by_cases pos4 : 0<b5
        · have usethigh5 := thigh5 pos4
          clear bigDeep cost2 oneLow orderSmall scount2 scount3 scount6 smallDark t0 tcount0 tcount1 tcount2 tcount3 tcount4 tcount6 termEvenA thigh5
          omega
        · clear thigh5
          by_cases pos5 : 0<b2
          · have usecost2 := cost2 pos5
            clear bigDeep cost2 t0 tcount0 tcount1 tcount4 termEvenA
            omega
          · clear cost2 orderBig orderSmall tcount2 termA
            omega
  · clear cost1 cost3 cost6 s0 s1 scount2 scount4 scount5 scount7 shigh0 shigh1 shigh3 slow7 t0 tcount4 tcount7 termA thigh0 thigh2 thigh5
    by_cases pos2 : 0<a2
    · have useshigh2 := shigh2 pos2
      clear bigDeep cost0 cost2 oneLow orderBig scount0 scount1 scount3 scount6 shigh2 smallDark t1 tcount0 tcount1 tcount2 tcount3 tcount5 tcount6 termB termEvenA termEvenB thigh4
      omega
    · clear orderSmall shigh2
      by_cases pos3 : 0<b4
      · have usethigh4 := thigh4 pos3
        clear bigDeep cost0 cost2 oneLow scount0 scount1 scount3 scount6 smallDark t1 tcount0 tcount1 tcount2 tcount3 tcount5 tcount6 termEvenA termEvenB thigh4
        omega
      · clear thigh4
        by_cases pos4 : 0<b0
        · clear t1 tcount2
          by_cases pos5 : 0<b2
          · have usecost0 := cost0 pos4
            have usecost2 := cost2 pos5
            clear bigDeep cost0 cost2 orderBig tcount0 tcount1 tcount3 tcount5 termB termEvenA
            omega
          · clear cost0 cost2 termEvenB
            omega
        · clear cost0 cost2 orderBig tcount0 termB termEvenA
          omega
  · clear cost1 cost3 cost6 s0 s1 scount0 scount2 scount4 scount5 scount7 shigh1 shigh3 slow7 t0 t1 tcount7 thigh0 thigh2 thigh4 thigh5
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost0 cost2 oneLow orderBig scount1 scount3 scount6 shigh0 shigh2 smallDark tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termA termB termEvenA termEvenB
      omega
    · clear shigh0
      by_cases pos3 : 0<a2
      · have useshigh2 := shigh2 pos3
        clear bigDeep cost0 cost2 oneLow orderBig scount1 scount3 scount6 shigh2 smallDark tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termA termB termEvenA termEvenB
        omega
      · clear orderSmall shigh2
        by_cases pos4 : 0<b0
        · clear tcount2 termA termEvenB
          by_cases pos5 : 0<b2
          · have usecost0 := cost0 pos4
            have usecost2 := cost2 pos5
            clear bigDeep cost0 cost2 orderBig tcount0 tcount1 tcount3 tcount4 tcount5 termB
            omega
          · clear cost0 cost2
            omega
        · clear cost0 cost2 tcount0 termB termEvenA
          omega
  · clear cost1 cost6 s0 s1 scount0 shigh1 shigh2 shigh3 slow7 smallDark t0 tcount7 termEvenA thigh0 thigh2 thigh4 thigh5
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost0 cost2 cost3 oneLow orderBig scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termA termB termEvenB
      omega
    · clear shigh0
      by_cases pos3 : 0<b0
      · clear t1 tcount2 tcount3 termA
        by_cases pos4 : 0<b2
        · have usecost0 := cost0 pos3
          have usecost2 := cost2 pos4
          clear bigDeep cost0 cost2 cost3 orderBig orderSmall tcount0 tcount1 tcount4 tcount5 termB
          omega
        · clear cost2
          by_cases pos5 : 0<b3
          · have usecost0 := cost0 pos3
            have usecost3 := cost3 pos5
            clear bigDeep cost0 cost3 orderBig orderSmall tcount0 tcount4 tcount5 termB
            omega
          · clear cost0 cost3 termEvenB
            omega
      · clear cost0 tcount0
        by_cases pos4 : 0<b2
        · have usecost2 := cost2 pos4
          clear cost2 cost3 t1 termB
          omega
        · clear cost2 tcount2 termA
          by_cases pos5 : 0<b3
          · have usecost3 := cost3 pos5
            clear bigDeep cost3 orderBig orderSmall tcount4 termB
            omega
          · clear cost3 t1 tcount3 termEvenB
            omega
  · clear cost0 cost6 s0 s1 scount2 shigh0 shigh1 shigh3 slow7 smallDark t1 tcount7 termEvenB thigh0 thigh2 thigh4 thigh5
    by_cases pos2 : 0<a2
    · have useshigh2 := shigh2 pos2
      clear bigDeep cost1 cost2 cost3 oneLow orderBig scount0 scount1 scount3 scount4 scount5 scount6 scount7 shigh2 t0 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termA termB termEvenA
      omega
    · clear shigh2
      by_cases pos3 : 0<b1
      · have usecost1 := cost1 pos3
        clear bigDeep cost1 cost2 cost3 orderBig orderSmall tcount2 tcount5 termA termB
        omega
      · clear cost1 t0 tcount1 termEvenA
        by_cases pos4 : 0<b2
        · have usecost2 := cost2 pos4
          clear bigDeep cost2 cost3 tcount0 tcount4 termB
          omega
        · clear cost2 tcount2
          by_cases pos5 : 0<b3
          · have usecost3 := cost3 pos5
            clear bigDeep cost3 tcount0 tcount4 termB
            omega
          · clear cost3 tcount3 termA
            omega
  · clear cost0 cost1 cost3 cost6 s0 s1 scount0 scount2 shigh1 shigh3 slow7 smallDark t1 tcount7 termB thigh0 thigh2 thigh4
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost2 oneLow orderBig scount1 scount3 scount4 scount5 scount6 scount7 shigh0 shigh2 t0 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termA termEvenA termEvenB thigh5
      omega
    · clear shigh0
      by_cases pos3 : 0<a2
      · have useshigh2 := shigh2 pos3
        clear bigDeep cost2 oneLow orderBig scount1 scount3 scount4 scount5 scount6 scount7 shigh2 t0 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termA termEvenA termEvenB thigh5
        omega
      · clear shigh2
        by_cases pos4 : 0<b5
        · clear t0
          by_cases pos5 : 0<b2
          · have usecost2 := cost2 pos5
            clear bigDeep cost2 tcount0 tcount1 tcount4 termEvenA termEvenB thigh5
            omega
          · have usethigh5 := thigh5 pos4
            clear cost2 tcount2 termA thigh5
            omega
        · clear tcount5 termEvenB thigh5
          by_cases pos5 : 0<b2
          · have usecost2 := cost2 pos5
            clear bigDeep cost2 t0 tcount0 tcount1 tcount4 termEvenA
            omega
          · clear cost2 orderBig tcount2 termA
            omega
  · clear cost1 cost2 cost3 cost6 s0 s1 scount4 scount5 scount7 shigh0 shigh1 shigh2 shigh3 slow7 t0 tcount4 tcount7 termA termEvenA thigh0 thigh2 thigh5
    by_cases pos2 : 0<b4
    · have usethigh4 := thigh4 pos2
      clear bigDeep cost0 oneLow orderSmall scount0 scount1 scount2 scount3 scount6 smallDark t1 tcount0 tcount1 tcount2 tcount3 tcount5 tcount6 termEvenB thigh4
      omega
    · clear thigh4
      by_cases pos3 : 0<b0
      · have usecost0 := cost0 pos3
        clear bigDeep cost0 t1 tcount2 tcount3 tcount5 termEvenB
        omega
      · clear cost0 orderBig orderSmall tcount0 termB
        omega
  · clear cost1 cost6 s0 s1 scount0 shigh1 shigh2 shigh3 slow7 t0 tcount7 termA termEvenA thigh0 thigh2 thigh5
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost0 cost2 cost3 oneLow orderBig scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 smallDark t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termB termEvenB thigh4
      omega
    · clear shigh0
      by_cases pos3 : 0<b2
      · clear cost3 orderSmall tcount0 tcount4 termB
        by_cases pos4 : 0<b4
        · have usethigh4 := thigh4 pos4
          have usecost2 := cost2 pos3
          clear bigDeep cost0 cost2 smallDark t1 tcount1 thigh4
          omega
        · clear orderBig thigh4
          by_cases pos5 : 0<b0
          · have usecost0 := cost0 pos5
            have usecost2 := cost2 pos3
            clear bigDeep cost0 cost2 smallDark t1 tcount1 tcount2 tcount3 tcount5
            omega
          · clear cost0 cost2 scount4 scount5 scount7
            omega
      · clear cost0 cost2 smallDark tcount2 thigh4
        by_cases pos4 : 0<b3
        · have usecost3 := cost3 pos4
          clear bigDeep cost3 orderBig orderSmall tcount0 tcount4 termB
          omega
        · clear cost3 t1 tcount3 termEvenB
          omega
  · clear cost6 s0 s1 scount2 scount4 scount5 scount7 shigh0 shigh1 shigh3 slow7 t0 t1 tcount7 thigh0 thigh2 thigh4 thigh5
    by_cases pos2 : 0<a2
    · have useshigh2 := shigh2 pos2
      clear bigDeep cost0 cost1 cost2 cost3 oneLow orderBig scount0 scount1 scount3 scount6 shigh2 smallDark tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termA termB termEvenA termEvenB
      omega
    · clear shigh2
      by_cases pos3 : 0<b0
      · clear cost1 tcount2 termA
        by_cases pos4 : 0<b2
        · have usecost0 := cost0 pos3
          have usecost2 := cost2 pos4
          clear bigDeep cost0 cost2 cost3 orderBig orderSmall tcount0 tcount1 tcount3 tcount4 tcount5 termB termEvenB
          omega
        · clear cost0 cost2
          by_cases pos5 : 0<b3
          · have usecost3 := cost3 pos5
            clear bigDeep cost3 orderBig tcount0 tcount4 termB
            omega
          · clear cost3 tcount3 termEvenA termEvenB
            omega
      · clear cost0 cost2 cost3 tcount0 termB
        by_cases pos4 : 0<b1
        · have usecost1 := cost1 pos4
          clear bigDeep cost1 orderBig tcount2 tcount5 termA
          omega
        · clear cost1 tcount1 termEvenA termEvenB
          omega
  · clear cost1 cost6 s0 s1 scount0 shigh1 shigh2 shigh3 slow7 smallDark t0 tcount7 termEvenA thigh0 thigh2 thigh4 thigh5
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost0 cost2 cost3 oneLow orderBig scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termA termB termEvenB
      omega
    · clear shigh0
      by_cases pos3 : 0<b0
      · clear t1 tcount2 tcount3 termA
        by_cases pos4 : 0<b2
        · have usecost0 := cost0 pos3
          have usecost2 := cost2 pos4
          clear bigDeep cost0 cost2 cost3 orderBig orderSmall tcount0 tcount1 tcount4 tcount5 termB
          omega
        · clear cost2
          by_cases pos5 : 0<b3
          · have usecost0 := cost0 pos3
            have usecost3 := cost3 pos5
            clear bigDeep cost0 cost3 orderBig orderSmall tcount0 tcount4 tcount5 termB
            omega
          · clear cost0 cost3 termEvenB
            omega
      · clear cost0 tcount0
        by_cases pos4 : 0<b2
        · have usecost2 := cost2 pos4
          clear cost2 cost3 termB
          omega
        · clear cost2 tcount2 termA
          by_cases pos5 : 0<b3
          · have usecost3 := cost3 pos5
            clear bigDeep cost3 orderBig orderSmall tcount4 termB
            omega
          · clear cost3 t1 tcount3 termEvenB
            omega
  · clear bigDeep cost0 cost1 cost2 cost3 cost6 oneLow orderBig s0 s1 scount0 scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 shigh1 shigh2 shigh3 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 tcount7 termA termB termEvenA termEvenB thigh0 thigh2 thigh4 thigh5
    omega
  · clear cost1 cost2 cost3 cost6 s0 s1 scount4 scount5 scount7 shigh0 shigh1 shigh2 shigh3 slow7 t0 tcount4 tcount7 termA termEvenA thigh0 thigh2 thigh5
    by_cases pos2 : 0<b4
    · have usethigh4 := thigh4 pos2
      clear bigDeep cost0 oneLow orderSmall scount0 scount1 scount2 scount3 scount6 smallDark t1 tcount0 tcount1 tcount2 tcount3 tcount5 tcount6 termEvenB thigh4
      omega
    · clear thigh4
      by_cases pos3 : 0<b0
      · have usecost0 := cost0 pos3
        clear bigDeep cost0 t1 tcount2 tcount3 tcount5 termEvenB
        omega
      · clear cost0 orderBig orderSmall tcount0 termB
        omega
  · clear cost1 cost3 cost6 orderBig s0 s1 scount0 scount2 scount4 scount5 scount7 shigh1 shigh3 tcount7 termA termB thigh0 thigh2 thigh4 thigh5
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost0 cost2 oneLow scount1 scount3 scount6 shigh0 shigh2 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termEvenA termEvenB
      omega
    · clear shigh0
      by_cases pos3 : 0<a2
      · have useshigh2 := shigh2 pos3
        clear bigDeep cost0 cost2 oneLow scount1 scount3 scount6 shigh2 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termEvenA termEvenB
        omega
      · clear shigh2
        by_cases pos4 : 0<x7
        · have useslow7 := slow7 pos4
          clear bigDeep cost0 cost2 oneLow scount1 scount3 scount6 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termEvenA termEvenB
          omega
        · clear slow7
          by_cases pos5 : 0<b0
          · clear t1 tcount2
            by_cases pos6 : 0<b2
            · have usecost0 := cost0 pos5
              have usecost2 := cost2 pos6
              clear bigDeep cost0 cost2 orderSmall t0 tcount0 tcount1 tcount3 tcount4 tcount5 termEvenA
              omega
            · clear cost0 cost2
              omega
          · clear cost0 cost2 t0 tcount0
            omega
  · clear cost1 cost6 s0 s1 scount0 shigh1 shigh2 shigh3 slow7 smallDark t0 tcount7 termEvenA thigh0 thigh2 thigh4 thigh5
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost0 cost2 cost3 oneLow orderBig scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termA termB termEvenB
      omega
    · clear shigh0
      by_cases pos3 : 0<b0
      · clear t1 tcount2 tcount3 termA
        by_cases pos4 : 0<b2
        · have usecost0 := cost0 pos3
          have usecost2 := cost2 pos4
          clear bigDeep cost0 cost2 cost3 orderBig orderSmall tcount0 tcount1 tcount4 tcount5 termB
          omega
        · clear cost2
          by_cases pos5 : 0<b3
          · have usecost0 := cost0 pos3
            have usecost3 := cost3 pos5
            clear bigDeep cost0 cost3 orderBig orderSmall tcount0 tcount4 tcount5 termB
            omega
          · clear cost0 cost3 termEvenB
            omega
      · clear cost0 tcount0
        by_cases pos4 : 0<b2
        · have usecost2 := cost2 pos4
          clear cost2 cost3 termB
          omega
        · clear cost2 tcount2 termA
          by_cases pos5 : 0<b3
          · have usecost3 := cost3 pos5
            clear bigDeep cost3 orderBig orderSmall tcount4 termB
            omega
          · clear cost3 t1 tcount3 termEvenB
            omega
  · clear bigDeep cost0 cost1 cost2 cost3 cost6 oneLow orderBig s0 s1 scount0 scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 shigh1 shigh2 shigh3 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 tcount7 termA termB termEvenA termEvenB thigh0 thigh2 thigh4 thigh5
    omega
  · clear bigDeep cost0 cost1 cost2 cost3 cost6 oneLow orderBig s0 s1 scount0 scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 shigh1 shigh2 shigh3 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 tcount7 termA termB termEvenA termEvenB thigh0 thigh2 thigh4 thigh5
    omega
  · clear cost1 cost3 cost6 s0 s1 scount2 scount4 scount5 scount7 shigh0 shigh1 tcount4 tcount7 termA thigh2 thigh5
    by_cases pos2 : 0<a2
    · have useshigh2 := shigh2 pos2
      clear bigDeep cost0 cost2 oneLow orderBig scount0 scount1 scount3 scount6 shigh2 shigh3 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount5 tcount6 termB termEvenA termEvenB thigh0 thigh4
      omega
    · clear shigh2
      by_cases pos3 : 0<a3
      · clear cost2 slow7 t0 termEvenA thigh0
        by_cases pos4 : 0<b4
        · have usethigh4 := thigh4 pos4
          clear bigDeep cost0 oneLow orderSmall scount0 scount1 scount3 scount6 shigh3 smallDark t1 tcount0 tcount1 tcount2 tcount3 tcount5 tcount6 termEvenB thigh4
          omega
        · clear thigh4
          by_cases pos5 : 0<b0
          · have usecost0 := cost0 pos5
            clear bigDeep cost0 shigh3 t1 tcount2 tcount3 tcount5 termEvenB
            omega
          · have useshigh3 := shigh3 pos3
            clear cost0 orderBig shigh3 tcount0 termB
            omega
      · clear cost0 scount3 shigh3
        by_cases pos4 : 0<x7
        · have useslow7 := slow7 pos4
          clear bigDeep cost2 oneLow orderBig scount0 scount1 scount6 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount5 tcount6 termB termEvenA termEvenB thigh0 thigh4
          omega
        · clear orderSmall slow7
          by_cases pos5 : 0<b0
          · clear t1
            by_cases pos6 : 0<b4
            · have usethigh4 := thigh4 pos6
              clear bigDeep cost2 oneLow scount0 scount1 scount6 smallDark t0 tcount0 tcount1 tcount2 tcount3 tcount5 tcount6 termEvenA termEvenB thigh0 thigh4
              omega
            · clear thigh4
              by_cases pos7 : 0<b2
              · have usethigh0 := thigh0 pos5
                have usecost2 := cost2 pos7
                clear bigDeep cost2 t0 tcount0 tcount1 termB termEvenA thigh0
                omega
              · have usethigh0 := thigh0 pos5
                clear cost2 tcount2 termEvenB thigh0
                omega
          · clear cost2 t0 tcount0 termEvenA thigh0
            by_cases pos6 : 0<b4
            · have usethigh4 := thigh4 pos6
              clear bigDeep oneLow scount0 scount1 scount6 smallDark t1 tcount1 tcount2 tcount3 tcount5 tcount6 termEvenB thigh4
              omega
            · clear orderBig termB thigh4
              omega
  · clear cost1 cost6 s0 s1 scount0 scount2 scount4 scount5 scount7 shigh1 shigh3 slow7 t0 tcount7 termA termEvenA thigh0 thigh2 thigh5
    by_cases pos2 : 0<a0
    · have useshigh0 := shigh0 pos2
      clear bigDeep cost0 cost2 cost3 oneLow orderBig scount1 scount3 scount6 shigh0 shigh2 smallDark t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termB termEvenB thigh4
      omega
    · clear shigh0
      by_cases pos3 : 0<a2
      · have useshigh2 := shigh2 pos3
        clear bigDeep cost0 cost2 cost3 oneLow orderBig scount1 scount3 scount6 shigh2 smallDark t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 termB termEvenB thigh4
        omega
      · clear shigh2
        by_cases pos4 : 0<b4
        · clear cost0 t1
          by_cases pos5 : 0<b2
          · have usethigh4 := thigh4 pos4
            have usecost2 := cost2 pos5
            clear bigDeep cost2 cost3 orderSmall tcount0 tcount1 tcount4 termB thigh4
            omega
          · clear cost2 tcount2
            by_cases pos6 : 0<b3
            · have usethigh4 := thigh4 pos4
              have usecost3 := cost3 pos6
              clear bigDeep cost3 orderSmall tcount0 tcount4 termB thigh4
              omega
            · clear cost3 tcount3 termEvenB thigh4
              omega
        · clear cost2 cost3 tcount4 thigh4
          by_cases pos5 : 0<b0
          · have usecost0 := cost0 pos5
            clear bigDeep cost0 t1 tcount2 tcount3 tcount5 termEvenB
            omega
          · clear cost0 orderBig orderSmall tcount0 termB
            omega
  · clear bigDeep cost0 cost1 cost2 cost3 cost6 oneLow orderBig s0 s1 scount0 scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 shigh1 shigh2 shigh3 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 tcount7 termA termB termEvenA termEvenB thigh0 thigh2 thigh4 thigh5
    omega
  · clear bigDeep cost0 cost1 cost2 cost3 cost6 oneLow orderBig s0 s1 scount0 scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 shigh1 shigh2 shigh3 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 tcount7 termA termB termEvenA termEvenB thigh0 thigh2 thigh4 thigh5
    omega
  · clear bigDeep cost0 cost1 cost2 cost3 cost6 oneLow orderBig s0 s1 scount0 scount1 scount2 scount3 scount4 scount5 scount6 scount7 shigh0 shigh1 shigh2 shigh3 slow7 smallDark t0 t1 tcount0 tcount1 tcount2 tcount3 tcount4 tcount5 tcount6 tcount7 termA termB termEvenA termEvenB thigh0 thigh2 thigh4 thigh5
    omega

#print axioms impossible_seven_eleven_counts
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
