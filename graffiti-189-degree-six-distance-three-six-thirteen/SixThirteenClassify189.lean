import SixThirteenSat189
namespace Graffiti189LongestPath.SixThirteenSat
set_option maxHeartbeats 100000000
def shapeData : Array (List ℕ) := #[
  [1,5,0,5,0,1,0,0,0,7,0],
  [1,5,0,5,0,1,0,0,0,7,2],
  [1,5,0,5,0,1,0,0,0,7,4],
  [1,5,0,5,0,1,0,0,0,7,8],
  [1,5,1,4,1,0,0,0,1,6,3],
  [1,5,2,3,1,0,0,0,1,6,3],
  [1,5,3,2,1,0,0,0,1,6,3],
  [1,5,4,1,1,0,0,0,1,6,3],
  [1,5,5,0,1,0,0,0,1,6,3],
  [2,4,0,4,0,2,0,0,0,7,0],
  [2,4,0,4,0,2,0,0,0,7,2],
  [2,4,0,4,0,2,0,0,0,7,4],
  [2,4,0,4,0,2,0,0,0,7,8],
  [2,4,0,4,1,1,1,0,0,6,3],
  [2,4,1,3,0,2,0,1,0,6,1],
  [2,4,3,1,5,0,0,1,2,1,8],
  [2,4,3,2,5,0,0,0,2,1,8],
  [2,4,4,0,5,0,0,1,2,1,8],
  [2,4,4,1,5,0,0,0,2,1,8],
  [2,4,5,0,5,0,0,0,2,1,8],
  [3,3,0,3,0,3,0,0,0,7,0],
  [3,3,0,3,0,3,0,0,0,7,2],
  [3,3,0,3,0,3,0,0,0,7,4],
  [3,3,0,3,0,3,0,0,0,7,8],
  [3,3,0,3,1,2,1,0,0,6,3],
  [3,3,1,2,0,3,0,1,0,6,1],
  [3,3,3,0,3,0,0,0,3,4,0],
  [3,3,3,0,3,0,0,0,3,4,1],
  [3,3,3,0,3,0,0,0,3,4,3],
  [3,3,3,0,3,0,0,0,3,4,7],
  [3,3,3,0,3,0,0,0,3,4,8],
  [3,3,3,0,3,0,1,1,2,3,0],
  [3,3,3,0,3,0,1,1,2,3,1],
  [3,3,3,0,3,0,1,1,2,3,3],
  [3,3,3,0,3,0,1,1,2,3,5],
  [3,3,3,0,3,0,1,1,2,3,6],
  [3,3,3,0,3,0,1,1,2,3,7],
  [3,3,3,0,3,0,1,1,2,3,8],
  [3,3,3,0,3,0,2,2,1,2,0],
  [3,3,3,0,3,0,2,2,1,2,1],
  [3,3,3,0,3,0,2,2,1,2,3],
  [3,3,3,0,3,0,2,2,1,2,5],
  [3,3,3,0,3,0,2,2,1,2,6],
  [3,3,3,0,3,0,2,2,1,2,7],
  [3,3,3,0,3,0,2,2,1,2,8],
  [3,3,4,0,4,0,1,1,2,1,8],
  [3,3,4,0,4,1,0,1,2,1,8],
  [3,3,4,0,5,0,0,0,3,1,8],
  [3,3,4,0,5,0,0,1,2,1,8],
  [3,3,4,1,4,0,1,0,2,1,8],
  [3,3,4,1,4,1,0,0,2,1,8],
  [3,3,4,1,5,0,0,0,2,1,8],
  [3,3,5,0,4,0,0,0,3,1,8],
  [3,3,5,0,4,0,1,0,2,1,8],
  [3,3,5,0,4,1,0,0,2,1,8],
  [3,3,5,0,5,0,0,0,2,1,8],
  [3,3,5,0,5,0,0,0,3,0,0],
  [3,3,5,0,5,0,0,0,3,0,1],
  [3,3,5,0,5,0,0,0,3,0,3],
  [3,3,5,0,5,0,0,0,3,0,7]]

set_option linter.unusedVariables false in
theorem classify_shape
    (p q x0 x1 x2 x3 x4 x5 x6 x7 e0 e1 e2 e3 e4 e5 e6 e7 l : ℕ)
    (p0 : 1≤p)
    (q0 : 1≤q)
    (norm : p≤q)
    (q5 : q≤5)
    (ps : 5≤p+q)
    (ps6 : p+q≤6)
    (ord : x0+x1+x2+x3+x4+x5+x6+x7=13)
    (low : e0+e1+e2+e3+e4+e5+e6+e7+5≤p+q)
    (pa : x0+x1+x5≤5)
    (pb : x2+x3+x4≤5)
    (ha : 6≤p+x0+x1)
    (hb : 6≤q+x2+x3)
    (va : x3+x4+x6≤p)
    (vb : x1+x5+x6≤q)
    (l8 : l≤8)
    (e0le : e0≤x0)
    (l0 : l=1 → e0=1)
    (nl0 : l≠1 → e0=0)
    (d0 : e0<x0 → 6≤x0+x1+x4+x6)
    (m0 : 0<x0 → 2≤x0+x1+x4+x6)
    (e1le : e1≤x1)
    (l1 : l=2 → e1=1)
    (nl1 : l≠2 → e1=0)
    (d1 : e1<x1 → 6≤x0+x1+x3+x4+x6)
    (m1 : 0<x1 → 2≤x0+x1+x3+x4+x6)
    (e2le : e2≤x2)
    (l2 : l=3 → e2=1)
    (nl2 : l≠3 → e2=0)
    (d2 : e2<x2 → 6≤x2+x3+x5+x6)
    (m2 : 0<x2 → 2≤x2+x3+x5+x6)
    (e3le : e3≤x3)
    (l3 : l=4 → e3=1)
    (nl3 : l≠4 → e3=0)
    (d3 : e3<x3 → 6≤x1+x2+x3+x5+x6)
    (m3 : 0<x3 → 2≤x1+x2+x3+x5+x6)
    (e4le : e4≤x4)
    (l4 : l=5 → e4=1)
    (nl4 : l≠5 → e4=0)
    (d4 : e4<x4 → 7≤x0+x1+x4+x5+x6+x7)
    (m4 : 0<x4 → 3≤x0+x1+x4+x5+x6+x7)
    (e5le : e5≤x5)
    (l5 : l=6 → e5=1)
    (nl5 : l≠6 → e5=0)
    (d5 : e5<x5 → 7≤x2+x3+x4+x5+x6+x7)
    (m5 : 0<x5 → 3≤x2+x3+x4+x5+x6+x7)
    (e6le : e6≤x6)
    (l6 : l=7 → e6=1)
    (nl6 : l≠7 → e6=0)
    (d6 : e6<x6 → 7≤x0+x1+x2+x3+x4+x5+x6+x7)
    (m6 : 0<x6 → 3≤x0+x1+x2+x3+x4+x5+x6+x7)
    (e7le : e7≤x7)
    (l7 : l=8 → e7=1)
    (nl7 : l≠8 → e7=0)
    (d7 : e7<x7 → 7≤x4+x5+x6+x7)
    (m7 : 0<x7 → 3≤x4+x5+x6+x7)
    : ∃ i : Fin 60, shapeData[i.val]! = [p,q,x0,x1,x2,x3,x4,x5,x6,x7,l] := by
  have pCases : p=1 ∨ p=2 ∨ p=3 := by omega
  have qCases : q=3 ∨ q=4 ∨ q=5 := by omega
  have lCases : l=0 ∨ l=1 ∨ l=2 ∨ l=3 ∨ l=4 ∨ l=5 ∨ l=6 ∨ l=7 ∨ l=8 := by omega
  rcases pCases with hp|hp|hp <;> rcases qCases with hq|hq|hq <;> rcases lCases with hl|hl|hl|hl|hl|hl|hl|hl|hl
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    by_cases hg2 : e7<x7
    · have used7 := d7 hg2
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
      omega
  · 
    have en0 : e0=1 := l0 hl
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=1 := l1 hl
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=1 := l2 hl
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=1 := l3 hl
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=1 := l4 hl
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=1 := l5 hl
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=1 := l6 hl
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=1 := l7 hl
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=5 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
      omega
    have hx5 : x2=0 := by
      by_cases hg3 : e2<x2
      · have used2 := d2 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=1 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx7 : x4=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx8 : x5=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
      omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=7 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨0, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=1 := l0 hl
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    by_cases hg2 : e2<x2
    · by_cases hg3 : e7<x7
      · have used2 := d2 hg2
        have used7 := d7 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
        omega
    · by_cases hg3 : e3<x3
      · have used3 := d3 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=1 := l1 hl
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=5 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
      omega
    have hx5 : x2=0 := by
      by_cases hg3 : e2<x2
      · have used2 := d2 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=1 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx7 : x4=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx8 : x5=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
      omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=7 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨1, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=1 := l2 hl
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=1 ∨ x0=2 ∨ x0=3 ∨ x0=4 ∨ x0=5 := by
      by_cases hg3 : 0<x2
      · by_cases hg4 : e7<x7
        · have usem2 := m2 hg3
          have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 va
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    rcases hx3 with hx3|hx3|hx3|hx3|hx3
    · have hx4 : x1=4 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=1 := by
        by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=0 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx7 : x4=0 := by
        by_cases hg4 : 0<x2
        · have usem2 := m2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx9 : x6=1 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx10 : x7=6 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨4, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=3 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=1 := by
        by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=0 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx7 : x4=0 := by
        by_cases hg4 : 0<x2
        · have usem2 := m2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx9 : x6=1 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx10 : x7=6 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨5, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=2 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=1 := by
        by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=0 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx7 : x4=0 := by
        by_cases hg4 : 0<x2
        · have usem2 := m2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx9 : x6=1 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx10 : x7=6 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨6, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=1 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=1 := by
        by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=0 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx7 : x4=0 := by
        by_cases hg4 : 0<x2
        · have usem2 := m2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx9 : x6=1 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx10 : x7=6 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨7, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=1 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      have hx6 : x3=0 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx7 : x4=0 := by
        by_cases hg4 : 0<x2
        · have usem2 := m2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx9 : x6=1 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx10 : x7=6 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨8, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=1 := l3 hl
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 := by
      by_cases hg3 : e0<x0
      · have used0 := d0 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=5 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
      omega
    have hx5 : x2=0 := by
      by_cases hg3 : e2<x2
      · have used2 := d2 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 ps ps6 q0 q5 vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=1 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx7 : x4=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx8 : x5=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
      omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=7 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨2, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=1 := l4 hl
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    by_cases hg2 : e2<x2
    · have used2 := d2 hg2
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 ps ps6 q0 q5 vb
      omega
    · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=1 := l5 hl
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=1 := l6 hl
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    by_cases hg2 : e2<x2
    · by_cases hg3 : e7<x7
      · have used2 := d2 hg2
        have used7 := d7 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
        omega
    · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=1 := l7 hl
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=5 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
      omega
    have hx5 : x2=0 := by
      by_cases hg3 : e2<x2
      · have used2 := d2 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=1 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx7 : x4=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx8 : x5=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
      omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=7 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨3, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    by_cases hg2 : e7<x7
    · have used7 := d7 hg2
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
      omega
  · 
    have en0 : e0=1 := l0 hl
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=1 := l1 hl
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=1 := l2 hl
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=1 := l3 hl
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=1 := l4 hl
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=1 := l5 hl
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=1 := l6 hl
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=1 := l7 hl
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=4 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx5 : x2=0 := by
      by_cases hg3 : e2<x2
      · have used2 := d2 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=2 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx7 : x4=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx8 : x5=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=7 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨9, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=1 := l0 hl
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=1 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=3 := by
      by_cases hg3 : e7<x7
      · have used7 := d7 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
        omega
    have hx5 : x2=0 := by
      by_cases hg3 : e2<x2
      · by_cases hg4 : e7<x7
        · have used2 := d2 hg3
          have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=2 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx7 : x4=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx8 : x5=1 := by
      by_cases hg3 : e3<x3
      · have used3 := d3 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=6 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨14, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=1 := l1 hl
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=4 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx5 : x2=0 := by
      by_cases hg3 : e2<x2
      · have used2 := d2 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=2 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx7 : x4=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx8 : x5=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=7 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨10, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=1 := l2 hl
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=4 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx5 : x2=1 := by
      by_cases hg3 : e2<x2
      · have used2 := d2 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=1 := by
      by_cases hg3 : e7<x7
      · have used7 := d7 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
        omega
    have hx7 : x4=1 := by
      by_cases hg3 : e1<x1
      · have used1 := d1 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx8 : x5=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=6 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨13, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=1 := l3 hl
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e7<x7
        · have used0 := d0 hg3
          have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=4 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx5 : x2=0 := by
      by_cases hg3 : e2<x2
      · have used2 := d2 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=2 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx7 : x4=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx8 : x5=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=7 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨11, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=1 := l4 hl
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    by_cases hg2 : e2<x2
    · by_cases hg3 : e7<x7
      · have used2 := d2 hg2
        have used7 := d7 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
        omega
    · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=1 := l5 hl
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    by_cases hg2 : e0<x0
    · by_cases hg3 : e2<x2
      · by_cases hg4 : e7<x7
        · have used2 := d2 hg3
          have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      · have used0 := d0 hg2
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
        omega
    · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=1 := l6 hl
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    by_cases hg2 : e2<x2
    · by_cases hg3 : e7<x7
      · have used2 := d2 hg2
        have used7 := d7 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
        omega
    · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=1 := l7 hl
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 ∨ x0=3 ∨ x0=4 ∨ x0=5 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 va
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    rcases hx3 with hx3|hx3|hx3|hx3
    · have hx4 : x1=4 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
        omega
      have hx5 : x2=0 := by
        by_cases hg4 : e2<x2
        · have used2 := d2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=2 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx7 : x4=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
        omega
      have hx9 : x6=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx10 : x7=7 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨12, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=1 ∨ x1=2 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      rcases hx4 with hx4|hx4
      · have hx5 : x2=5 := by
          by_cases hg5 : e0<x0
          · by_cases hg6 : e2<x2
            · by_cases hg7 : e7<x7
              · have used2 := d2 hg6
                have used7 := d7 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
                omega
            · have used0 := d0 hg5
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
              omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx6 : x3=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        have hx7 : x4=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        have hx8 : x5=1 := by
          by_cases hg5 : e7<x7
          · have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
        have hx9 : x6=2 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=1 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨15, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx5 : x2=5 := by
          by_cases hg5 : e0<x0
          · by_cases hg6 : e7<x7
            · have used7 := d7 hg6
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
              omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx6 : x3=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        have hx7 : x4=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        have hx8 : x5=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
          omega
        have hx9 : x6=2 := by
          by_cases hg5 : e7<x7
          · have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
            omega
        have hx10 : x7=1 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨16, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 ∨ x1=1 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      rcases hx4 with hx4|hx4
      · have hx5 : x2=5 := by
          by_cases hg5 : e0<x0
          · by_cases hg6 : e2<x2
            · by_cases hg7 : e7<x7
              · have used2 := d2 hg6
                have used7 := d7 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
                omega
            · have used0 := d0 hg5
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
              omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx6 : x3=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        have hx7 : x4=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        have hx8 : x5=1 := by
          by_cases hg5 : e7<x7
          · have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
        have hx9 : x6=2 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=1 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨17, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx5 : x2=5 := by
          by_cases hg5 : e0<x0
          · by_cases hg6 : e7<x7
            · have used7 := d7 hg6
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
              omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx6 : x3=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        have hx7 : x4=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        have hx8 : x5=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
          omega
        have hx9 : x6=2 := by
          by_cases hg5 : e7<x7
          · have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
            omega
        have hx10 : x7=1 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨18, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=5 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      have hx6 : x3=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      have hx7 : x4=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx9 : x6=2 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
          omega
      have hx10 : x7=1 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨19, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 ∨ x0=3 ∨ x0=5 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 va
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    rcases hx3 with hx3|hx3|hx3
    · have hx4 : x1=3 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
        omega
      have hx5 : x2=0 := by
        by_cases hg4 : e2<x2
        · have used2 := d2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=3 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx7 : x4=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
        omega
      have hx9 : x6=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx10 : x7=7 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨20, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
          omega
      have hx5 : x2=3 := by
        by_cases hg4 : e0<x0
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=0 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx7 : x4=0 ∨ x4=1 ∨ x4=2 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      rcases hx7 with hx7|hx7|hx7
      · have hx8 : x5=0 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=3 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=4 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨26, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx8 : x5=1 := by
          by_cases hg5 : e0<x0
          · by_cases hg6 : e2<x2
            · have used0 := d0 hg5
              have used2 := d2 hg6
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5
              omega
            · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
              omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=2 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=3 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨31, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx8 : x5=2 := by
          by_cases hg5 : e2<x2
          · have used2 := d2 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=1 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=2 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨38, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=5 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      have hx6 : x3=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      have hx7 : x4=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx9 : x6=3 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
          omega
      have hx10 : x7=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨56, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=1 := l0 hl
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=1 ∨ x0=3 ∨ x0=5 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 va
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    rcases hx3 with hx3|hx3|hx3
    · have hx4 : x1=2 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
          omega
      have hx5 : x2=0 := by
        by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=3 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx7 : x4=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx8 : x5=1 := by
        by_cases hg4 : e3<x3
        · have used3 := d3 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx9 : x6=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx10 : x7=6 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨25, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
          omega
      have hx5 : x2=3 := by
        by_cases hg4 : e0<x0
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=0 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx7 : x4=0 ∨ x4=1 ∨ x4=2 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      rcases hx7 with hx7|hx7|hx7
      · have hx8 : x5=0 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=3 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=4 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨27, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx8 : x5=1 := by
          by_cases hg5 : e0<x0
          · by_cases hg6 : e2<x2
            · have used0 := d0 hg5
              have used2 := d2 hg6
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5
              omega
            · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
              omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=2 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=3 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨32, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx8 : x5=2 := by
          by_cases hg5 : e2<x2
          · have used2 := d2 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=1 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=2 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨39, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=5 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      have hx6 : x3=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      have hx7 : x4=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx9 : x6=3 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
          omega
      have hx10 : x7=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨57, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=1 := l1 hl
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 va
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=3 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx5 : x2=0 := by
      by_cases hg3 : e2<x2
      · have used2 := d2 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=3 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx7 : x4=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx8 : x5=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=7 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨21, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=1 := l2 hl
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 ∨ x0=3 ∨ x0=5 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 va
            omega
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
            omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    rcases hx3 with hx3|hx3|hx3
    · have hx4 : x1=3 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
        omega
      have hx5 : x2=1 := by
        by_cases hg4 : e2<x2
        · have used2 := d2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=2 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
          omega
      have hx7 : x4=1 := by
        by_cases hg4 : e1<x1
        · have used1 := d1 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
        omega
      have hx9 : x6=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx10 : x7=6 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨24, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
          omega
      have hx5 : x2=3 := by
        by_cases hg4 : e0<x0
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=0 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx7 : x4=0 ∨ x4=1 ∨ x4=2 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      rcases hx7 with hx7|hx7|hx7
      · have hx8 : x5=0 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=3 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=4 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨28, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx8 : x5=1 := by
          by_cases hg5 : e0<x0
          · by_cases hg6 : e2<x2
            · have used0 := d0 hg5
              have used2 := d2 hg6
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5
              omega
            · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
              omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=2 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=3 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨33, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx8 : x5=2 := by
          by_cases hg5 : e2<x2
          · have used2 := d2 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=1 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=2 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨40, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=5 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      have hx6 : x3=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      have hx7 : x4=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx9 : x6=3 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
          omega
      have hx10 : x7=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨58, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=1 := l3 hl
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e7<x7
        · have used0 := d0 hg3
          have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx4 : x1=3 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx5 : x2=0 := by
      by_cases hg3 : e2<x2
      · have used2 := d2 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=3 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx7 : x4=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx8 : x5=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
      omega
    have hx9 : x6=0 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
      omega
    have hx10 : x7=7 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
      omega
    exact ⟨22, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=1 := l4 hl
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=3 := by
      by_cases hg3 : e2<x2
      · by_cases hg4 : e7<x7
        · have used2 := d2 hg3
          have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
    have hx4 : x1=0 := by
      by_cases hg3 : e7<x7
      · have used7 := d7 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
        omega
    have hx5 : x2=3 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e7<x7
        · have used0 := d0 hg3
          have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=0 := by
      by_cases hg3 : e0<x0
      · have used0 := d0 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx7 : x4=1 ∨ x4=2 := by
      clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
      omega
    rcases hx7 with hx7|hx7
    · have hx8 : x5=1 := by
        by_cases hg4 : e0<x0
        · by_cases hg5 : e2<x2
          · have used0 := d0 hg4
            have used2 := d2 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx9 : x6=2 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx10 : x7=3 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨34, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx8 : x5=2 := by
        by_cases hg4 : e2<x2
        · have used2 := d2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx9 : x6=1 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx10 : x7=2 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨41, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=1 := l5 hl
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=3 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 va
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
        omega
    have hx4 : x1=0 := by
      by_cases hg3 : e7<x7
      · have used7 := d7 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
        omega
    have hx5 : x2=3 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e7<x7
        · have used0 := d0 hg3
          have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx6 : x3=0 := by
      by_cases hg3 : e0<x0
      · have used0 := d0 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    have hx7 : x4=1 ∨ x4=2 := by
      by_cases hg3 : e0<x0
      · have used0 := d0 hg3
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
        omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    rcases hx7 with hx7|hx7
    · have hx8 : x5=1 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx9 : x6=2 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx10 : x7=3 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨35, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx8 : x5=2 := by
        by_cases hg4 : e2<x2
        · have used2 := d2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx9 : x6=1 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx10 : x7=2 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨42, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=1 := l6 hl
    have en7 : e7=0 := nl7 (by omega)
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=3 ∨ x0=5 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 va
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
        omega
    rcases hx3 with hx3|hx3
    · have hx4 : x1=0 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
          omega
      have hx5 : x2=3 := by
        by_cases hg4 : e0<x0
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=0 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx7 : x4=0 ∨ x4=1 ∨ x4=2 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      rcases hx7 with hx7|hx7|hx7
      · have hx8 : x5=0 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=3 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=4 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨29, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx8 : x5=1 := by
          by_cases hg5 : e0<x0
          · by_cases hg6 : e2<x2
            · have used0 := d0 hg5
              have used2 := d2 hg6
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5
              omega
            · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
              omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=2 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=3 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨36, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx8 : x5=2 := by
          by_cases hg5 : e2<x2
          · have used2 := d2 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=1 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        have hx10 : x7=2 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨43, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=5 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      have hx6 : x3=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      have hx7 : x4=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx9 : x6=3 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
          omega
      have hx10 : x7=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨59, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · 
    have en0 : e0=0 := nl0 (by omega)
    have en1 : e1=0 := nl1 (by omega)
    have en2 : e2=0 := nl2 (by omega)
    have en3 : e3=0 := nl3 (by omega)
    have en4 : e4=0 := nl4 (by omega)
    have en5 : e5=0 := nl5 (by omega)
    have en6 : e6=0 := nl6 (by omega)
    have en7 : e7=1 := l7 hl
    clear l0 nl0 l1 nl1 l2 nl2 l3 nl3 l4 nl4 l5 nl5 l6 nl6 l7 nl7
    have hx3 : x0=0 ∨ x0=3 ∨ x0=4 ∨ x0=5 := by
      by_cases hg3 : e0<x0
      · by_cases hg4 : e2<x2
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg3
            have used2 := d2 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 va
            omega
        · have used0 := d0 hg3
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
          omega
      · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
        omega
    rcases hx3 with hx3|hx3|hx3|hx3
    · have hx4 : x1=3 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
        omega
      have hx5 : x2=0 := by
        by_cases hg4 : e2<x2
        · have used2 := d2 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=3 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx7 : x4=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx8 : x5=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
        omega
      have hx9 : x6=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
        omega
      have hx10 : x7=7 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
        omega
      exact ⟨23, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
          omega
      have hx5 : x2=3 := by
        by_cases hg4 : e0<x0
        · by_cases hg5 : e7<x7
          · have used0 := d0 hg4
            have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
            omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx6 : x3=0 := by
        by_cases hg4 : e0<x0
        · have used0 := d0 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
          omega
      have hx7 : x4=0 ∨ x4=1 ∨ x4=2 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
        omega
      rcases hx7 with hx7|hx7|hx7
      · have hx8 : x5=0 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=3 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=4 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨30, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx8 : x5=1 := by
          by_cases hg5 : e0<x0
          · by_cases hg6 : e2<x2
            · have used0 := d0 hg5
              have used2 := d2 hg6
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5
              omega
            · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
              omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=2 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=3 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨37, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx8 : x5=2 := by
          by_cases hg5 : e2<x2
          · have used2 := d2 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx9 : x6=1 := by
          by_cases hg5 : e0<x0
          · have used0 := d0 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=2 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨44, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 ∨ x1=1 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      rcases hx4 with hx4|hx4
      · have hx5 : x2=4 ∨ x2=5 := by
          by_cases hg5 : e7<x7
          · have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
            omega
        rcases hx5 with hx5|hx5
        · have hx6 : x3=0 ∨ x3=1 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
            omega
          rcases hx6 with hx6|hx6
          · have hx7 : x4=1 := by
              by_cases hg7 : e7<x7
              · have used7 := d7 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
                omega
            have hx8 : x5=1 := by
              by_cases hg7 : e7<x7
              · have used7 := d7 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
                omega
            have hx9 : x6=2 := by
              by_cases hg7 : e7<x7
              · have used7 := d7 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
                omega
            have hx10 : x7=1 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            exact ⟨45, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
          · have hx7 : x4=0 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
              omega
            have hx8 : x5=1 := by
              by_cases hg7 : e7<x7
              · have used7 := d7 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pb ps ps6 q0 q5 vb
                omega
            have hx9 : x6=2 := by
              by_cases hg7 : e0<x0
              · have used0 := d0 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
                omega
            have hx10 : x7=1 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            exact ⟨46, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
        · have hx6 : x3=0 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
            omega
          have hx7 : x4=0 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
            omega
          have hx8 : x5=0 ∨ x5=1 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
            omega
          rcases hx8 with hx8|hx8
          · have hx9 : x6=3 := by
              by_cases hg7 : e7<x7
              · have used7 := d7 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
                omega
            have hx10 : x7=1 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            exact ⟨47, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
          · have hx9 : x6=2 := by
              by_cases hg7 : e0<x0
              · have used0 := d0 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
                omega
            have hx10 : x7=1 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            exact ⟨48, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx5 : x2=4 ∨ x2=5 := by
          by_cases hg5 : e0<x0
          · by_cases hg6 : e7<x7
            · have used7 := d7 hg6
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
              omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
            omega
        rcases hx5 with hx5|hx5
        · have hx6 : x3=0 ∨ x3=1 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
            omega
          rcases hx6 with hx6|hx6
          · have hx7 : x4=1 := by
              by_cases hg7 : e7<x7
              · have used7 := d7 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa ps ps6 q0 q5 va
                omega
            have hx8 : x5=0 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
              omega
            have hx9 : x6=2 := by
              by_cases hg7 : e2<x2
              · have used2 := d2 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
                omega
            have hx10 : x7=1 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            exact ⟨49, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
          · have hx7 : x4=0 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
              omega
            have hx8 : x5=0 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
              omega
            have hx9 : x6=2 := by
              by_cases hg7 : e7<x7
              · have used7 := d7 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
                omega
            have hx10 : x7=1 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            exact ⟨50, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
        · have hx6 : x3=0 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
            omega
          have hx7 : x4=0 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
            omega
          have hx8 : x5=0 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
            omega
          have hx9 : x6=2 := by
            by_cases hg6 : e7<x7
            · have used7 := d7 hg6
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va
              omega
          have hx10 : x7=1 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
            omega
          exact ⟨51, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
    · have hx4 : x1=0 := by
        clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
        omega
      have hx5 : x2=4 ∨ x2=5 := by
        by_cases hg4 : e7<x7
        · have used7 := d7 hg4
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 ps ps6 q0 q5 vb
          omega
      rcases hx5 with hx5|hx5
      · have hx6 : x3=0 ∨ x3=1 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        rcases hx6 with hx6|hx6
        · have hx7 : x4=0 ∨ x4=1 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
            omega
          rcases hx7 with hx7|hx7
          · have hx8 : x5=0 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
              omega
            have hx9 : x6=3 := by
              by_cases hg7 : e7<x7
              · have used7 := d7 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
                omega
            have hx10 : x7=1 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            exact ⟨52, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
          · have hx8 : x5=0 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
              omega
            have hx9 : x6=2 := by
              by_cases hg7 : e2<x2
              · have used2 := d2 hg7
                clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 vb
                omega
              · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa pb ps ps6 q0 q5 va vb
                omega
            have hx10 : x7=1 := by
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            exact ⟨53, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
        · have hx7 : x4=0 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
            omega
          have hx8 : x5=0 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
            omega
          have hx9 : x6=2 := by
            by_cases hg6 : e7<x7
            · have used7 := d7 hg6
              clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
              omega
            · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 vb
              omega
          have hx10 : x7=1 := by
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
            omega
          exact ⟨54, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
      · have hx6 : x3=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        have hx7 : x4=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pa ps ps6 q0 q5 va vb
          omega
        have hx8 : x5=0 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm ord p0 pb ps ps6 q0 q5 va vb
          omega
        have hx9 : x6=2 := by
          by_cases hg5 : e7<x7
          · have used7 := d7 hg5
            clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
            omega
          · clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
            omega
        have hx10 : x7=1 := by
          clear d0 d1 d2 d3 d4 d5 d6 d7 e0le e1le e2le e3le e4le e5le e6le e7le ha hb low m0 m1 m2 m3 m4 m5 m6 m7 norm p0 pa pb ps ps6 q0 q5 va vb
          omega
        exact ⟨55, by rw [hp,hq,hl,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10]; rfl⟩
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega
  · clear p0 q0 ord low pa pb ha hb va vb l8 e0le d0 m0 e1le d1 m1 e2le d2 m2 e3le d3 m3 e4le d4 m4 e5le d5 m5 e6le d6 m6 e7le d7 m7
    omega

#print axioms classify_shape
end Graffiti189LongestPath.SixThirteenSat
