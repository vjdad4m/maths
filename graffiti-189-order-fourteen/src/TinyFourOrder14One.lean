import TinyFourOrder14OneRow14
import TinyFourOrder14OneRow15
import TinyFourOrder14OneRow16
import TinyFourOrder14OneRow17
import TinyFourOrder14OneRow18
import TinyFourOrder14OneRow19
import TinyFourOrder14OneRow110
import TinyFourOrder14OneRow111
import TinyFourOrder14OneRow25
import TinyFourOrder14OneRow26
import TinyFourOrder14OneRow27
import TinyFourOrder14OneRow28
import TinyFourOrder14OneRow29
import TinyFourOrder14OneRow210
import TinyFourOrder14OneRow36
import TinyFourOrder14OneRow37
import TinyFourOrder14OneRow38
import TinyFourOrder14OneRow39
import TinyFourOrder14OneRow47
import TinyFourOrder14OneRow48

namespace FourOrder14One
open Finset

private theorem rows (i j : ℕ) (ip : 1≤i) (sep : i+3≤j) (jp : j≤11) (rev : i≤12-j) :
    Table i j (by omega) (by omega) ∧ 4≤(sites i j).length := by
  have loc : i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases loc with t|t|t|t <;> subst i
  · have loc : j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 := by omega
    rcases loc with t|t|t|t|t|t|t|t <;> subst j
    · exact ⟨tbl14, by decide⟩
    · exact ⟨tbl15, by decide⟩
    · exact ⟨tbl16, by decide⟩
    · exact ⟨tbl17, by decide⟩
    · exact ⟨tbl18, by decide⟩
    · exact ⟨tbl19, by decide⟩
    · exact ⟨tbl110, by decide⟩
    · exact ⟨tbl111, by decide⟩
  · have loc : j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
    rcases loc with t|t|t|t|t|t <;> subst j
    · exact ⟨tbl25, by decide⟩
    · exact ⟨tbl26, by decide⟩
    · exact ⟨tbl27, by decide⟩
    · exact ⟨tbl28, by decide⟩
    · exact ⟨tbl29, by decide⟩
    · exact ⟨tbl210, by decide⟩
  · have loc : j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
    rcases loc with t|t|t|t <;> subst j
    · exact ⟨tbl36, by decide⟩
    · exact ⟨tbl37, by decide⟩
    · exact ⟨tbl38, by decide⟩
    · exact ⟨tbl39, by decide⟩
  · have loc : j=7 ∨ j=8 := by omega
    rcases loc with t|t <;> subst j
    · exact ⟨tbl47, by decide⟩
    · exact ⟨tbl48, by decide⟩

/-- The remaining finite models have a spanning path or one exact exceptional pattern. -/
theorem tiny (i j : ℕ) (ip : 1≤i) (sep : i+3≤j) (jp : j≤11) (rev : i≤12-j)
    (m : Marks) (e f g h t : Bool) (h0 : m 0=1) (h12 : m 11=2)
    (holes : ∀ k : Fin 12, hole i j k.val → m k=0)
    (LEFT : 4≤markCount m 1) (RIGHT : 4≤markCount m 2)
    (di : 4≤degree i j m e f g h t ⟨i,by omega⟩)
    (dj : 4≤degree i j m e f g h t ⟨j,by omega⟩)
    (exactPin : pinExact i j m e f g h t (by omega) (by omega))
    (d0 : (d2Set i j m e f g h t 0).card≤4)
    (d2i : (d2Set i j m e f g h t ⟨i,by omega⟩).card≤4)
    (d2j : (d2Set i j m e f g h t ⟨j,by omega⟩).card≤4)
    (d12 : (d2Set i j m e f g h t 12).card≤4)
    (d13 : (d2Set i j m e f g h t 13).card≤4) :
    Spanning i j m e f g h t ∨ Exceptional i j m e f g h t := by
  obtain ⟨tabs,enough⟩ := rows i j ip sep jp rev
  exact checked i j (by omega) (by omega) ip sep jp tabs enough m e f g h t h0 h12 holes
    LEFT RIGHT di dj exactPin d0 d2i d2j d12 d13

#print axioms tiny
end FourOrder14One
