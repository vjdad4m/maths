import SixLayer24ModelMiddle189
import Equality24T3B4M0Cert189
import Equality24T3B4M1Cert189
import Equality24T3B4M2Cert189
import Equality24T3B5M0Cert189
import Equality24T3B5M1Cert189
import Equality24T3B5M2Cert189
import Equality24T3B6M1Cert189
import Equality24T3B6M2Cert189
import Equality24T4B4M0Cert189
import Equality24T4B4M1Cert189
import Equality24T4B4M2Cert189
import Equality24T4B5M0Cert189
import Equality24T4B5M1Cert189
import Equality24T4B5M2Cert189
import Equality24T4B6M1Cert189
import Equality24T4B6M2Cert189

namespace Graffiti189LongestPath.Equality24Profile
open SimpleGraph Finset Layer24Numbering
set_option linter.unusedSectionVars false

theorem model_impossible {G : SimpleGraph Vert} [DecidableRel G.Adj]
    {m : Kind} {t b : ℕ} (ht : t=3∨t=4) (b4 : 4≤b) (b6 : b≤6)
    (b5 : childCount m=12→b≤5) (M : Model G m t b) : False := by
  have bm : b=4∨b=5∨b=6 := by omega
  have mm : m=0∨m=1∨m=2 := by
    have l := m.isLt
    have h : m.val=0∨m.val=1∨m.val=2 := by omega
    rcases h with e|e|e <;> simp [Fin.ext_iff,e]
  rcases ht with rfl|rfl <;> rcases bm with rfl|rfl|rfl <;>
    rcases mm with rfl|rfl|rfl
  · exact Equality24Count.T3B4M0.impossible M
  · exact Equality24Count.T3B4M1.impossible M
  · exact Equality24Count.T3B4M2.impossible M
  · exact Equality24Count.T3B5M0.impossible M
  · exact Equality24Count.T3B5M1.impossible M
  · exact Equality24Count.T3B5M2.impossible M
  · have h := b5 (by decide)
    omega
  · exact Equality24Count.T3B6M1.impossible M
  · exact Equality24Count.T3B6M2.impossible M
  · exact Equality24Count.T4B4M0.impossible M
  · exact Equality24Count.T4B4M1.impossible M
  · exact Equality24Count.T4B4M2.impossible M
  · exact Equality24Count.T4B5M0.impossible M
  · exact Equality24Count.T4B5M1.impossible M
  · exact Equality24Count.T4B5M2.impossible M
  · have h := b5 (by decide)
    omega
  · exact Equality24Count.T4B6M1.impossible M
  · exact Equality24Count.T4B6M2.impossible M

/-- No order-24 graph in the exact degree-six case with connectivity at least three. -/
theorem impossible_order_twenty_four_at_degree_six_three_connected
    {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (x : V) (dx : G.degree x=6) (n : Fintype.card V=24) : False := by
  obtain ⟨e,m,t,b,ht,b4,_hi,_lo,b6,b5,M⟩ :=
    model_at_order_twenty_four hc cap conn high x dx n
  exact model_impossible ht b4 b6 b5 M

#print axioms model_impossible
#print axioms impossible_order_twenty_four_at_degree_six_three_connected
end Graffiti189LongestPath.Equality24Profile
