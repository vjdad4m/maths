import DegreeFiveReverseSupport189
import DegreeFiveBalancedMixedBudget189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private tight_shell_high_contact from DegreeFiveReverseSupport189
open private mixedPorters from DegreeFiveBalancedMixedBudget189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- A mixed edge between two tight two-contact colors propagates to
all four mixed pairs. The weighted parity bound then leaves order ≤7. -/
theorem two_two_mixed_small_of_tight_shells
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (none : ∀ v∈Shore D,¬(G.Adj a v ∧ G.Adj b v))
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=2)
    (eA : (secondShore D a).card=3) (eB : (secondShore D b).card=3)
    (cA : (secondShore C a).card=1) (cB : (secondShore C b).card=1)
    (high : ∀ w∈Shore D,5≤G.degree w)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    {u v : V} (ua : u∈portColor D a) (vb : v∈portColor D b) (uv : G.Adj u v) :
    (Shore D).card≤7 := by
  classical
  let A := portColor D a
  let B := portColor D b
  have a2 : A.card=2 := pA
  have b2 : B.card=2 := pB
  obtain ⟨ud,au⟩ := mem_filter.mp ua
  obtain ⟨vd,bv⟩ := mem_filter.mp vb
  have no {w : V} (wd : w∈Shore D) {c : V} (co : c∉Shore D) : c≠w :=
    fun h=>co (h.symm ▸ wd)
  have va : v∈secondShore D a := mem_inter.mpr ⟨vd,
    d2 hc (no vd (shore_off D).1) (fun av=>none v vd ⟨av,bv⟩) au uv⟩
  have adjA (w : V) (wa : w∈A) : G.Adj w v := by
    obtain ⟨wd,aw⟩ := mem_filter.mp wa
    exact tight_shell_high_contact hc (.inl ⟨rfl,rfl⟩) (by omega) wa
      (fun bw=>none w wd ⟨aw,bw⟩) (high w wd) v va
  have adjB (w t : V) (wa : w∈A) (tb : t∈B) : G.Adj t w := by
    obtain ⟨wd,aw⟩ := mem_filter.mp wa
    obtain ⟨td,bt⟩ := mem_filter.mp tb
    have bw := fun bw=>none w wd ⟨aw,bw⟩
    have h : w∈secondShore D b := mem_inter.mpr ⟨wd,
      d2 hc (no wd (shore_off D).2) bw bv (adjA w wa).symm⟩
    exact tight_shell_high_contact hc (.inr ⟨rfl,rfl⟩) (by omega) tb
      (fun at'=>none t td ⟨at',bt⟩) (high t td) w h
  have subA : A⊆mixedPorters D b a := by
    intro w wa
    obtain ⟨wd,aw⟩ := mem_filter.mp wa
    exact mem_filter.mpr ⟨wd,aw,v,vd,bv,adjA w wa⟩
  have subB : B⊆mixedPorters D a b := by
    intro w wb
    obtain ⟨wd,bw⟩ := mem_filter.mp wb
    exact mem_filter.mpr ⟨wd,bw,u,ud,au,adjB u w ua wb⟩
  have disAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro w wa wb
    exact none w (mem_filter.mp wa).1 ⟨(mem_filter.mp wa).2,(mem_filter.mp wb).2⟩
  have eq : A∪B=cutPorts D := by ext w; simp [A,B,portColor,cutPorts,and_or_left]
  have four : 4≤(cutPorts D).card := by
    rw [←eq,card_union_of_disjoint disAB,a2,b2]
  have k := exclusive_shore_order_add_mixed_add_charges_le_thirteen hc two even conn cd xc ax bx none four
  have la := card_le_card subA
  have lb := card_le_card subB
  omega

#print axioms two_two_mixed_small_of_tight_shells
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
