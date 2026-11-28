import AdjacentCutFiveFourteenSingletonTerminal189
import AdjacentCutFiveFourteenSingletonThree189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore from AdjacentCutFiveActual189
open private prof classSet from AdjacentCutFiveTopProfiles189
open private compact_graph_fourteen_singleton_profile from AdjacentCutFiveFourteenSingletonPartial189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

namespace AdjProfile

def Singleton14Frontier (a b c p q r : Nat) : Prop :=
     (a=2 ∧ b=2 ∧ c=2 ∧ p=1 ∧ q=1 ∧ r=3)
  ∨ (a=2 ∧ b=3 ∧ c=1 ∧ p=1 ∧ q=1 ∧ r=3)
  ∨ (a=2 ∧ b=3 ∧ c=1 ∧ p=1 ∧ q=2 ∧ r=2)
  ∨ (a=2 ∧ b=4 ∧ c=0 ∧ p=1 ∧ q=2 ∧ r=2)
  ∨ (a=3 ∧ b=3 ∧ c=0 ∧ p=1 ∧ q=2 ∧ r=2)
  ∨ (a=3 ∧ b=3 ∧ c=0 ∧ p=2 ∧ q=2 ∧ r=1)
  ∨ (a=3 ∧ b=3 ∧ c=1 ∧ p=1 ∧ q=1 ∧ r=2)

set_option maxHeartbeats 1000000 in
private theorem reduce_rows {a b c p q r : Nat}
    (row : Singleton14Rows a b c p q r)
    (ha : 3≤p+r) (hb : 3≤q+r) :
    Singleton14Frontier a b c p q r ∨
    (0<a ∧ 0<b ∧ c=0 ∧ p=1 ∧ q=1 ∧ ((4≤a ∨ 4≤b) ∨ (3≤a ∧ 3≤b ∧ 0<r))) := by
  unfold Singleton14Rows at row
  unfold Singleton14Frontier
  rcases row with h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := h <;> simp_all
end AdjProfile

/-- Up to exchanging terminals, a n=14 singleton counterexample must have
one of these seven parity profiles. This does not exclude the seven cases. -/
theorem frontier_of_adjacent_singleton_eleven_counterexample
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (one : (Shore C).card=1) (big : (Shore D).card=11)
    (fail : ¬∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support) :
    (let y := prof D
     AdjProfile.Singleton14Frontier y.ea y.eb y.ec y.oa y.ob y.oc ∨
     AdjProfile.Singleton14Frontier y.eb y.ea y.ec y.ob y.oa y.oc) := by
  classical
  obtain ⟨s,eq,as',bs',rows⟩ := compact_graph_fourteen_singleton_profile hc ab even conn degree cd one big
  have x := adjacent_singleton_terminal_profile_bounds hc ab degree cd cover one
  have sc : s∈Shore C := by simp [eq]
  have close (ea : 0<(prof D).ea) (eb : 0<(prof D).eb)
      (ec : (prof D).ec=0) (oa : (prof D).oa=1) (ob : (prof D).ob=1)
      (f : (4≤(prof D).ea ∨ 4≤(prof D).eb) ∨
        (3≤(prof D).ea ∧ 3≤(prof D).eb ∧ 0<(prof D).oc)) : False := by
    rcases f with f|⟨ta,tb,oc⟩
    · exact fail (traceable_of_adjacent_singleton_eleven_unique_four hc ab even conn degree cd one ea eb ec oa ob f)
    obtain ⟨x,y,xy,non,cut⟩ := nonadjacent_separator_of_common_other_unique_three_both
      hc ab even cd sc as' bs' ea eb ec oa ob ta tb oc
    exact fail (FiveActualCut.traceable_at_actual_five_nonadjacent_cut hc xy non even conn degree cut)
  rcases rows with r|r
  · rcases AdjProfile.reduce_rows r x.1 x.2 with r|⟨ea,eb,ec,oa,ob,f⟩
    · exact .inl r
    exact (close ea eb ec oa ob f).elim
  rcases AdjProfile.reduce_rows r x.2 x.1 with r|⟨eb,ea,ec,ob,oa,f⟩
  · exact .inr r
  have t : (4≤(prof D).ea ∨ 4≤(prof D).eb) ∨
      (3≤(prof D).ea ∧ 3≤(prof D).eb ∧ 0<(prof D).oc) := by
    rcases f with f|⟨tb,ta,oc⟩
    · exact .inl f.symm
    exact .inr ⟨ta,tb,oc⟩
  exact (close ea eb ec oa ob t).elim

#print axioms frontier_of_adjacent_singleton_eleven_counterexample
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
