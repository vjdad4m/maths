import DegreeFiveOneColorVisible189
import DegreeFiveActualCutSwap189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private swapCut from DegreeFiveActualCutSwap189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem visible_from_either_named_cut
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card ≤ 6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C4 : 4≤(cutPorts C).card) (shared : 2≤(sharedPortSet D).card)
    {c : V} (which : c=a ∨ c=b)
    (all : ∀ w∈cutPorts D,G.Adj c w)
    (near : ∀ x∈sharedPortSet D,(secondShore D x).card ≤ 1 ∧
      ∀ w∈Shore D,G.dist x w≤2) :
    Shore D⊆cutPorts D∪secondShore D c := by
  rcases which with rfl|cb
  · exact shore_with_all_ports_touching_first_visible hc two even cd C4 shared all near
  subst c
  let Cs := swapCut C
  let Ds := swapCut D
  have sc : Shore Cs=Shore C := shore_swapCut C
  have sd : Shore Ds=Shore D := shore_swapCut D
  have cp : cutPorts Cs=cutPorts C := by simp [cutPorts,sc,or_comm]
  have dp : cutPorts Ds=cutPorts D := by simp [cutPorts,sd,or_comm]
  have sp : sharedPortSet Ds=sharedPortSet D := by simp [sharedPortSet,sd,and_comm]
  have es (x : V) : secondShore Ds x=secondShore D x := by simp [secondShore,sd]
  have csd : Cs≠Ds := fun e=>cd (swapCut.injective e)
  have ts : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have h := shore_with_all_ports_touching_first_visible (a:=b) (b:=a) hc ts even csd
    (by rwa [cp]) (by rwa [sp]) (by rwa [dp])
    (by simpa [sp,sd,es] using near)
  simpa [sd,dp,es] using h

end Graffiti189LongestPath.CrossSaturation.FiveActualCut
