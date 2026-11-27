import DegreeFiveReverseSupport189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private cross_nonadj nonmixed_shell_nonports from DegreeFiveReverseSupport189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem overlapping_shells_at_three_b_in_reverse
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (none : ∀ w∈Shore D,¬(G.Adj a w ∧ G.Adj b w))
    (nonmix : ∀ u∈portColor D a,∀ v∈portColor D b,¬G.Adj u v)
    (pA : (portColor D a).card=2) (eB : (secondShore D b).card=3)
    {z : V} (zc : z∈Shore C) (za : G.Adj a z) (zb : G.dist z b=2) :
    ∃ t, t∈secondShore D a ∧ t∈secondShore D b := by
  classical
  let A := portColor D a
  let E := secondShore D a
  let F := secondShore D b
  let R := F\E
  by_contra! no
  have sub : F⊆R := fun w wf => mem_sdiff.mpr ⟨wf,fun we=>no w we wf⟩
  have r3 : 3≤R.card := by
    have q := card_le_card sub
    change F.card=3 at eB
    omega
  have shell (w : V) (wr : w∈R) : G.dist z w=4 := by
    obtain ⟨wf,we⟩ := mem_sdiff.mp wr
    obtain ⟨wd,db⟩ := mem_inter.mp wf
    have db' := (mem_filter.mp db).2
    have wo : w∉Shore C := fun h=>disjoint_left.mp (shore_disjoint cd) h wd
    have az := dist_eq_one_iff_adj.mpr za.symm
    have an : ¬G.Adj a w := (nonmixed_shell_nonports hc two none nonmix
      (.inr ⟨rfl,rfl⟩) wf).1
    have aw : a≠w := fun e=>(shore_off D).1
      (Eq.mp (congrArg (fun v : V => v∈Shore D) e.symm) wd)
    have lo := hc.one_lt_dist_of_ne_of_not_adj aw an
    have da : G.dist a w≠2 := fun h=>we (mem_inter.mpr ⟨wd,by simp [DistanceTwo,h]⟩)
    have eq := cross_metric (Shore C) hc zc wo (shore_closed C)
    rw [az,zb,db'] at eq
    omega
  have ben : A⊆DistanceTwo G z := by
    intro w wm
    obtain ⟨wd,aw⟩ := mem_filter.mp wm
    have n : z≠w := fun h=>disjoint_left.mp (shore_disjoint cd) zc (h.symm ▸ wd)
    exact d2 hc n (cross_nonadj cd zc wd) za.symm aw
  have dis : Disjoint R A := by
    apply disjoint_left.mpr
    intro w wr wa
    exact (nonmixed_shell_nonports hc two none nonmix
      (.inr ⟨rfl,rfl⟩) (mem_sdiff.mp wr).1).1 (mem_filter.mp wa).2
  have off (w : V) (wm : w∈R∪A) : w∈Shore D := by
    rcases mem_union.mp wm with wr|wa
    · exact (mem_inter.mp (mem_sdiff.mp wr).1).1
    exact (mem_filter.mp wa).1
  have bo : b∉R∪A := fun h=>(shore_off D).2 (off b h)
  have zo : z∉R∪A := fun h=>disjoint_left.mp (shore_disjoint cd) zc (off z h)
  have zn : z≠b := fun e=>(shore_off C).2 (e ▸ zc)
  have ss : insert z (insert b (R∪A))⊆EvenFrom G z := by
    intro w ww
    unfold EvenFrom
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases mem_insert.mp ww with rfl|ww
    · rw [SimpleGraph.dist_self]; decide
    rcases mem_insert.mp ww with rfl|ww
    · rw [zb]; decide
    rcases mem_union.mp ww with wr|wa
    · rw [shell w wr]; decide
    rw [(mem_filter.mp (ben wa)).2]; decide
  have k := (card_le_card ss).trans (even z)
  rw [card_insert_of_not_mem (by simpa [zn] using zo),card_insert_of_not_mem bo,
    card_union_of_disjoint dis] at k
  change A.card=2 at pA
  omega

#print axioms overlapping_shells_at_three_b_in_reverse
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
