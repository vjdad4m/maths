import DegreeFiveReverseSupport189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private local_shell_comes_from_port from DegreeFiveNonmixedThreeFour189
open private tight_shell_high_contact from DegreeFiveReverseSupport189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- No nonmixed opposite wing can realize the asymmetric (3,4)–(2,2)
configuration once the base shape and the a-shell size are known. -/
theorem no_nonmixed_at_three_four_opposite_two_two
    (hc : G.Connected) (two : G.dist a b=2)
    (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (none : ∀ w∈Shore D,¬(G.Adj a w ∧ G.Adj b w))
    (noMixed : ∀ u∈portColor D a,∀ v∈portColor D b,¬G.Adj u v)
    (twoA : (portColor D a).card=2) (twoB : (portColor D b).card=2)
    (fourC : (portColor C b).card=4) (shell : (secondShore D a).card=3)
    (high : ∀ w∈Shore D,5≤G.degree w)
    {z : V} (zc : z∈Shore C) (za : G.dist z a=2) (zb : G.Adj b z) :
    False := by
  classical
  let A := portColor D a
  let B := portColor D b
  let K := portColor C b
  let E := secondShore D a
  have cross {u v : V} (uc : u∈Shore C) (vd : v∈Shore D) : ¬G.Adj u v := by
    intro e
    rcases shore_closed C u uc v e with rfl|rfl|vc
    · exact (shore_off D).1 vd
    · exact (shore_off D).2 vd
    exact disjoint_left.mp (shore_disjoint cd) vc vd
  have bridge {u : V} (up : u∈A) : ∀ w∈E,G.Adj u w := by
    obtain ⟨ud,au⟩ := mem_filter.mp up
    exact tight_shell_high_contact hc (.inl ⟨rfl,rfl⟩) (by omega) up
      (fun h=>none _ ud ⟨au,h⟩) (high _ ud)
  have noA {w : V} (we : w∈E) : ¬ G.Adj a w := by
    intro aw
    have dist := (mem_filter.mp (mem_inter.mp we).2).2
    have q := dist_eq_one_iff_adj.mpr aw
    omega
  have noB {w : V} (we : w∈E) : ¬ G.Adj b w := by
    intro bw
    obtain ⟨u,ua,uw⟩ := local_shell_comes_from_port hc two (.inl rfl) we
    exact noMixed u ua w (mem_filter.mpr ⟨(mem_inter.mp we).1,bw⟩) uw
  have noPortAdj {w v : V} (we : w∈E) (vp : v∈B) : ¬ G.Adj v w := by
    intro vw
    obtain ⟨vd,bv⟩ := mem_filter.mp vp
    have foreign : K ⊆ DistanceTwo G v := by
      intro t tk
      obtain ⟨tc,bt⟩ := mem_filter.mp tk
      have ne : v≠t := fun h=>disjoint_left.mp (shore_disjoint cd) tc (h ▸ vd)
      exact d2 hc ne (fun h=>cross tc vd h.symm) bv.symm bt
    have localA : A ⊆ DistanceTwo G v := by
      intro u ua
      obtain ⟨ud,au⟩ := mem_filter.mp ua
      have ne : v≠u := fun h=>none u ud ⟨au,h ▸ bv⟩
      exact d2 hc ne (fun h=>noMixed u ua v vp h.symm) vw (bridge ua w we).symm
    have dis : Disjoint K A := (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)
    have q := (card_le_card (union_subset foreign localA)).trans (distanceTwo_le_of_even 5 v (even v))
    rw [card_union_of_disjoint dis] at q
    change K.card=4 at fourC
    change A.card=2 at twoA
    omega
  have four {w : V} (we : w∈E) : G.dist z w=4 := by
    have wd := (mem_inter.mp we).1
    have wc : w∉Shore C := fun h=>disjoint_left.mp (shore_disjoint cd) h wd
    have db : 3≤G.dist b w := by
      have ne : b≠w := fun h=>(shore_off D).2 (h.symm ▸ wd)
      have lo := hc.one_lt_dist_of_ne_of_not_adj ne (noB we)
      by_cases t : G.dist b w=2
      · obtain ⟨v,vp,vw⟩ := local_shell_comes_from_port hc two (.inr rfl)
          (show w∈secondShore D b from mem_inter.mpr ⟨wd,by simp [DistanceTwo,t]⟩)
        exact (noPortAdj we vp vw).elim
      omega
    have da := (mem_filter.mp (mem_inter.mp we).2).2
    have bz : G.dist z b=1 := dist_eq_one_iff_adj.mpr zb.symm
    have q := cross_metric (Shore C) hc zc wc (shore_closed C)
    rw [za,bz,da] at q
    omega
  have ben : B⊆DistanceTwo G z := by
    intro w wp
    obtain ⟨wd,bw⟩ := mem_filter.mp wp
    have ne : z≠w := fun h=>disjoint_left.mp (shore_disjoint cd) zc (h.symm ▸ wd)
    exact d2 hc ne (cross zc wd) zb.symm bw
  have dis : Disjoint E B := by
    apply disjoint_left.mpr
    intro w we wb
    exact noB we (mem_filter.mp wb).2
  have ss : insert z (insert a (E∪B)) ⊆ EvenFrom G z := by
    intro w hw
    unfold EvenFrom
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hw with rfl|hw
    · rw [SimpleGraph.dist_self]; decide
    rcases mem_insert.mp hw with rfl|hw
    · rw [za]; decide
    rcases mem_union.mp hw with we|wp
    · rw [four we]; decide
    have t := (mem_filter.mp (ben wp)).2
    rw [t]; decide
  have ao : a∉E∪B := by
    intro w
    rcases mem_union.mp w with e|h
    · exact (shore_off D).1 (mem_inter.mp e).1
    exact (shore_off D).1 (mem_filter.mp h).1
  have zo : z∉E∪B := by
    intro w
    apply disjoint_left.mp (shore_disjoint cd) zc
    rcases mem_union.mp w with e|h
    · exact (mem_inter.mp e).1
    exact (mem_filter.mp h).1
  have zz : z≠a := fun h=>(shore_off C).1 (h ▸ zc)
  have q := (card_le_card ss).trans (even z)
  rw [card_insert_of_not_mem (by simpa [zz] using zo),
    card_insert_of_not_mem ao,card_union_of_disjoint dis] at q
  change E.card=3 at shell
  change B.card=2 at twoB
  omega

#print axioms no_nonmixed_at_three_four_opposite_two_two
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
