import DegreeFiveNonmixedThreeFour189
import DegreeFiveReverseCover189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private secondShore anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private local_shell_comes_from_port from DegreeFiveNonmixedThreeFour189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem reverse_boundary {D : Cmp (G:=G) (a:=a) (b:=b)} {c d : V}
    (dir : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) {u w : V} (ud : u∈Shore D) (uw : G.Adj u w) :
    w=c ∨ w=d ∨ w∈Shore D := by
  rcases dir with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact shore_closed D u ud w uw
  rcases shore_closed D u ud w uw with e|e|e
  · exact .inr (.inl e)
  · exact .inl e
  exact .inr (.inr e)

private theorem tight_shell_high_contact (hc : G.Connected)
    {D : Cmp (G:=G) (a:=a) (b:=b)} {c d u : V}
    (dir : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (ports : (portColor D c).card+(secondShore D c).card=5)
    (up : u∈portColor D c) (no : ¬G.Adj d u) (high : 5≤G.degree u) :
    ∀ w∈secondShore D c,G.Adj u w := by
  classical
  let A := portColor D c
  let E := secondShore D c
  obtain ⟨ud,cu⟩ := mem_filter.mp up
  have co : c∉Shore D := by
    rcases dir with ⟨rfl,_⟩|⟨rfl,_⟩
    · exact (shore_off D).1
    exact (shore_off D).2
  have sub : G.neighborFinset u ⊆ insert c (A.erase u∪E) := by
    intro w wm
    have uw := (mem_neighborFinset G _ _).mp wm
    rcases reverse_boundary dir ud uw with rfl|rfl|wd
    · exact mem_insert_self _ _
    · exact (no uw.symm).elim
    apply mem_insert_of_mem
    by_cases cw : G.Adj c w
    · exact mem_union_left _ (mem_erase.mpr ⟨uw.ne.symm,mem_filter.mpr ⟨wd,cw⟩⟩)
    have ne : c≠w := fun e=>co (e.symm ▸ wd)
    exact mem_union_right _ (mem_inter.mpr ⟨wd,d2 hc ne cw cu uw⟩)
  have cap : (insert c (A.erase u∪E)).card≤(G.neighborFinset u).card := by
    have k := card_insert_le c (A.erase u∪E)
    have q := card_union_le (A.erase u) E
    have cnt : (A.erase u).card+E.card≤4 := by
      rw [card_erase_of_mem (show u∈A from up)]
      change A.card+E.card=5 at ports
      have p := card_pos.mpr ⟨u,show u∈A from up⟩
      omega
    rw [card_neighborFinset_eq_degree]
    omega
  have eq := eq_of_subset_of_card_le sub cap
  intro w wm
  exact (mem_neighborFinset G _ _).mp (eq.symm ▸ mem_insert_of_mem (mem_union_right _ wm))

private theorem cross_nonadj {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {u v : V} (uc : u∈Shore C) (vd : v∈Shore D) : ¬G.Adj u v := by
  intro e
  rcases shore_closed C u uc v e with rfl|rfl|vc
  · exact (shore_off D).1 vd
  · exact (shore_off D).2 vd
  exact disjoint_left.mp (shore_disjoint cd) vc vd

private theorem local_d2_plus_foreign_le_five
    (hc : G.Connected) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D) {c u : V}
    (up : u∈portColor D c) :
    (secondShore D u).card+(portColor C c).card≤5 := by
  classical
  obtain ⟨ud,cu⟩ := mem_filter.mp up
  have far : portColor C c ⊆ DistanceTwo G u := by
    intro w wm
    obtain ⟨wc,cw⟩ := mem_filter.mp wm
    have uw : u≠w := fun e=>disjoint_left.mp (shore_disjoint cd) wc (e ▸ ud)
    exact d2 hc uw (fun e=>cross_nonadj cd wc ud e.symm) cu.symm cw
  have dis : Disjoint (secondShore D u) (portColor C c) :=
    (shore_disjoint cd.symm).mono inter_subset_left (filter_subset _ _)
  have h := (card_le_card (union_subset (show secondShore D u ⊆ DistanceTwo G u from inter_subset_right) far)).trans (distanceTwo_le_of_even 5 u (even u))
  rwa [card_union_of_disjoint dis] at h

private theorem nonmixed_shell_nonports
    (hc : G.Connected) (two : G.dist a b=2)
    {D : Cmp (G:=G) (a:=a) (b:=b)}
    (none : ∀ w∈Shore D,¬(G.Adj a w ∧ G.Adj b w))
    (nonmix : ∀ u∈portColor D a,∀ v∈portColor D b,¬G.Adj u v)
    {c d w : V} (dir : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (ws : w∈secondShore D c) : ¬G.Adj a w ∧ ¬G.Adj b w := by
  have cn : ¬G.Adj c w := by
    intro cw
    have eq := (mem_filter.mp (mem_inter.mp ws).2).2
    have val := dist_eq_one_iff_adj.mpr cw
    omega
  have dn : ¬G.Adj d w := by
    intro dw
    obtain ⟨r,rp,rw⟩ := local_shell_comes_from_port hc two
      (dir.elim (fun e=>.inl e.1) (fun e=>.inr e.1)) ws
    have wp : w∈portColor D d := mem_filter.mpr ⟨(mem_inter.mp ws).1,dw⟩
    rcases dir with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact nonmix r rp w wp rw
    exact nonmix w wp r rp rw.symm
  rcases dir with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨cn,dn⟩
  exact ⟨dn,cn⟩

#print axioms tight_shell_high_contact
#print axioms local_d2_plus_foreign_le_five
#print axioms nonmixed_shell_nonports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
