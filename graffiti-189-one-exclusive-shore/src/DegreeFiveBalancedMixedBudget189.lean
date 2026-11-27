import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveThreeForeignImpossible189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget from DegreeFiveThreeForeignImpossible189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private noncomputable def mixedPorters (D : Cmp (G:=G) (a:=a) (b:=b)) (c d : V) : Finset V := by
  classical
  exact (Shore D).filter (fun z=>G.Adj d z ∧ ∃ w∈Shore D,G.Adj c w ∧ G.Adj z w)

/-- High mixed-contact counts and charges in the common shore take away
slots from the exclusive shore's possible nonport vertices. -/
theorem exclusive_shore_order_add_mixed_add_charges_le_thirteen
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (four : 4≤(cutPorts D).card) :
    (Shore D).card + ((mixedPorters D a b).card+(mixedPorters D b a).card) +
        ((secondShore C a).card+(secondShore C b).card)≤13 := by
  classical
  let P := cutPorts D
  let A := secondShore D a
  let B := secondShore D b
  let W := Shell G x 4
  let Ma := mixedPorters D a b
  let Mb := mixedPorters D b a
  have off {z : V} (zd : z∈Shore D) : z∉Shore C :=
    disjoint_left.mp (shore_disjoint cd.symm) zd
  have foreign : P⊆DistanceTwo G x := by
    intro z zm
    obtain ⟨zd,h⟩ := mem_filter.mp zm
    have nz : x≠z := fun e=>off zd (e ▸ xC)
    have no : ¬G.Adj x z := by
      intro e
      rcases shore_closed C x xC z e with rfl|rfl|zc
      · exact (shore_off D).1 zd
      · exact (shore_off D).2 zd
      exact off zd zc
    exact h.elim (fun az=>d2 hc nz no ax.symm az) (fun bz=>d2 hc nz no bx.symm bz)
  have pcap := card_le_card foreign
  have budget := shell_two_four_le_of_even (x:=x) (d:=5) (even x)
  rw [shell_two] at budget
  change (DistanceTwo G x).card+W.card≤5 at budget
  change 4≤P.card at four
  have rad (z : V) : G.dist x z≤4 := by
    apply Classical.byContradiction
    intro no
    have f : 4<G.dist x z := by omega
    have k := shell_card_of_far hc 2 conn (i:=4) (by decide) f
    change 2≤W.card at k
    omega
  have cover : Shore D⊆P∪(A\P)∪(B\P)∪W := by
    intro z zd
    by_cases zp : z∈P
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ zp))
    by_cases d4 : G.dist x z=4
    · exact mem_union_right _ (mem_shell.mpr d4)
    have noA : ¬G.Adj a z := fun h=>zp (mem_filter.mpr ⟨zd,.inl h⟩)
    have noB : ¬G.Adj b z := fun h=>zp (mem_filter.mpr ⟨zd,.inr h⟩)
    have loA := hc.one_lt_dist_of_ne_of_not_adj (show a≠z from fun e=>(shore_off D).1 (e.symm ▸ zd)) noA
    have loB := hc.one_lt_dist_of_ne_of_not_adj (show b≠z from fun e=>(shore_off D).2 (e.symm ▸ zd)) noB
    have dx := rad z
    have cross := cross_metric (Shore C) hc xC (off zd) (shore_closed C)
    rw [dist_eq_one_iff_adj.mpr ax.symm,dist_eq_one_iff_adj.mpr bx.symm] at cross
    have near : G.dist a z=2 ∨ G.dist b z=2 := by omega
    rcases near with h|h
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _
        (mem_sdiff.mpr ⟨mem_inter.mpr ⟨zd,by simp [DistanceTwo,h]⟩,zp⟩)))
    exact mem_union_left _ (mem_union_right _
      (mem_sdiff.mpr ⟨mem_inter.mpr ⟨zd,by simp [DistanceTwo,h]⟩,zp⟩))
  have mA : Ma⊆A∩P := by
    intro z zm
    obtain ⟨zd,bz,w,wd,aw,zw⟩ := mem_filter.mp zm
    have h := d2 hc (show a≠z from fun e=>(shore_off D).1 (e.symm ▸ zd))
      (fun az=>none z zd ⟨az,bz⟩) aw zw.symm
    exact mem_inter.mpr ⟨mem_inter.mpr ⟨zd,h⟩,mem_filter.mpr ⟨zd,.inr bz⟩⟩
  have mB : Mb⊆B∩P := by
    intro z zm
    obtain ⟨zd,az,w,wd,bw,zw⟩ := mem_filter.mp zm
    have h := d2 hc (show b≠z from fun e=>(shore_off D).2 (e.symm ▸ zd))
      (fun bz=>none z zd ⟨az,bz⟩) bw zw.symm
    exact mem_inter.mpr ⟨mem_inter.mpr ⟨zd,h⟩,mem_filter.mpr ⟨zd,.inl az⟩⟩
  have mAs := card_le_card mA
  have mBs := card_le_card mB
  have eA : (A\P).card+(A∩P).card=A.card := by
    have e := card_sdiff_add_card_eq_card (s:=A∩P) (t:=A) inter_subset_left
    have eq : A\(A∩P)=A\P := by ext z; simp [and_assoc]
    rwa [eq] at e
  have eB : (B\P).card+(B∩P).card=B.card := by
    have e := card_sdiff_add_card_eq_card (s:=B∩P) (t:=B) inter_subset_left
    have eq : B\(B∩P)=B\P := by ext z; simp [and_assoc]
    rwa [eq] at e
  have rev : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have aCap := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have bCap := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ rev even
  change _+A.card≤4 at aCap
  change _+B.card≤4 at bCap
  have u := (card_le_card cover).trans (card_union_le (P∪(A\P)∪(B\P)) W)
  have v := card_union_le (P∪(A\P)) (B\P)
  have w := card_union_le P (A\P)
  change _+(Ma.card+Mb.card)+_≤13
  omega

#print axioms exclusive_shore_order_add_mixed_add_charges_le_thirteen
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
