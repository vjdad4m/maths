import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveExclusiveGateway189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_disjoint from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor foreign_exclusive_subset_at_port universal_if_no_own_second from DegreeFiveThreeForeignImpossible189
open private boundary_permuted walk_three_data from DegreeFiveExclusiveGateway189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem exclusive_four_local_gateway
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {c d u : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (cu : G.Adj c u) (uD : u∈Shore D) (du : ¬G.Adj d u)
    (noMixed : ∀ z∈Shore D, G.Adj d z → ¬G.Adj u z)
    (hit : ∃ z∈Shore D,G.Adj d z)
    (four : (portColor C c).card=4) :
    ∃ q∈Shore D,secondShore D u={q} ∧
      (∀ z∈Shore D,z≠u → ¬G.Adj u z → z≠q → G.Adj q z) := by
  classical
  let Q := secondShore D u
  let F := portColor C c
  have ct : c=a ∨ c=b := perm.elim (fun e=>.inl e.1) (fun e=>.inr e.1)
  have dist : G.dist c d=2 := by
    rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact two
    rwa [SimpleGraph.dist_comm]
  have noCut : ¬G.Adj c d := by intro e; have := dist_eq_one_iff_adj.mpr e; omega
  obtain ⟨v,vD,dv⟩ := hit
  have nonzero : 0<Q.card := by
    apply Classical.byContradiction
    intro h
    have z : Q.card=0 := by omega
    have all := universal_if_no_own_second hc uD z
    exact (all v vD).elim (fun e=>du (e ▸ dv)) (noMixed v vD dv)
  have dis : Disjoint Q F := (shore_disjoint cd.symm).mono inter_subset_left (filter_subset _ _)
  have foreign : F⊆DistanceTwo G u := foreign_exclusive_subset_at_port hc cd ct uD cu
  have sub : Q∪F⊆DistanceTwo G u := union_subset inter_subset_right foreign
  have h := card_le_card sub
  rw [card_union_of_disjoint dis] at h
  change F.card=4 at four
  have cap := distanceTwo_le_of_even 5 u (even u)
  have q1 : Q.card=1 := by omega
  obtain ⟨q,qq⟩ := card_eq_one.mp q1
  have qD : q∈Shore D := (mem_inter.mp (show q∈Q by simp [qq])).1
  have rad (z : V) : G.dist u z≤3 := by
    apply Classical.byContradiction
    intro no
    have far : 4≤G.dist u z := by omega
    have lo := distanceTwo_add_two_le_even_of_far hc far
    have prev := even u
    omega
  refine ⟨q,qD,qq,?_⟩
  intro z zD zu uz zq
  have not2 : z∉DistanceTwo G u := by
    intro zz
    have zQ : z∈Q := mem_inter.mpr ⟨zD,zz⟩
    exact zq (by simpa [qq] using zQ)
  have pos := hc.one_lt_dist_of_ne_of_not_adj zu.symm uz
  have three := rad z
  have dz : G.dist u z=3 := by
    by_cases d2 : G.dist u z=2
    · exact (not2 (by simp [DistanceTwo,d2])).elim
    omega
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist u z
  obtain ⟨i,j,ui,ij,jz⟩ := walk_three_data p (pl.trans dz)
  have jD : j∈Shore D := by
    rcases boundary_permuted perm z zD j jz.symm with rfl|rfl|jD
    · have w := G.dist_le (Walk.cons cu.symm (Walk.cons jz .nil))
      simp at w
      omega
    · rcases boundary_permuted perm u uD i ui with rfl|rfl|iD
      · exact (noCut ij).elim
      · exact (du ui.symm).elim
      exact (noMixed i iD ij.symm ui).elim
    exact jD
  have jq : j∈Q := by
    have uj : ¬G.Adj u j := by
      intro e
      have w := G.dist_le (Walk.cons e (Walk.cons jz .nil))
      simp at w
      omega
    have jne : u≠j := fun e=>uz (e.symm ▸ jz)
    exact mem_inter.mpr ⟨jD,d2 hc jne uj ui ij⟩
  have e : j=q := by simpa [qq] using jq
  exact e ▸ jz

#print axioms exclusive_four_local_gateway
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
