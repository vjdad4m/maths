import DegreeFiveFourForeignGeom189
import DegreeFiveThreeFiveShapes189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget all_adj_of_no_second from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem four_foreign_double_charge_inputs
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (D4 : (cutPorts D).card=4)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    let E := Shore C \ cutPorts C
    let F := Shore D \ cutPorts D
    let A := E.filter (G.Adj x)
    let B := F.filter (fun z=>G.dist x z≠4)
    A.card≤4 ∧ E.card≤A.card+1 ∧
    F.card≤B.card+1 ∧ 2*A.card+B.card≤8 ∧
    (A.card<E.card → B=F) ∧ (A.card=4 → (Shore D).card=4) := by
  classical
  dsimp only
  let E := Shore C \ cutPorts C
  let F := Shore D \ cutPorts D
  let A := E.filter (G.Adj x)
  let B := F.filter (fun z=>G.dist x z≠4)
  let LA := secondShore C a
  let LB := secondShore C b
  let RA := secondShore D a
  let RB := secondShore D b
  let Q := univ.filter (fun z=>G.dist x z=4)
  obtain ⟨⟨_,near⟩,_,budget,dom⟩ := four_foreign_near_with_exception hc two even conn cd cover D4 xc ax bx
  have ad : A⊆LA := by
    intro z az
    obtain ⟨ze,xz⟩ := mem_filter.mp az
    obtain ⟨zc,nP⟩ := mem_sdiff.mp ze
    have n : ¬G.Adj a z := fun h=>nP (mem_filter.mpr ⟨zc,.inl h⟩)
    have ne : a≠z := fun e=>(shore_off C).1 (e.symm ▸ zc)
    exact mem_inter.mpr ⟨zc,d2 hc ne n ax xz⟩
  have bd : A⊆LB := by
    intro z az
    obtain ⟨ze,xz⟩ := mem_filter.mp az
    obtain ⟨zc,nP⟩ := mem_sdiff.mp ze
    have n : ¬G.Adj b z := fun h=>nP (mem_filter.mpr ⟨zc,.inr h⟩)
    have ne : b≠z := fun e=>(shore_off C).2 (e.symm ▸ zc)
    exact mem_inter.mpr ⟨zc,d2 hc ne n bx xz⟩
  have choices : B⊆RA∪RB := by
    intro z bz
    obtain ⟨zf,no4⟩ := mem_filter.mp bz
    obtain ⟨zd,nP⟩ := mem_sdiff.mp zf
    obtain ⟨w,wp,zw⟩ := (dom z zd nP).resolve_left no4
    obtain ⟨_,aw|bw⟩ := mem_filter.mp wp
    · have ne : a≠z := fun e=>(shore_off D).1 (e.symm ▸ zd)
      have n : ¬G.Adj a z := fun h=>nP (mem_filter.mpr ⟨zd,.inl h⟩)
      exact mem_union_left _ (mem_inter.mpr ⟨zd,d2 hc ne n aw zw.symm⟩)
    have ne : b≠z := fun e=>(shore_off D).2 (e.symm ▸ zd)
    have n : ¬G.Adj b z := fun h=>nP (mem_filter.mpr ⟨zd,.inr h⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zd,d2 hc ne n bw zw.symm⟩)
  have eqE : (E\A).card+A.card=E.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have noAdjC : E\A⊆secondShore C x := by
    intro z h
    obtain ⟨ez,na⟩ := mem_sdiff.mp h
    obtain ⟨zc,np⟩ := mem_sdiff.mp ez
    have ne : x≠z := fun e=>np (mem_filter.mpr ⟨zc,.inl (e ▸ ax)⟩)
    have n : ¬G.Adj x z := fun h=>na (mem_filter.mpr ⟨ez,h⟩)
    have lo := hc.one_lt_dist_of_ne_of_not_adj ne n
    have hi := near z zc
    exact mem_inter.mpr ⟨zc,by simp [DistanceTwo,show G.dist x z=2 by omega]⟩
  have neC := card_le_card noAdjC
  have qCap : Q.card+(secondShore C x).card≤1 := budget
  have eqF : (F\B).card+B.card=F.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have exc : F\B⊆Q := by
    intro z h
    obtain ⟨zf,nb⟩ := mem_sdiff.mp h
    have eq : G.dist x z=4 := Classical.byContradiction (fun n=>nb (mem_filter.mpr ⟨zf,n⟩))
    exact mem_filter.mpr ⟨mem_univ _,eq⟩
  have neD := card_le_card exc
  have la := card_le_card ad
  have lb := card_le_card bd
  have rb := (card_le_card choices).trans (card_union_le RA RB)
  have sumA : LA.card+RA.card≤4 :=
    two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have sumB : LB.card+RB.card≤4 :=
    two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ (by rwa [dist_comm]) even
  change A.card≤4 ∧ E.card≤A.card+1 ∧ F.card≤B.card+1 ∧ 2*A.card+B.card≤8 ∧
    (A.card<E.card → B=F) ∧ (A.card=4 → (Shore D).card=4)
  refine ⟨by omega,by omega,by omega,by omega,?_,?_⟩
  · intro h
    exact eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  intro full
  have aOff := (shore_off D).1
  have bOff := (shore_off D).2
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have allA := all_adj_of_no_second hc aOff (shore_hit_a ab conn D)
    (show (secondShore D a).card=0 by change RA.card=0; omega)
  have allB := all_adj_of_no_second hc bOff (shore_hit_b ab conn D)
    (show (secondShore D b).card=0 by change RB.card=0; omega)
  have eq : cutPorts D=Shore D := by
    ext z
    exact ⟨fun h=>(mem_filter.mp h).1,fun h=>mem_filter.mpr ⟨h,.inl (allA z h)⟩⟩
  exact eq ▸ D4

theorem two_four_shore_cardinality_cases
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C2 : (cutPorts C).card=2) (D4 : (cutPorts D).card=4)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    ((Shore C).card=6 ∧ (Shore D).card≤6) ∨
    ((Shore C).card=7 ∧ (Shore D).card=4) := by
  classical
  let E := Shore C \ cutPorts C
  let F := Shore D \ cutPorts D
  let A := E.filter (G.Adj x)
  let B := F.filter (fun z=>G.dist x z≠4)
  have cS : (cutPorts C).card≤(Shore C).card := card_le_card (filter_subset _ _)
  have c4 := four_in_nonsingleton degree (show 2≤(Shore C).card by omega)
  have dS : (cutPorts D).card≤(Shore D).card := card_le_card (filter_subset _ _)
  have cEq : E.card+2=(Shore C).card := by
    have eq : E.card+(cutPorts C).card=(Shore C).card := card_sdiff_add_card_eq_card (filter_subset _ _)
    rwa [C2] at eq
  have dEq : F.card+4=(Shore D).card := by
    have eq : F.card+(cutPorts D).card=(Shore D).card := card_sdiff_add_card_eq_card (filter_subset _ _)
    rwa [D4] at eq
  have c6 : 6≤(Shore C).card := by
    apply Classical.byContradiction
    intro small
    obtain ⟨u,ue,v,ve,uv⟩ := one_lt_card.mp (show 1<E.card by omega)
    obtain ⟨uc,un⟩ := mem_sdiff.mp ue
    obtain ⟨vc,vn⟩ := mem_sdiff.mp ve
    have hu := nonport_degree_bound_small uc un
    have hv := nonport_degree_bound_small vc vn
    exact (degree u v uv).elim (fun h=>by omega) (fun h=>by omega)
  have inputs : A.card≤4 ∧ E.card≤A.card+1 ∧ F.card≤B.card+1 ∧ 2*A.card+B.card≤8 ∧
      (A.card<E.card → B=F) ∧ (A.card=4 → (Shore D).card=4) :=
    four_foreign_double_charge_inputs hc two even conn cd cover D4 xc ax bx
  obtain ⟨ad,ca,db,cap,sat,full⟩ := inputs
  by_cases c7 : (Shore C).card=7
  · exact .inr ⟨c7,full (by omega)⟩
  have csix : (Shore C).card=6 := by omega
  refine .inl ⟨csix,?_⟩
  by_cases h : A.card=4
  · rw [full h]; decide
  have eq := sat (by omega)
  have tally := congrArg Finset.card eq
  omega

#print axioms two_four_shore_cardinality_cases
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
