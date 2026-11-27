import DegreeFiveRouteBasic189
import DegreeFiveUniquePortClosureTest189
import DegreeFiveActualCut189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open ArticulationPair
open private left_boundary from AdjacentCut189
open private lift_side_path from DegreeFiveSmallSides189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Split G a b)
set_option linter.unusedSectionVars false

private theorem inside_at_least_three_at_high {u : V} (ul : u∈S.L)
    (high : 5≤G.degree u) : 3≤(inside G S.L u).card := by
  classical
  let N := inside G S.L u
  have sub : G.neighborFinset u⊆insert a (insert b N) := by
    intro v vm
    have e := (mem_neighborFinset G u v).mp vm
    rcases left_boundary S u ul v e with rfl|rfl|vl
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_self _ _)
    exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨vl,e⟩))
  have h := card_le_card sub
  rw [card_neighborFinset_eq_degree] at h
  have c := card_insert_le a (insert b N)
  have d := card_insert_le b N
  change 3≤N.card
  omega

private theorem inside_at_least_four_at_exclusive_high {u : V} (ul : u∈S.L)
    (exclusive : ¬(G.Adj a u ∧ G.Adj b u))
    (high : 5≤G.degree u) : 4≤(inside G S.L u).card := by
  classical
  let N := inside G S.L u
  have one (c d : V) (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a)) (nd : ¬G.Adj d u) :
      G.neighborFinset u⊆insert c N := by
    intro v vm
    have uv := (mem_neighborFinset G u v).mp vm
    have e : v=c ∨ v=d ∨ v∈S.L := by
      rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact left_boundary S u ul v uv
      rcases left_boundary S u ul v uv with h|h|h
      · exact .inr (.inl h)
      · exact .inl h
      exact .inr (.inr h)
    rcases e with rfl|rfl|vl
    · exact mem_insert_self _ _
    · exact (nd uv.symm).elim
    exact mem_insert_of_mem (mem_filter.mpr ⟨vl,uv⟩)
  have bound (c : V) (sub : G.neighborFinset u⊆insert c N) : 4≤N.card := by
    have h := (card_le_card sub).trans (card_insert_le c N)
    rw [card_neighborFinset_eq_degree] at h
    omega
  by_cases au : G.Adj a u
  · exact bound a (one a b (.inl ⟨rfl,rfl⟩) (fun bu=>exclusive ⟨au,bu⟩))
  exact bound b (one b a (.inr ⟨rfl,rfl⟩) au)

theorem root_any_vertex_of_high_shore_with_one_common
    (small : S.L.card≤8)
    (high : ∀ u∈S.L,5≤G.degree u)
    {x : V} (xL : x∈S.L) (unique : ∀ z∈S.L,G.Adj a z → G.Adj b z → z=x)
    {z : V} (zl : z∈S.L) :
    ∃ t,RouteOn G S.L z t := by
  classical
  let U := ↑(↑S.L : Set V)
  let J := G.induce (↑S.L : Set V)
  let xx : U := ⟨x,xL⟩
  let zz : U := ⟨z,zl⟩
  let A : Finset U := univ.erase xx
  let K := completeWith J A
  have count : Fintype.card U≤8 := by
    change Fintype.card {v : V // v∈S.L}≤8
    rwa [Fintype.card_coe]
  have clique : CompleteOn K A := completeWith_of_mem J A
  have ge (v : U) (va : v∈A) : 4≤J.degree v := by
    have e := inside_card_eq_degree_induce (G:=G) S.L v
    rw [←e]
    apply inside_at_least_four_at_exclusive_high S v.property _ (high _ v.property)
    intro hv
    apply (mem_erase.mp va).1
    exact Subtype.ext (unique _ v.property hv.1 hv.2)
  have sum (u : U) (ua : u∈A) (v : U) (va : v∈A) :
      Fintype.card U≤J.degree u+J.degree v := by
    have g1 := ge u ua
    have g2 := ge v va
    omega
  let ore : RootedClosureAPI := by
    intro W _ _ J' K' _ _ sub root hdeg hp
    exact Graffiti189Ore.rooted_closure sub root hdeg hp
  have min : 3≤J.degree xx := by
    have e := inside_card_eq_degree_induce (G:=G) S.L xx
    change 3≤(G.induce (↑S.L : Set V)).degree xx
    rw [←e]
    exact inside_at_least_three_at_high S xL (high x xL)
  have good : ∃ w : U, J.Adj xx w ∧ w≠zz := by
    apply Classical.byContradiction
    intro no
    have sub : J.neighborFinset xx ⊆ {zz} := by
      intro w wh
      apply mem_singleton.mpr
      apply Classical.byContradiction
      intro e
      exact no ⟨w,(mem_neighborFinset J xx w).mp wh,e⟩
    have h := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_singleton] at h
    omega
  obtain ⟨w,xw,wz⟩ := good
  have path : RootedSpan J zz := by
    refine close_completed_class ore A zz sum ?_
    have wx : w≠xx := xw.ne.symm
    have adj := completeWith_mono J A xw
    by_cases h : zz=xx
    · rw [h]
      exact rooted_path_from_root_into_clique K adj clique
    exact rooted_path_of_clique_and_outlier K h wx (Ne.symm wz) adj.symm clique
  obtain ⟨t,p,pp,ps⟩ := path
  obtain ⟨q,qp,qs⟩ := lift_side_path S.L p pp ps
  exact ⟨t.val,q,qp,qs⟩

theorem traceable_unique_common_test_of_high_shores (hc : G.Connected)
    (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (rightConn : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ u∈S.R,G.Adj a u) (rightB : ∃ u∈S.R,G.Adj b u)
    {x : V} (xL : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (one : (CommonPorts G a b).card=1)
    (test : Fintype.card V-2≤G.degree a+G.degree b)
    (high : ∀ z,z∈S.L ∨ z∈S.R → 5≤G.degree z) :
    ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let T := switch S rightConn rightA rightB
  have n15 := order_le_fifteen_of_unique_common_closure_test S hc two even
    rightConn rightA rightB xL ax bx one test
  have maxInner := (degree_sum_threshold_iff_at_unique_common two one).mp test
  have unique {z : V} (az : G.Adj a z) (bz : G.Adj b z) : z=x := by
    have xm : x∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a x).mpr ax,(mem_neighborFinset G b x).mpr bx⟩
    have zm : z∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a z).mpr az,(mem_neighborFinset G b z).mpr bz⟩
    exact card_le_one.mp one.le z zm x xm
  have none {z : V} (zr : z∈S.R) : ¬(G.Adj a z ∧ G.Adj b z) := by
    intro h
    exact disjoint_left.mp S.dis xL (unique h.1 h.2 ▸ zr)
  have r5 : 5≤S.R.card := by
    obtain ⟨u,ur,au⟩ := rightA
    have h := inside_at_least_four_at_exclusive_high T ur (none ur) (high _ (.inr ur))
    have sub : inside G S.R u ⊆ S.R.erase u := by
      intro v vm
      obtain ⟨vr,uv⟩ := mem_filter.mp vm
      exact mem_erase.mpr ⟨uv.ne.symm,vr⟩
    have k := card_le_card sub
    rw [card_erase_of_mem ur] at k
    change 4≤(inside G S.R u).card at h
    omega
  have sizeL : S.L.card≤8 := by
    have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
    have aa : a∉S.L∪S.R := by simp [S.leftOff.1,S.rightOff.1]
    have bb : b∉S.L∪S.R := by simp [S.leftOff.2,S.rightOff.2]
    have nb : a∉insert b (S.L∪S.R) := by simp [ab,aa]
    have c := card_le_univ (insert a (insert b (S.L∪S.R)))
    rw [card_insert_of_not_mem nb,card_insert_of_not_mem bb,card_union_of_disjoint S.dis] at c
    omega
  have sizeR : S.R.card≤6 := by
    have fl : S.foreignPorts⊆DistanceTwo G x := by
      intro z zp
      obtain ⟨zr,az|bz⟩ := mem_filter.mp zp
      all_goals
        have ne : x≠z := fun e=>disjoint_left.mp S.dis xL (e.symm ▸ zr)
        have no := S.cross x xL z zr
      · exact d2 hc ne no ax.symm az
      exact d2 hc ne no bx.symm bz
    have fc := (card_le_card fl).trans (distanceTwo_le_of_even 5 x (even x))
    have sub : S.R ⊆ S.foreignPorts∪Nonports G a b := by
      intro z zr
      by_cases h : G.Adj a z ∨ G.Adj b z
      · exact mem_union_left _ (mem_filter.mpr ⟨zr,h⟩)
      apply mem_union_right
      apply mem_sdiff.mpr
      refine ⟨mem_erase.mpr ⟨fun e=>S.rightOff.2 (e ▸ zr),
        mem_erase.mpr ⟨fun e=>S.rightOff.1 (e ▸ zr),mem_univ _⟩⟩,?_⟩
      intro nm
      exact h ((mem_union.mp nm).imp ((mem_neighborFinset G a z).mp) ((mem_neighborFinset G b z).mp))
    have c := (card_le_card sub).trans (card_union_le S.foreignPorts (Nonports G a b))
    omega
  obtain ⟨u,ur,au⟩ := rightA
  obtain ⟨v,vr,bv⟩ := rightB
  have uv : u≠v := fun e=>none ur ⟨au,e.symm ▸ bv⟩
  let U := ↑(↑S.R : Set V)
  let J := G.induce (↑S.R : Set V)
  let uu : U := ⟨u,ur⟩
  let vv : U := ⟨v,vr⟩
  have cnt : Fintype.card U≤6 := by
    change Fintype.card {w : V // w∈S.R}≤6
    rwa [Fintype.card_coe]
  have inner4 (w : U) : 4≤J.degree w := by
    rw [←inside_card_eq_degree_induce (G:=G) S.R w]
    exact inside_at_least_four_at_exclusive_high T w.property (none w.property)
      (high _ (.inr w.property))
  have h := hamilton_connected_of_ore
    (G:=J) (by
      intro y z _ _
      change Fintype.card U + 1 ≤ J.degree y + J.degree z
      have a := inner4 y
      have b := inner4 z
      omega)
    (show uu≠vv from fun e=>uv (congrArg Subtype.val e))
  obtain ⟨p,pp,ps⟩ := h
  obtain ⟨qr,qpr,qs⟩ := lift_side_path S.R p pp ps
  have m : RouteOn G ((insert a (insert b S.R))) a b := by
    have q : RouteOn G S.R u v := ⟨qr,qpr,qs⟩
    have r := q.suffix bv.symm S.rightOff.2
    exact r.prefix au (by simp [S.rightOff.1,show a≠b by
      intro e; rw [e,SimpleGraph.dist_self] at two; omega])
  obtain ⟨w,l⟩ := root_any_vertex_of_high_shore_with_one_common S sizeL
    (fun z zl=>high z (.inl zl)) xL (fun z _ az bz=>unique az bz) xL
  have all := m.reverse.join l
    (by apply disjoint_left.mpr; intro z zm zl; simp only [mem_insert] at zm;
        rcases zm with rfl|rfl|zr
        · exact S.leftOff.1 zl
        · exact S.leftOff.2 zl
        exact disjoint_left.mp S.dis zl zr)
    ax
  obtain ⟨p,pp,ps⟩ := all
  refine ⟨b,w,p,pp,fun z=>(ps z).mpr ?_⟩
  rcases S.cover z with rfl|rfl|zl|zr
  · simp
  · simp
  · exact mem_union_right _ zl
  exact mem_union_left _ (mem_insert_of_mem (mem_insert_of_mem zr))

#print axioms root_any_vertex_of_high_shore_with_one_common
#print axioms traceable_unique_common_test_of_high_shores
end Graffiti189LongestPath.CrossSaturation.Split.Five

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem traceable_of_actual_unique_common_test_without_exception {a b : V}
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (comp : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2)
    (one : (CommonPorts G a b).card=1)
    (test : Fintype.card V-2≤G.degree a+G.degree b)
    (high : ∀ z : V,z≠a → z≠b → 5≤G.degree z) :
    ∃ u v : V,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent=2 at comp
  rw [Nat.card_eq_fintype_card] at comp
  have ab : a≠b := by intro eq; rw [eq,SimpleGraph.dist_self] at two; omega
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨x,ax,xb⟩ := two_walk_middle p (pl.trans two)
  let C := J.connectedComponentMk ⟨x,ax.ne.symm,xb.ne⟩
  have xC : x∈Shore C := mem_shore.mpr ⟨⟨ax.ne.symm,xb.ne⟩,rfl⟩
  let T := (univ : Finset J.ConnectedComponent).erase C
  have tc : T.card=1 := by
    dsimp [T]
    rw [card_erase_of_mem (mem_univ _),card_univ,comp]
  obtain ⟨D,hD⟩ := card_eq_one.mp tc
  have dt : D∈T := by simp [hD]
  have DC : D≠C := (mem_erase.mp dt).1
  have dis : Disjoint (Shore C) (Shore D) := shore_disjoint DC.symm
  have cover (u : V) : u=a ∨ u=b ∨ u∈Shore C ∨ u∈Shore D := by
    by_cases ua : u=a
    · exact .inl ua
    by_cases ub : u=b
    · exact .inr (.inl ub)
    let E := J.connectedComponentMk ⟨u,ua,ub⟩
    have eu : u∈Shore E := mem_shore.mpr ⟨⟨ua,ub⟩,rfl⟩
    by_cases ec : E=C
    · exact .inr (.inr (.inl (ec ▸ eu)))
    have et : E∈T := mem_erase.mpr ⟨ec,mem_univ _⟩
    rw [hD] at et
    exact .inr (.inr (.inr (mem_singleton.mp et ▸ eu)))
  have cross (u : V) (uC : u∈Shore C) (v : V) (vD : v∈Shore D) : ¬G.Adj u v := by
    intro uv
    rcases shore_closed C u uC v uv with rfl|rfl|vC
    · exact (shore_off D).1 vD
    · exact (shore_off D).2 vD
    exact disjoint_left.mp dis vC vD
  let S : Split G a b :=
    ⟨Shore C,Shore D,dis,shore_off C,shore_off D,shore_connected C,cross,
      shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  exact Split.Five.traceable_unique_common_test_of_high_shores S hc two even
    (shore_connected D) (shore_hit_a ab conn D) (shore_hit_b ab conn D)
    xC ax xb.symm one test (fun z h=>by
      rcases h with zL|zR
      · exact high z (fun e=>S.leftOff.1 (e ▸ zL)) (fun e=>S.leftOff.2 (e ▸ zL))
      exact high z (fun e=>S.rightOff.1 (e ▸ zR)) (fun e=>S.rightOff.2 (e ▸ zR)))

#print axioms traceable_of_actual_unique_common_test_without_exception
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
