import DegreeFiveFourUniversalTerminal189
import DegreeFiveNearSmallRoot189
import DegreeFiveBothFourFiveFifteen189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem shores_add_two_le_graph_order {C D : Cmp (G:=G) (a:=a) (b:=b)}
    (ab : a≠b) (cd : C≠D) :
    (Shore C).card+(Shore D).card+2≤Fintype.card V := by
  classical
  let U := Shore C∪Shore D
  have ao : a∉U := fun h=>(mem_union.mp h).elim (shore_off C).1 (shore_off D).1
  have bo : b∉U := fun h=>(mem_union.mp h).elim (shore_off C).2 (shore_off D).2
  have k := card_le_card (subset_univ (insert a (insert b U)))
  rw [card_univ,card_insert_of_not_mem (by simpa [ab] using ao),
    card_insert_of_not_mem bo] at k
  change (Shore C∪Shore D).card+1+1≤Fintype.card V at k
  rwa [card_union_of_disjoint (shore_disjoint cd),Nat.add_assoc] at k

/-- Top-order 4+5 both-common profile: the four-port wing is terminal;
the five-port wing supplies both free masks, in the original graph. -/
theorem four_five_order_fifteen_masks
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : (cutPorts C).card=4) (D5 : (cutPorts D).card=5)
    (n : Fintype.card V=15)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    WingRealizes G a b (Shore C) .terminal ∧ WingRealizes G a b (Shore D) .aFree ∧
      WingRealizes G a b (Shore D) .bFree := by
  classical
  obtain ⟨pure,dA,dB⟩ := order_fifteen_four_five_contact_constraints hc two even conn
    cd cover C4 D5 (le_of_eq n.symm) xc ax bx yd ay by'
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have sum := shores_add_two_le_graph_order ab cd
  have c4 : 4≤(Shore C).card := by rw [←C4]; exact card_le_card (filter_subset _ _)
  have d5 : 5≤(Shore D).card := by rw [←D5]; exact card_le_card (filter_subset _ _)
  have cUniv (u : V) (uk : u∈sharedPortSet C) : ∀ w∈Shore C,u≠w → G.Adj u w := by
    obtain ⟨uc,au,bu⟩ := mem_filter.mp uk
    exact common_universal_in_shore_at_five hc even cd uc au bu D5
  have cross {u v : V} (uc : u∈Shore C) (vd : v∈Shore D) : ¬G.Adj u v := by
    intro e
    rcases shore_closed C u uc v e with rfl|rfl|vC
    · exact (shore_off D).1 vd
    · exact (shore_off D).2 vd
    exact disjoint_left.mp (shore_disjoint cd) vC vd
  let T : Split G a b := ⟨Shore D,Shore C,shore_disjoint cd.symm,shore_off D,shore_off C,
    shore_connected D,(fun _ vd _ uc e=>cross uc vd e.symm),shore_hit_a ab conn D,shore_hit_b ab conn D,
    (fun z=>(cover z).imp id (fun h=>h.imp id Or.symm))⟩
  have near (u : V) (uk : u∈sharedPortSet D) :
      (secondShore D u).card≤1 ∧ ∀ w∈Shore D,G.dist u w≤2 := by
    obtain ⟨ud,au,bu⟩ := mem_filter.mp uk
    exact Split.Five.near_universal_at_four_foreign T hc even conn ud au bu (le_of_eq C4.symm)
  have tally : (portColor D a).card+(portColor D b).card=(cutPorts D).card+(sharedPortSet D).card := by
    have u : portColor D a∪portColor D b=cutPorts D := by ext w; simp [portColor,cutPorts,and_or_left]
    have i : portColor D a∩portColor D b=sharedPortSet D := by
      ext w; simp [portColor,sharedPortSet,and_assoc,and_left_comm]
    rw [←u,←i,card_union_add_card_inter]
  have dK : 3≤(sharedPortSet D).card := by omega
  obtain ⟨r,rk,t,path⟩ := common_rooted_of_small_near_universal_shore hc degree d5 (by omega)
    (le_of_eq D5) dK near
  obtain ⟨rd,ar,br⟩ := mem_filter.mp rk
  exact ⟨terminal_mask_at_four_universal_common_ports degree C4 pure (by omega) cUniv,
    ⟨r,t,ar,path⟩,⟨r,t,br,path⟩⟩

theorem traceable_of_four_five_order_fifteen
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : (cutPorts C).card=4) (D5 : (cutPorts D).card=5)
    (n : Fintype.card V=15)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  obtain ⟨tc,ra,rb⟩ := four_five_order_fifteen_masks hc two even conn degree
    cd cover C4 D5 n xc ax bx yd ay by'
  exact traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
    (shore_off D).1 (shore_off D).2 cover (.inl ⟨tc,.inl ra⟩)

#print axioms four_five_order_fifteen_masks
#print axioms traceable_of_four_five_order_fifteen
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
