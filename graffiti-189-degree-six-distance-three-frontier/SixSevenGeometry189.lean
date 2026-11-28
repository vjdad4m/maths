import SixTwelveGeometry189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_disjoint shore_off shore_closed shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far shore_inside_five from SixDistanceThreeShort189
open private d2 from CrossSaturation189
open private each_foreign_port_is_distance_two from SixCutHighShore189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open private neighbor_subset_of_dark from SixTenRegular189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (cross_metric shore_swapCut)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}

theorem cut_terminal_high_distance_three (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D) :
    6≤G.degree a := by
  classical
  by_contra! lo
  let P := cutPorts G (Shore C) a
  let Q := cutPorts G (Shore D) a
  let X := cutSeen G (Shore D) a
  obtain ⟨u,uc,au⟩ := shore_hit_a ab conn C
  obtain ⟨v,vd,av⟩ := shore_hit_a ab conn D
  have ua : u≠a := fun e=>(shore_off C).1 (e ▸ uc)
  have highu := (degree a u ua.symm).resolve_left (by omega)
  let L := (inside G (Shore C) u) \ P
  have lcap : 5≤L.card+P.card-1 := by
    have u5 := shore_inside_five far C uc highu
    have hup : u∈P := mem_filter.mpr ⟨uc,au⟩
    have hpos : 0<P.card := card_pos.mpr ⟨u,hup⟩
    have hnu : u∉inside G (Shore C) u := by simp [inside]
    have hi : inside G (Shore C) u ∩ P ⊆ P.erase u := by
      intro z hz
      exact mem_erase.mpr ⟨fun e=>hnu (e ▸ (mem_inter.mp hz).1),(mem_inter.mp hz).2⟩
    have ci := card_le_card hi
    rw [card_erase_of_mem hup] at ci
    have c : L.card+(inside G (Shore C) u ∩ P).card=(inside G (Shore C) u).card := by
      rw [← card_union_of_disjoint (s := L) (t := inside G (Shore C) u∩P)]
      · congr 1
        ext z
        simp [L,mem_sdiff]
        tauto
      · exact disjoint_left.mpr (fun z hz zi=>(mem_sdiff.mp hz).2 (mem_inter.mp zi).2)
    rw [← c] at u5
    change (inside G (Shore C) u ∩ P).card ≤ P.card - 1 at ci
    omega
  have LC : L⊆DistanceTwo G a := by
    intro z hz
    obtain ⟨hn,hP⟩ := mem_sdiff.mp hz
    obtain ⟨zc,uz⟩ := mem_filter.mp hn
    exact d2 hc (fun e=>(shore_off C).1 (e.symm ▸ zc))
      (fun az=>hP (mem_filter.mpr ⟨zc,az⟩)) au uz
  have Lsub : L⊆Shore C := subset_trans sdiff_subset (filter_subset _ _)
  have dis : Disjoint L X := (shore_disjoint cd).mono Lsub inter_subset_left
  have budget := (card_le_card (union_subset LC (show X⊆DistanceTwo G a from inter_subset_right))).trans
    (distanceTwo_le_of_even 6 a (even a))
  rw [card_union_of_disjoint dis] at budget
  have xcap : X.card≤P.card := by omega
  have noab : ¬G.Adj a b := fun h=>by have z := dist_eq_one_iff_adj.mpr h; omega
  have dega : G.degree a=P.card+Q.card := by
    have eq : G.neighborFinset a=P∪Q := by
      ext x
      rw [G.mem_neighborFinset,mem_union]
      constructor
      · intro ax
        have xa : x≠a := ax.ne.symm
        have xb : x≠b := fun e=>noab (e ▸ ax)
        exact (cover xa xb).imp (fun xc=>mem_filter.mpr ⟨xc,ax⟩) (fun xd=>mem_filter.mpr ⟨xd,ax⟩)
      · exact fun e=>e.elim (fun h=>(mem_filter.mp h).2) (fun h=>(mem_filter.mp h).2)
    have dPQ : Disjoint P Q := (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)
    rw [←G.card_neighborFinset_eq_degree,eq,card_union_of_disjoint dPQ]
  have va : v≠a := fun e=>(shore_off D).1 (e ▸ vd)
  have highv := (degree a v va.symm).resolve_left (by omega)
  have sub : G.neighborFinset v⊆insert a ((Q.erase v)∪X) := by
    intro z zn
    have vz := (G.mem_neighborFinset _ _).mp zn
    rcases shore_closed D v vd z vz with rfl|rfl|zD
    · exact mem_insert_self _ _
    · exact (no_common_far far ⟨av,vz.symm⟩).elim
    by_cases az : G.Adj a z
    · exact mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨vz.ne.symm,mem_filter.mpr ⟨zD,az⟩⟩))
    · exact mem_insert_of_mem (mem_union_right _ (visible_of_adj_port hc
        (fun e=>(shore_off D).1 (e ▸ zD)) zD av vz az))
  have d := card_le_card sub
  have d₁ := card_insert_le a ((Q.erase v)∪X)
  have d₂ := card_union_le (Q.erase v) X
  rw [card_erase_of_mem (show v∈Q from mem_filter.mpr ⟨vd,av⟩)] at d₂
  have qpos := card_pos.mpr (show Q.Nonempty from ⟨v,mem_filter.mpr ⟨vd,av⟩⟩)
  rw [G.card_neighborFinset_eq_degree] at d
  omega

open private degree_two_from_one_deletion from AdjacentCutFiveTwinThreeGeom189

theorem shore_inside_one_of_two_connected (far : 3≤G.dist a b)
    (conn : DeletionConnected G) {C : Cmp G a b} {x : V} (xc : x∈Shore C) :
    1≤(inside G (Shore C) x).card := by
  classical
  obtain near|far' : G.Adj a x ∨ ¬G.Adj a x := em _
  · have no : ¬G.Adj x b := fun h=>no_common_far far ⟨near,h.symm⟩
    have low := degree_two_from_one_deletion (u := x) (v := b) conn
      (fun e=>(shore_off C).2 (e ▸ xc)) no
    have ss : G.neighborFinset x⊆insert a (inside G (Shore C) x) := by
      intro y yn
      have h := (G.mem_neighborFinset _ _).mp yn
      rcases shore_closed C x xc y h with rfl|rfl|yc
      · exact mem_insert_self _ _
      · exact (no h).elim
      · exact mem_insert_of_mem (mem_filter.mpr ⟨yc,h⟩)
    have bound := (card_le_card ss).trans (card_insert_le a _)
    rw [G.card_neighborFinset_eq_degree] at bound
    omega
  · have no : ¬G.Adj x a := fun h=>far' h.symm
    have low := degree_two_from_one_deletion (u := x) (v := a) conn
      (fun e=>(shore_off C).1 (e ▸ xc)) no
    have ss : G.neighborFinset x⊆insert b (inside G (Shore C) x) := by
      intro y yn
      have h := (G.mem_neighborFinset _ _).mp yn
      rcases shore_closed C x xc y h with rfl|rfl|yc
      · exact (no h).elim
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_filter.mpr ⟨yc,h⟩)
    have bound := (card_le_card ss).trans (card_insert_le b _)
    rw [G.card_neighborFinset_eq_degree] at bound
    omega

theorem seven_nonedge_to_high_is_distance_two (hc : G.Connected)
    (far : 3≤G.dist a b) (conn : DeletionConnected G)
    {C : Cmp G a b} (seven : (Shore C).card=7) {x y : V}
    (xc : x∈Shore C) (yc : y∈Shore C) (xy : x≠y) (no : ¬G.Adj x y)
    (high : 6≤G.degree x) : y∈DistanceTwo G x := by
  apply nonedge_charge_with_exclusions hc (Shore C) xc yc xy no ∅ (by simp)
  have xl := shore_inside_five far C xc high
  have yl := shore_inside_one_of_two_connected far conn yc
  rw [seven,card_empty]
  omega

/-- Any unseen vertex with a high marked companion is in the third
shell if nonedges to that companion charge the second shell. -/
theorem unseen_dist_three_of_charged_port (hc : G.Connected) {S : Finset V}
    {r x u : V} (xr : x≠r) (xS : x∈S) (ru : G.Adj r u)
    (rx : ¬G.Adj r x) (unseen : G.dist r x≠2)
    (charge : x≠u → ¬G.Adj u x → x∈DistanceTwo G u) :
    G.dist r x=3 := by
  have xu : x≠u := fun e=>rx (e.symm ▸ ru)
  have ux : ¬G.Adj u x := by
    intro h
    have xC := visible_of_adj_port hc xr xS ru h rx
    exact unseen ((mem_cutSeen.mp xC).2)
  have h2 := (mem_cutSeen.mp (show x∈cutSeen G S u from mem_inter.mpr ⟨xS,charge xu ux⟩)).2
  have upper := hc.dist_triangle (u:=r) (v:=u) (w:=x)
  have h1 := dist_eq_one_iff_adj.mpr ru
  have lower := hc.one_lt_dist_of_ne_of_not_adj xr.symm rx
  omega

theorem dark_high_universal_in_seven {C : Cmp G a b}
    (seven : (Shore C).card=7) {x : V} (xc : x∈Shore C)
    (xa : ¬G.Adj a x) (xb : ¬G.Adj b x) (high : 6≤G.degree x) :
    ∀ y∈Shore C, y≠x → G.Adj x y := by
  have h := dark_inside_six xc xa xb high
  have eq : inside G (Shore C) x=(Shore C).erase x := by
    refine eq_of_subset_of_card_le (inside_subset_erase _ _) ?_
    rw [card_erase_of_mem xc,seven]
    exact h
  intro y yc ne
  have j : y∈inside G (Shore C) x := by
    rw [eq]
    exact mem_erase.mpr ⟨ne,yc⟩
  exact (mem_filter.mp j).2

theorem hidden_dark_not_high_of_dark_card (hc : G.Connected)
    {D : Cmp G a b} (atMost : ((Shore D) \ (cutPorts G (Shore D) a∪cutPorts G (Shore D) b)).card≤6)
    {x : V} (xd : x∈Shore D) (xa : ¬G.Adj a x) (xb : ¬G.Adj b x)
    (na : G.dist a x≠2) (nb : G.dist b x≠2) : G.degree x<6 := by
  let S := (Shore D) \ (cutPorts G (Shore D) a∪cutPorts G (Shore D) b)
  have xm : x∈S := by simp [S,cutPorts,xd,xa,xb]
  have xane : x≠a := fun e=>(shore_off D).1 (e ▸ xd)
  have xbne : x≠b := fun e=>(shore_off D).2 (e ▸ xd)
  have h : G.neighborFinset x⊆S.erase x := by
    intro y hy
    have xy := (G.mem_neighborFinset _ _).mp hy
    rcases shore_closed D x xd y xy with rfl|rfl|yd
    · exact (xa xy.symm).elim
    · exact (xb xy.symm).elim
    have ya : ¬G.Adj a y := fun ay=>na ((mem_cutSeen.mp
      (visible_of_adj_port hc xane xd ay xy.symm xa)).2)
    have yb : ¬G.Adj b y := fun by'=>nb ((mem_cutSeen.mp
      (visible_of_adj_port hc xbne xd by' xy.symm xb)).2)
    exact mem_erase.mpr ⟨xy.ne.symm,by simp [S,cutPorts,yd,ya,yb]⟩
  have e := card_le_card h
  rw [card_erase_of_mem xm,G.card_neighborFinset_eq_degree] at e
  change S.card≤6 at atMost
  omega

#print axioms dark_high_universal_in_seven
#print axioms hidden_dark_not_high_of_dark_card
#print axioms unseen_dist_three_of_charged_port
#print axioms seven_nonedge_to_high_is_distance_two
#print axioms cut_terminal_high_distance_three
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
