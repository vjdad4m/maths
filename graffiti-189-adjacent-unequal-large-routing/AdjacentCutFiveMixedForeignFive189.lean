import AdjacentCutFiveMixedSevenEight189
import AdjacentCutFiveTwoTwinGeometry189
import UniversalRouteSingletons189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_closed shore_off shore_connected shore_disjoint shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Vis positive_cap foreign_pos_even from AdjacentCutFiveComponents189
open private d2 mem_positive from AdjacentCutFiveBound189
open private complete_from_no_local_even from AdjacentCutFiveTwoTwinGeometry189
open private MixedRootCases choose_root_cases from AdjacentCutFiveMixedSevenEight189
open private augment_both_one_or_two from AdjacentCutFiveMixedBothTerminals189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev RouteCmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem universal_of_five_spent (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6)
    {D : RouteCmp G a b} {x : V} (xd : x∈Shore D)
    {F : Finset V} (f5 : 5≤F.card) (apart : Disjoint F (Shore D))
    (spent : F⊆PositiveEven G x) :
    ∀ z∈Shore D,z=x ∨ G.Adj x z := by
  classical
  apply complete_from_no_local_even hc xd
  intro z zd zp
  have off : z∉F := fun e=>disjoint_left.mp apart e zd
  have q := card_le_card (insert_subset_iff.mpr ⟨zp,spent⟩ :
    insert z F⊆PositiveEven G x)
  rw [card_insert_of_not_mem off] at q
  have mx := positive_cap x even
  omega

private theorem all_ports_universal_from_five_four (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card≤6) {C D : RouteCmp G a b} (cd : C≠D)
    (c5 : (Shore C).card=5) (allB : ∀ z∈Shore C,G.Adj b z)
    (a4 : 4≤((Shore C).filter (G.Adj a)).card)
    {x : V} (xm : x∈Vis D) : ∀ z∈Shore D,z=x ∨ G.Adj x z := by
  classical
  obtain ⟨xd,p⟩ := mem_filter.mp xm
  by_cases bx : G.Adj b x
  · exact universal_of_five_spent hc even xd (by omega : 5≤(Shore C).card)
      (shore_disjoint cd) (fun _ zc=>foreign_pos_even hc cd.symm xd zc bx (allB _ zc))
  have ax := p.resolve_right bx
  let A := (Shore C).filter (G.Adj a)
  have bo : b∉A := fun h=>(shore_off C).2 (mem_filter.mp h).1
  have apart : Disjoint (insert b A) (Shore D) := by
    apply disjoint_left.mpr
    intro z zm zd
    rcases mem_insert.mp zm with rfl|h
    · exact (shore_off D).2 zd
    · exact disjoint_left.mp (shore_disjoint cd) (mem_filter.mp h).1 zd
  refine universal_of_five_spent hc even xd (F:=insert b A) ?_ apart ?_
  · rw [card_insert_of_not_mem bo]
    change 4≤A.card at a4
    omega
  intro z zm
  rcases mem_insert.mp zm with hz|h
  · rw [hz]
    have xb : x≠b := fun e=>(shore_off D).2 (e ▸ xd)
    have dst := (mem_filter.mp (d2 hc xb (fun e=>bx e.symm) ax.symm ab)).2
    exact mem_positive.mpr ⟨xb.symm,by rw [dst]; decide⟩
  obtain ⟨zc,az⟩ := mem_filter.mp h
  exact foreign_pos_even hc cd.symm xd zc ax az

private theorem rooted_at_universal_ports (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {D : RouteCmp G a b} (d9 : 9≤(Shore D).card)
    (univPort : ∀ x∈Vis D,∀ z∈Shore D,z=x ∨ G.Adj x z)
    {v : V} (vd : v∈Shore D) (bv : G.Adj b v)
    {x : V} (root : x∈Vis D) :
    ∃ t,RouteOn G (Shore D) x t := by
  classical
  let K := Vis D
  let R := Shore D \ K
  have sub : K⊆Shore D := fun _ h=>(mem_filter.mp h).1
  have ksplit : K∪R=Shore D := union_sdiff_of_subset sub
  have kn : Disjoint K R := by
    apply disjoint_left.mpr
    exact fun _ h e=>(mem_sdiff.mp e).2 h
  have kcard := card_sdiff_add_card_eq_card sub
  change R.card+K.card=(Shore D).card at kcard
  have vk : v∈K := mem_filter.mpr ⟨vd,Or.inr bv⟩
  have xk : x∈K := root
  have r5 : R.card≤5 := by
    have small : R⊆PositiveEven G b := by
      intro z zr
      obtain ⟨zd,zk⟩ := mem_sdiff.mp zr
      have bz : ¬G.Adj b z := fun e=>zk (mem_filter.mpr ⟨zd,.inr e⟩)
      have bz' : b≠z := fun e=>(shore_off D).2 (e.symm ▸ zd)
      have vz : v≠z := fun e=>zk (e ▸ vk)
      have edge : G.Adj v z := (univPort v vk z zd).resolve_left vz.symm
      have dst := (mem_filter.mp (d2 hc bz' bz bv edge)).2
      exact mem_positive.mpr ⟨bz'.symm,by rw [dst]; decide⟩
    exact (card_le_card small).trans (positive_cap b even)
  have join : ∀ u∈K,∀ w∈K∪R,u≠w → G.Adj u w := by
    intro u uk w wm neq
    rw [ksplit] at wm
    exact (univPort u uk w wm).resolve_left neq.symm
  by_cases room : R.card≤K.card
  · obtain ⟨t,p,_⟩ := universal_route_from_singletons K R xk kn join room
    exact ⟨t,ksplit ▸ p⟩
  have r : R.card=5 := by omega
  have k : K.card=4 := by omega
  obtain ⟨u,ur,v,vr,uv⟩ := one_lt_card.mp (show 1<R.card by omega)
  have h : ∃ w∈R,5≤G.degree w := by
    rcases degree u v uv with d|d
    · exact ⟨u,ur,d⟩
    exact ⟨v,vr,d⟩
  obtain ⟨u,ur,ud⟩ := h
  obtain ⟨v,vr,uv⟩ : ∃ v∈R,G.Adj u v := by
    by_contra no
    obtain ⟨us,un⟩ := mem_sdiff.mp ur
    have deny (z : V) (zs : z∈Shore D) (zk : z∉K) (e : G.Adj u z) : False :=
      no ⟨z,mem_sdiff.mpr ⟨zs,zk⟩,e⟩
    have s : G.neighborFinset u⊆K := by
      intro z zm
      have e := (mem_neighborFinset G u z).mp zm
      rcases shore_closed D u us z e with rfl|rfl|zs
      · exact (un (mem_filter.mpr ⟨us,.inl e.symm⟩)).elim
      · exact (un (mem_filter.mpr ⟨us,.inr e.symm⟩)).elim
      · by_contra zk
        exact deny z zs zk e
    have p := card_le_card s
    rw [card_neighborFinset_eq_degree] at p
    omega
  let P : Finset V := {u,v}
  have pr : P⊆R := by simpa [P,ur,vr] using
    (insert_subset_iff.mpr ⟨ur,singleton_subset_iff.mpr vr⟩ : ({u,v}:Finset V)⊆R)
  have part := card_sdiff_add_card_eq_card pr
  have p2 : P.card=2 := by simp [P,uv.ne]
  obtain ⟨t,p,_⟩ := universal_route_with_one_block K R P xk
    (by simp [P]) (by simp [P]) kn pr (RouteOn.edge uv) join (by omega)
  exact ⟨t,ksplit ▸ p⟩

/-- A five-vertex shore with full visibility at one terminal and at least four
ports at the other gives a spanning path if the opposite shore has ≥9 vertices. -/
theorem traceable_of_adjacent_five_shore_with_four_common (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : RouteCmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (c5 : (Shore C).card=5) (d9 : 9≤(Shore D).card)
    (allB : ∀ z∈Shore C,G.Adj b z)
    (a4 : 4≤((Shore C).filter (G.Adj a)).card) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have univPort : ∀ x∈Vis D,∀ z∈Shore D,z=x ∨ G.Adj x z :=
    fun _ xm=>all_ports_universal_from_five_four hc ab even cd c5 allB a4 xm
  have run {x y : V} (xy : G.Adj x y) (xo : ∀ K : RouteCmp G a b,x∉Shore K)
      (yo : ∀ K : RouteCmp G a b,y∉Shore K)
      (cov : ∀ {z : V}, z≠x → z≠y → z∈Shore C ∨ z∈Shore D)
      (bd : ∀ u∈Shore C,∀ z,G.Adj u z → z=x ∨ z=y ∨ z∈Shore C)
      (root : MixedRootCases C x) (right : ∃ r∈Vis D,G.Adj y r) :
      ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
    obtain ⟨t,p⟩ := augment_both_one_or_two xy (xo C) (yo C) (by omega) bd root
    obtain ⟨r,rd,yr⟩ := right
    obtain ⟨k,kd,bk⟩ := shore_hit_b ab.ne conn D
    have choose := rooted_at_universal_ports hc even degree d9 univPort kd bk rd
    obtain ⟨s,q⟩ := choose
    have apart : Disjoint (insert y (insert x (Shore C))) (Shore D) := by
      apply disjoint_left.mpr
      intro u um ud
      rcases mem_insert.mp um with rfl|um
      · exact yo D ud
      rcases mem_insert.mp um with rfl|um
      · exact xo D ud
      exact disjoint_left.mp (shore_disjoint cd) um ud
    obtain ⟨w,wp,ws⟩ := p.reverse.join q apart yr
    refine ⟨t,s,w,wp,fun v=>(ws v).mpr ?_⟩
    by_cases e : v=x
    · simp [e]
    by_cases f : v=y
    · simp [f]
    rcases cov e f with h|h <;> simp [h]
  obtain ⟨u,um,au⟩ := shore_hit_a ab.ne conn D
  obtain ⟨v,vm,bv⟩ := shore_hit_b ab.ne conn D
  rcases choose_root_cases ab.ne conn degree (by omega : 2≤(Shore C).card) with h|h
  · exact run ab (fun K=>(shore_off K).1) (fun K=>(shore_off K).2) cover
      (shore_closed C) h ⟨v,mem_filter.mpr ⟨vm,.inr bv⟩,bv⟩
  · exact run ab.symm (fun K=>(shore_off K).2) (fun K=>(shore_off K).1)
      (fun nb na=>cover na nb) (fun u um z uz=>by simpa only [or_left_comm] using shore_closed C u um z uz)
      h ⟨u,mem_filter.mpr ⟨um,.inl au⟩,au⟩

#print axioms traceable_of_adjacent_five_shore_with_four_common
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
