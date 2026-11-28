import AdjacentCutFiveSingletonGeometry189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_closed shore_nonempty shore_connected
  shore_hit_a shore_hit_b shore_disjoint from AdjacentCutFiveActual189
open private Vis vis_sub vis_card_ge_two degree_le_shore positive_cap foreign_pos_even
  from AdjacentCutFiveComponents189
open private mem_positive d2 from AdjacentCutFiveBound189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp := (CutGraph (G:=G) a b).ConnectedComponent

private theorem complete_from_no_local_even (hc : G.Connected)
    {C : Cmp (G:=G) (a:=a) (b:=b)} {x : V} (xc : x∈Shore C)
    (ban : ∀ y∈Shore C, y∉PositiveEven G x) :
    ∀ y∈Shore C, y=x ∨ G.Adj x y := by
  classical
  intro y yc
  let H := G.induce (↑(Shore C) : Set V)
  let s : (↑(Shore C) : Set V) := ⟨x,xc⟩
  let t : (↑(Shore C) : Set V) := ⟨y,yc⟩
  have closed {u v : ↑(↑(Shore C) : Set V)} (uv : H.Adj u v)
      (mark : u.val=x ∨ G.Adj x u.val) : v.val=x ∨ G.Adj x v.val := by
    have ev : G.Adj u.val v.val := uv
    rcases mark with e | e
    · exact .inr (by simpa only [e] using ev)
    · by_cases vx : v.val=x
      · exact .inl vx
      · right
        by_contra no
        have D2 := d2 hc (Ne.symm vx) no e ev
        exact ban v.val v.property (mem_positive.mpr ⟨vx,by simp [(mem_filter.mp D2).2]⟩)
  have prop {u v : ↑(↑(Shore C) : Set V)} (q : H.Walk u v)
      (f : u.val=x ∨ G.Adj x u.val) : v.val=x ∨ G.Adj x v.val := by
    induction q with
    | nil => exact f
    | cons e q ih => exact ih (closed e f)
  obtain ⟨p⟩ := (shore_connected C).preconnected s t
  exact prop p (.inl rfl)

private theorem size_four_common
    {D : Cmp (G:=G) (a:=a) (b:=b)} (four : (Shore D).card=4)
    (high : ∀ z∈Shore D,5≤G.degree z) :
    ∀ z∈Shore D,G.Adj a z ∧ G.Adj b z := by
  intro z zd
  have h := high z zd
  constructor
  · by_contra no
    have q := degree_le_shore D zd (.inl no)
    omega
  · by_contra no
    have q := degree_le_shore D zd (.inr no)
    omega

private theorem foreign_quota_from_four_common (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6)
    {D C E : Cmp (G:=G) (a:=a) (b:=b)} (dc : D≠C) (de : D≠E) (ce : C≠E)
    (four : (Shore D).card=4) (common : ∀ z∈Shore D,G.Adj a z ∧ G.Adj b z)
    {x t : V} (xc : x∈Shore C) (tx : G.Adj t x) (tt : t=a ∨ t=b) :
    ((Shore E).filter (G.Adj t)).card ≤ 1 := by
  classical
  let Q := (Shore E).filter (G.Adj t)
  have sub : Shore D ∪ Q ⊆ PositiveEven G x := by
    intro z hz
    rcases mem_union.mp hz with zd | zq
    · rcases tt with rfl|rfl
      · exact foreign_pos_even hc dc.symm xc zd tx (common z zd).1
      · exact foreign_pos_even hc dc.symm xc zd tx (common z zd).2
    · exact foreign_pos_even hc ce xc (mem_filter.mp zq).1 tx (mem_filter.mp zq).2
  have dis := (shore_disjoint de).mono (show Shore D ⊆ Shore D from subset_rfl)
    (show Q ⊆ Shore E from filter_subset _ _)
  have cnt := card_le_card sub
  rw [card_union_of_disjoint dis,four] at cnt
  have cap := positive_cap x even
  change Q.card ≤ 1
  omega

private theorem each_port_universal_from_four_common (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (ab : a≠b)
    {D C E : Cmp (G:=G) (a:=a) (b:=b)} (dc : D≠C) (de : D≠E) (ce : C≠E)
    (four : (Shore D).card=4) (common : ∀ z∈Shore D,G.Adj a z ∧ G.Adj b z)
    {x : V} (xc : x∈Shore C) (port : G.Adj a x ∨ G.Adj b x) :
    ∀ y∈Shore C, y=x ∨ G.Adj x y := by
  classical
  apply complete_from_no_local_even hc xc
  intro y yc ym
  obtain ⟨z,ze,hxD,hz⟩ : ∃ z∈Shore E, Shore D ⊆ PositiveEven G x ∧ z ∈ PositiveEven G x := by
    rcases port with ax|bx
    · obtain ⟨z,ze,az⟩ := shore_hit_a ab conn E
      exact ⟨z,ze,fun w wd=>foreign_pos_even hc dc.symm xc wd ax (common w wd).1,
        foreign_pos_even hc ce xc ze ax az⟩
    · obtain ⟨z,ze,bz⟩ := shore_hit_b ab conn E
      exact ⟨z,ze,fun w wd=>foreign_pos_even hc dc.symm xc wd bx (common w wd).2,
        foreign_pos_even hc ce xc ze bx bz⟩
  have zD : z∉Shore D := fun e=>disjoint_left.mp (shore_disjoint de) e ze
  have yD : y∉Shore D := fun e=>disjoint_left.mp (shore_disjoint dc) e yc
  have yz : y≠z := fun e=>disjoint_left.mp (shore_disjoint ce) yc (by simpa only [e] using ze)
  have sub : insert y (insert z (Shore D)) ⊆ PositiveEven G x := by
    intro w hw
    rcases mem_insert.mp hw with rfl|hw
    · exact ym
    rcases mem_insert.mp hw with rfl|hw
    · exact hz
    · exact hxD hw
  have no : y∉insert z (Shore D) := by simp [yz,yD]
  have cnt := card_le_card sub
  rw [card_insert_of_not_mem no,card_insert_of_not_mem zD,four] at cnt
  have cap := positive_cap x even
  omega

private theorem vis_card_two_of_color_quota
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (ab : a≠b)
    (C : Cmp (G:=G) (a:=a) (b:=b))
    (big : 2≤(Shore C).card)
    (quotaA : ((Shore C).filter (G.Adj a)).card≤1)
    (quotaB : ((Shore C).filter (G.Adj b)).card≤1) :
    (Vis C).card=2 := by
  classical
  have lo := vis_card_ge_two ab conn C big
  have sub : Vis C ⊆ ((Shore C).filter (G.Adj a)) ∪ ((Shore C).filter (G.Adj b)) := by
    intro x xm
    obtain ⟨xc,p⟩ := mem_filter.mp xm
    exact mem_union.mpr (p.imp (fun h=>mem_filter.mpr ⟨xc,h⟩) (fun h=>mem_filter.mpr ⟨xc,h⟩))
  have hi := (card_le_card sub).trans (card_union_le _ _)
  omega

private theorem dark_if_two_port_has_high
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    {C : Cmp (G:=G) (a:=a) (b:=b)} (c4 : 4≤(Shore C).card) (port2 : (Vis C).card=2) :
    ∃ z∈Shore C, z∉Vis C ∧ 5≤G.degree z := by
  classical
  let Q := Shore C \ Vis C
  have q2 : 2≤Q.card := by
    have c := card_sdiff_add_card_eq_card (vis_sub C)
    change Q.card + _ = _ at c
    omega
  obtain ⟨u,um⟩ := card_pos.mp (show 0<Q.card by omega)
  have pos : 0<(Q.erase u).card := by
    have c := card_erase_add_one um
    omega
  obtain ⟨v,vm⟩ := card_pos.mp pos
  have vm' := (mem_erase.mp vm).2
  rcases degree v u (mem_erase.mp vm).1 with h|h
  · exact ⟨v,(mem_sdiff.mp vm').1,(mem_sdiff.mp vm').2,h⟩
  · exact ⟨u,(mem_sdiff.mp um).1,(mem_sdiff.mp um).2,h⟩

/-- Three nonsingleton shores cannot have a wholly high order-four shore. -/
theorem four_common_shore_impossible_with_two_other_large_shores (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    {D C E : Cmp (G:=G) (a:=a) (b:=b)} (dc : D≠C) (de : D≠E) (ce : C≠E)
    (four : (Shore D).card=4) (high : ∀ z∈Shore D,5≤G.degree z)
    (c4 : 4≤(Shore C).card) (e4 : 4≤(Shore E).card) : False := by
  classical
  have common := size_four_common four high
  have porttwo {K L : Cmp (G:=G) (a:=a) (b:=b)} (dk : D≠K) (dl : D≠L) (kl : K≠L)
      (big : 4≤(Shore L).card) : (Vis L).card=2 := by
    obtain ⟨x,xk,ax⟩ := shore_hit_a ab.ne conn K
    obtain ⟨y,yk,by'⟩ := shore_hit_b ab.ne conn K
    exact vis_card_two_of_color_quota conn ab.ne L (by omega)
      (foreign_quota_from_four_common hc even dk dl kl four common xk ax (.inl rfl))
      (foreign_quota_from_four_common hc even dk dl kl four common yk by' (.inr rfl))
  have c2 := porttwo de dc ce.symm c4
  have e2 := porttwo dc de ce e4
  have allCommon {K L : Cmp (G:=G) (a:=a) (b:=b)} (dk : D≠K) (dl : D≠L) (kl : K≠L)
      {z : V} (zk : z∈Shore K) (zd : z∉Vis K) :
      G.dist a z=2 ∧ G.dist b z=2 := by
    obtain ⟨x,xk,ax⟩ := shore_hit_a ab.ne conn K
    obtain ⟨y,yk,by'⟩ := shore_hit_b ab.ne conn K
    have nx : z≠x := fun h=>zd (mem_filter.mpr ⟨zk,h ▸ (.inl ax)⟩)
    have ny : z≠y := fun h=>zd (mem_filter.mpr ⟨zk,h ▸ (.inr by')⟩)
    have az : ¬G.Adj a z := fun h=>zd (mem_filter.mpr ⟨zk,.inl h⟩)
    have bz : ¬G.Adj b z := fun h=>zd (mem_filter.mpr ⟨zk,.inr h⟩)
    have xz := (each_port_universal_from_four_common hc even conn ab.ne dk dl kl four common
      xk (.inl ax) z zk).resolve_left nx
    have yz := (each_port_universal_from_four_common hc even conn ab.ne dk dl kl four common
      yk (.inr by') z zk).resolve_left ny
    have da := d2 hc (fun e=>(shore_off K).1 (by simpa only [← e] using zk)) az ax xz
    have db := d2 hc (fun e=>(shore_off K).2 (by simpa only [← e] using zk)) bz by' yz
    exact ⟨(mem_filter.mp da).2,(mem_filter.mp db).2⟩
  obtain ⟨z,zc,zv,zhi⟩ := dark_if_two_port_has_high degree c4 c2
  obtain ⟨w,we,wv,whi⟩ := dark_if_two_port_has_high degree e4 e2
  have zcom := allCommon dc de ce zc zv
  have wcom := allCommon de dc ce.symm we wv
  have wdepth : depth G a b w=2 := by simp [depth,wcom.1,wcom.2]
  have ns := dark_neighbors_in_shore hc we (by omega : depth G a b w ≠ 1)
  have wle := card_le_card ns
  rw [card_neighborFinset_eq_degree] at wle
  have wc := card_erase_add_one we
  have e6 : 6≤(Shore E).card := by omega
  have sub : Shore E \ Vis E ⊆ NearTwo E := by
    intro u hu
    obtain ⟨ue,uv⟩ := mem_sdiff.mp hu
    have d := allCommon de dc ce.symm ue uv
    exact mem_near_two.mpr ⟨ue,by simp [depth,d.1,d.2]⟩
  have e4near := card_le_card sub
  have csum := card_sdiff_add_card_eq_card (vis_sub E)
  have near3 := common_near_two_forbids_four_foreign hc ab even ce zc zcom.1 zcom.2
  omega

#print axioms four_common_shore_impossible_with_two_other_large_shores
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
