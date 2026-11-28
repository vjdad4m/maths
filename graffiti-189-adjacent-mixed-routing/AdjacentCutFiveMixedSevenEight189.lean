import AdjacentCutFiveMixedBothTerminals189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_closed shore_off shore_disjoint shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private augment_one_or_two inside_neighbor_of_nonsingle degree_two_if_nonadjacent from AdjacentCutFiveMixedTwoAugment189
open private augment_both_one_or_two from AdjacentCutFiveMixedBothTerminals189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev RouteCmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private def MixedRootCases (C : RouteCmp G a b) (x : V) : Prop :=
  ((∀ u∈Shore C,5≤G.degree u) ∧ (∃ u∈Shore C,G.Adj x u)) ∨
  ∃ l∈Shore C,(∀ u∈Shore C,u≠l → 5≤G.degree u) ∧
    ((G.Adj x l ∧ ∃ v∈Shore C,G.Adj l v) ∨
     ∃ u∈Shore C,∃ v∈Shore C,u≠l ∧ u≠v ∧ G.Adj x u ∧ G.Adj l v)

private theorem choose_root_cases {C : RouteCmp G a b} (ab : a≠b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (lo : 2≤(Shore C).card) : MixedRootCases C a ∨ MixedRootCases C b := by
  classical
  by_cases h : ∀ u∈Shore C,5≤G.degree u
  · exact .inl (.inl ⟨h,shore_hit_a ab conn C⟩)
  push_neg at h
  obtain ⟨l,lm,dl⟩ := h
  have hi (u : V) (_ : u∈Shore C) (ul : u≠l) : 5≤G.degree u :=
    (degree u l ul).resolve_right (by omega)
  by_cases al : G.Adj a l
  · exact .inl (.inr ⟨l,lm,hi,.inl ⟨al,inside_neighbor_of_nonsingle lm lo⟩⟩)
  by_cases bl : G.Adj b l
  · exact .inr (.inr ⟨l,lm,hi,.inl ⟨bl,inside_neighbor_of_nonsingle lm lo⟩⟩)
  obtain ⟨u,um,au⟩ := shore_hit_a ab conn C
  have bnd : G.neighborFinset l ⊆ Shore C := by
    intro v vm
    have lv := (mem_neighborFinset G l v).mp vm
    rcases shore_closed C l lm v lv with rfl|rfl|e
    · exact (al lv.symm).elim
    · exact (bl lv.symm).elim
    · exact e
  have sz : 2≤(G.neighborFinset l).card := by
    rw [card_neighborFinset_eq_degree]
    exact degree_two_if_nonadjacent (u:=l) (v:=a) conn (fun e=>(shore_off C).1 (e ▸ lm)) (fun e=>al e.symm)
  obtain ⟨v,vm,w,wm,vw⟩ := one_lt_card.mp sz
  have ext : ∃ r∈G.neighborFinset l,u≠r := by
    by_cases hu : u=v
    · exact ⟨w,wm,fun e=>vw (hu.symm.trans e)⟩
    · exact ⟨v,vm,hu⟩
  obtain ⟨r,rm,ur⟩ := ext
  exact .inl (.inr ⟨l,lm,hi,.inr
    ⟨u,um,r,bnd rm,fun e=>al (e ▸ au),ur,au,(mem_neighborFinset G l r).mp rm⟩⟩)

private theorem strip_augmentation {S : Finset V} (nonempty : S.Nonempty)
    {y t : V} (off : y∉S) (p : RouteOn G (insert y S) y t) :
    ∃ z,G.Adj y z ∧ RouteOn G S z t := by
  classical
  obtain ⟨w,wp,ws⟩ := p
  cases w with
  | nil =>
    obtain ⟨v,vm⟩ := nonempty
    have e : v=y := by simpa using (ws v).mpr (mem_insert_of_mem vm)
    exact (off (e ▸ vm)).elim
  | @cons _ z _ yz q =>
    have nq : y∉q.support := (List.nodup_cons.mp wp.support_nodup).1
    refine ⟨z,yz,q,wp.of_cons,?_⟩
    intro v
    by_cases e : v=y
    · simp [e,nq,off]
    have h := ws v
    simpa [support_cons,e] using h

/-- If one shore has 2–7 vertices and the other 2–8, a genuine
adjacent two-cut at degree-five threshold admits a spanning path. -/
theorem traceable_of_mixed_adjacent_two_shores_seven_eight (ab : G.Adj a b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : RouteCmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (clo : 2≤(Shore C).card) (chi : (Shore C).card≤7)
    (dlo : 2≤(Shore D).card) (dhi : (Shore D).card≤8) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have run {x y : V} (xy : G.Adj x y)
      (offx : ∀ K : RouteCmp G a b,x∉Shore K) (offy : ∀ K : RouteCmp G a b,y∉Shore K)
      (cov : ∀ {z : V}, z≠x → z≠y → z∈Shore C ∨ z∈Shore D)
      (bd : ∀ K : RouteCmp G a b,∀ u∈Shore K,∀ z,G.Adj u z → z=x ∨ z=y ∨ z∈Shore K)
      (rc : MixedRootCases C y) (rd : MixedRootCases D x) :
      ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
    obtain ⟨t,v⟩ := augment_one_or_two (y:=x) (offy C) chi
      (fun u um z uz=>by simpa only [or_left_comm] using bd C u um z uz) rc
    obtain ⟨z,yz,p⟩ := strip_augmentation (card_pos.mp (by omega)) (offy C) v
    obtain ⟨s,q⟩ := augment_both_one_or_two xy (offx D) (offy D) dhi (bd D) rd
    have apart : Disjoint (Shore C) (insert y (insert x (Shore D))) := by
      apply disjoint_left.mpr
      intro u um ud
      rcases mem_insert.mp ud with rfl|ud
      · exact offy C um
      rcases mem_insert.mp ud with rfl|ud
      · exact offx C um
      exact disjoint_left.mp (shore_disjoint cd) um ud
    obtain ⟨w,wp,ws⟩ := p.reverse.join q apart yz.symm
    refine ⟨t,s,w,wp,fun v=>(ws v).mpr ?_⟩
    by_cases e : v=x
    · simp [e]
    by_cases f : v=y
    · simp [f]
    rcases cov e f with h|h <;> simp [h]
  have abRun (rc : MixedRootCases C b) (rd : MixedRootCases D a) :=
    run ab (fun K=>(shore_off K).1) (fun K=>(shore_off K).2) cover shore_closed rc rd
  have baRun (rc : MixedRootCases C a) (rd : MixedRootCases D b) :=
    run ab.symm (fun K=>(shore_off K).2) (fun K=>(shore_off K).1) (fun nb na=>cover na nb)
      (fun K u um z uz=>by simpa only [or_left_comm] using shore_closed K u um z uz) rc rd
  by_cases d : ∀ u∈Shore D,5≤G.degree u
  · rcases choose_root_cases ab.ne conn degree clo with r|r
    · exact baRun r (.inl ⟨d,shore_hit_b ab.ne conn D⟩)
    · exact abRun r (.inl ⟨d,shore_hit_a ab.ne conn D⟩)
  push_neg at d
  obtain ⟨l,lm,ld⟩ := d
  have c (u : V) (um : u∈Shore C) : 5≤G.degree u :=
    (degree u l (fun e=>disjoint_left.mp (shore_disjoint cd) um (e.symm ▸ lm))).resolve_right (by omega)
  rcases choose_root_cases ab.ne conn degree dlo with r|r
  · exact abRun (.inl ⟨c,shore_hit_b ab.ne conn C⟩) r
  · exact baRun (.inl ⟨c,shore_hit_a ab.ne conn C⟩) r

/-- In orders through sixteen, two shores of size at least six are covered;
at order seventeen the same holds when both shores have size at least seven. -/
theorem traceable_of_mixed_adjacent_balanced_order_le_seventeen (ab : G.Adj a b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : RouteCmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (clo : 6≤(Shore C).card) (dlo : 6≤(Shore D).card)
    (order : Fintype.card V≤17)
    (shape : Fintype.card V≤16 ∨ 7≤(Shore C).card ∧ 7≤(Shore D).card) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have eq : Shore C ∪ Shore D = (univ.erase a |>.erase b : Finset V) := by
    ext z
    simp only [mem_union,mem_erase,mem_univ,and_true]
    constructor
    · rintro (h|h)
      · exact ⟨fun e=>(shore_off C).2 (e ▸ h),fun e=>(shore_off C).1 (e ▸ h)⟩
      · exact ⟨fun e=>(shore_off D).2 (e ▸ h),fun e=>(shore_off D).1 (e ▸ h)⟩
    · exact fun h=>cover h.2 h.1
  have sum := card_union_of_disjoint (shore_disjoint cd)
  rw [eq,card_erase_of_mem (by simp [ab.ne.symm]),card_erase_of_mem (mem_univ _),card_univ] at sum
  have cb : (Shore C).card≤8 := by
    rcases shape with h|⟨h,k⟩ <;> omega
  have db : (Shore D).card≤8 := by
    rcases shape with h|⟨h,k⟩ <;> omega
  by_cases c : (Shore C).card≤7
  · exact traceable_of_mixed_adjacent_two_shores_seven_eight ab conn degree cd cover
      (by omega) c (by omega) db
  exact traceable_of_mixed_adjacent_two_shores_seven_eight ab conn degree cd.symm
    (fun na nb=>(cover na nb).symm) (by omega) (by omega) (by omega) cb

#print axioms traceable_of_mixed_adjacent_two_shores_seven_eight
#print axioms traceable_of_mixed_adjacent_balanced_order_le_seventeen
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
