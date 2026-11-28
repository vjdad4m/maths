import DegreeFiveThreeThreeNeitherLTwo189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem local_card_intersection_nonempty {L X Y : Finset V}
    (L3 : L.card=3) (xL : X⊆L) (yL : Y⊆L) (x2 : 2≤X.card) (y2 : 2≤Y.card) :
    ∃ u∈X,u∈Y := by
  classical
  apply Classical.byContradiction
  intro no
  have dis : Disjoint X Y := disjoint_left.mpr (fun u ux uy=>no ⟨u,ux,uy⟩)
  have n := card_le_card (union_subset xL yL)
  rw [card_union_of_disjoint dis,L3] at n
  omega

theorem three_three_three_visible_local_impossible
    {S L T Yp Yq : Finset V} {p q f b u : V}
    (shape : S=insert p (insert q (L∪T))) (L3 : L.card=3)
    (uL : u∈L) (uNonport : G.neighborFinset u⊆S.erase u)
    (fS : f∈S)
    (high : ∀ x∈S,5≤G.degree x)
    (capP : Yp.card≤2) (capQ : Yq.card≤2)
    (dT : ∀ x∈T,x≠f → G.neighborFinset x⊆
      (L.filter (G.Adj x))∪T.erase x)
    (fBound : f∈T → G.neighborFinset f⊆insert b (L∪T.erase f))
    (hit : ∀ x∈T,x≠f → ((L.filter (G.Adj x)).Nonempty))
    (onP : ∀ x∈T,x≠f → ∀ m∈L,G.Adj p m → G.Adj x m → x∈Yp)
    (onQ : ∀ x∈T,x≠f → ∀ m∈L,G.Adj q m → G.Adj x m → x∈Yq)
    (coverL : ∀ x∈L,G.Adj p x ∨ G.Adj q x)
    (p2 : 2≤(L.filter (G.Adj p)).card)
    (q2 : 2≤(L.filter (G.Adj q)).card)
    (pFacts : f∈T → (f∈Yp ∨ ∀ x∈L,G.Adj p x))
    (qFacts : f∈T → (f∈Yq ∨ ∀ x∈L,G.Adj q x))
    (oneShared : f∈T → f∈Yp ∨ f∈Yq) :
    False := by
  classical
  have tS (x : V) (xt : x∈T) : x∈S := by
    rw [shape]
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ xt))
  have uS : u∈S := by rw [shape]; exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ uL))
  have left (x : V) (xt : x∈T) (xf : x≠f) :
      6≤(L.filter (G.Adj x)).card+T.card := by
    have n := (card_le_card (dT x xt xf)).trans (card_union_le _ _)
    rw [card_neighborFinset_eq_degree,card_erase_of_mem xt] at n
    have m := high x (tS x xt)
    have pos := card_pos.mpr ⟨x,xt⟩
    omega
  have lcap (x : V) : (L.filter (G.Adj x)).card≤3 := by
    exact (card_le_card (show L.filter (G.Adj x)⊆L from filter_subset _ _)).trans L3.le
  have tHit (x : V) (xt : x∈T) (xf : x≠f) : x∈Yp∪Yq := by
    obtain ⟨y,hy⟩ := hit x xt xf
    obtain ⟨yl,xy⟩ := mem_filter.mp hy
    rcases coverL y yl with py|qy
    · exact mem_union_left _ (onP x xt xf y yl py xy)
    exact mem_union_right _ (onQ x xt xf y yl qy xy)
  have shared_charge (R : Finset V) (r : V) (r2 : 2≤(L.filter (G.Adj r)).card)
      (onR : ∀ x∈T,x≠f → ∀ m∈L,G.Adj r m → G.Adj x m → x∈R) :
      ∀ x∈T,x≠f → 2≤(L.filter (G.Adj x)).card → x∈R := by
    intro x xt xf x2
    obtain ⟨y,ry,xy⟩ := local_card_intersection_nonempty L3 (filter_subset _ _) (filter_subset _ _) r2 x2
    exact onR x xt xf y (mem_filter.mp ry).1 (mem_filter.mp ry).2 (mem_filter.mp xy).2
  by_cases ft : f∈T
  · have t2 : 2≤T.card := by
      have n := card_le_card (fBound ft)
      rw [card_neighborFinset_eq_degree] at n
      have m := high f fS
      have k := card_insert_le b (L∪T.erase f)
      have w := card_union_le L (T.erase f)
      rw [card_erase_of_mem ft] at w
      omega
    have t3 : T.card≤3 := by
      rcases pFacts ft with pf|pAll
      · rcases qFacts ft with qf|qAll
        · have adj : T.erase f⊆(Yp.erase f)∪(Yq.erase f) := by
            intro x hx
            obtain ⟨xf,xt⟩ := mem_erase.mp hx
            rcases mem_union.mp (tHit x xt xf) with p|q
            · exact mem_union_left _ (mem_erase.mpr ⟨xf,p⟩)
            exact mem_union_right _ (mem_erase.mpr ⟨xf,q⟩)
          have n := (card_le_card adj).trans (card_union_le _ _)
          rw [card_erase_of_mem ft,card_erase_of_mem pf,card_erase_of_mem qf] at n
          omega
        have adj : T.erase f⊆Yq := by
          intro x hx
          obtain ⟨xf,xt⟩ := mem_erase.mp hx
          obtain ⟨y,ym⟩ := hit x xt xf
          obtain ⟨yl,xy⟩ := mem_filter.mp ym
          exact onQ x xt xf y yl (qAll y yl) xy
        have n := (card_le_card adj).trans capQ
        rw [card_erase_of_mem ft] at n
        omega
      have adj : T.erase f⊆Yp := by
        intro x hx
        obtain ⟨xf,xt⟩ := mem_erase.mp hx
        obtain ⟨y,ym⟩ := hit x xt xf
        obtain ⟨yl,xy⟩ := mem_filter.mp ym
        exact onP x xt xf y yl (pAll y yl) xy
      have n := (card_le_card adj).trans capP
      rw [card_erase_of_mem ft] at n
      omega
    obtain ⟨x,xm⟩ := card_pos.mp (show 0<(T.erase f).card by rw [card_erase_of_mem ft]; omega)
    obtain ⟨xf,xt⟩ := mem_erase.mp xm
    have n := left x xt xf
    have m := lcap x
    have exact3 : T.card=3 := by omega
    have charged (R : Finset V) (r : V) (rf : f∈R)
        (r2 : 2≤(L.filter (G.Adj r)).card)
        (onR : ∀ x∈T,x≠f → ∀ y∈L,G.Adj r y → G.Adj x y → x∈R) : T⊆R := by
      intro x xt
      by_cases e : x=f
      · exact e.symm ▸ rf
      have h := left x xt e
      exact shared_charge R r r2 onR x xt e (by omega)
    rcases oneShared ft with pf|qf
    · have p := (card_le_card (charged Yp p pf p2 onP)).trans capP
      omega
    have q := (card_le_card (charged Yq q qf q2 onQ)).trans capQ
    omega
  · have t4 : T.card≤4 := by
      have sub : T⊆Yp∪Yq := fun x xt=>tHit x xt (fun e=>ft (e ▸ xt))
      have n := (card_le_card sub).trans (card_union_le _ _)
      omega
    by_cases non : T.Nonempty
    · obtain ⟨x,xt⟩ := non
      have n := left x xt (fun e=>ft (e ▸ xt))
      have m := lcap x
      have t3 : 3≤T.card := by omega
      have sub : T⊆Yp := by
        intro y yt
        have yf : y≠f := fun e=>ft (e ▸ yt)
        have h := left y yt yf
        exact shared_charge Yp p p2 onP y yt yf (by omega)
      have h := (card_le_card sub).trans capP
      omega
    have t0 : T.card=0 := card_eq_zero.mpr
      (Finset.eq_empty_iff_forall_not_mem.mpr (fun x hx=>non ⟨x,hx⟩))
    have sh := cap_insert_pair shape
    exact nonport_lt_five_of_shore_small uS uNonport (by omega) (high u uS)

#print axioms three_three_three_visible_local_impossible
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
