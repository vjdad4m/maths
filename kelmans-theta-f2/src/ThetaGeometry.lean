import PentagonCap

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaGeometry
open PentagonCap (attach attach_boundary attach_degree_outside pathRoot pathCap SmallFourTrivial
  outside_law_of_attachment good_path_cap_of_no_leaf_split)
open PentagonProfile (Port portCount mismatch)
open SquareCap (boundary SmallTrivial min_three_of_small_trivial)
noncomputable section

variable {V : Type*} [Fintype V]
variable {T : Type*} [Fintype T]

private theorem in_boundary {G : SimpleGraph V} {c : V → Bool} {e : V × V} :
    e ∈ boundary G c ↔ c e.1 = true ∧ c e.2 = false ∧ G.Adj e.1 e.2 := by
  classical
  simp [boundary]

private theorem boundary_const {W : Type*} [Fintype W] (G : SimpleGraph W) (b : Bool) :
    (boundary G (fun _ => b)).card = 0 := by
  classical
  cases b <;> simp [boundary]

omit [Fintype V] [Fintype T] in
private theorem mismatch_const (p : Port ↪ V) (r : Port → T) (c : V → Bool) (b : Bool) :
    mismatch p c ((fun _ => !b) ∘ r) = portCount p c b := by
  unfold mismatch portCount
  congr 1
  ext i
  cases b <;> cases h : c (p i) <;> simp [h]


omit [Fintype V] in
private theorem fiber_one [DecidableEq V] (p : Port ↪ V) (i : Port) :
    ((univ : Finset Port).filter (fun j => p j = p i)).card=1 := by
  have same : (univ : Finset Port).filter (fun j => p j = p i) = {i} := by
    ext j
    simp [p.injective.eq_iff]
  rw [same,card_singleton]

private theorem orient_big_cut [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : V→Bool) (b : Bool) {u v : V}
    (uv : u ≠ v) (cu : c u=b) (cv : c v=b)
    (only : ∀ x,c x=b → x=u ∨ x=v)
    (du : G.degree u=2) (dv : G.degree v=2)
    (ee : ¬G.Adj u v) :
    4 ≤ (boundary G c).card := by
  classical
  let endpoint (a w : V) := if b then (a,w) else (w,a)
  let A := (G.neighborFinset u).image (endpoint u)
  let B := (G.neighborFinset v).image (endpoint v)
  have occupy (a w : V) (h : G.Adj a w) (ax : c a=b) (wx : c w≠b) :
      endpoint a w ∈ boundary G c := by
    cases b
    · have wt : c w=true := by cases h : c w <;> simp_all
      exact in_boundary.mpr ⟨wt,ax,h.symm⟩
    · have wf : c w=false := by cases h : c w <;> simp_all
      exact in_boundary.mpr ⟨ax,wf,h⟩
  have intoA : A ⊆ boundary G c := by
    intro t ht
    obtain ⟨w,wn,rfl⟩ := mem_image.mp ht
    have ed := (mem_neighborFinset G u w).mp wn
    exact occupy u w ed cu (fun h => (only w h).elim
      (fun e => ed.ne e.symm) (fun e => ee (e ▸ ed)))
  have intoB : B ⊆ boundary G c := by
    intro t ht
    obtain ⟨w,wn,rfl⟩ := mem_image.mp ht
    have ed := (mem_neighborFinset G v w).mp wn
    exact occupy v w ed cv (fun h => (only w h).elim
      (fun e => ee (e ▸ ed).symm) (fun e => ed.ne e.symm))
  have dj : Disjoint A B := by
    apply disjoint_left.mpr
    intro t a b'
    obtain ⟨x,_,e⟩ := mem_image.mp a
    obtain ⟨y,_,f⟩ := mem_image.mp b'
    have clash := e.trans f.symm
    cases h : b
    · exact uv (by simpa [endpoint,h] using congrArg Prod.snd clash)
    · exact uv (by simpa [endpoint,h] using congrArg Prod.fst clash)
  have inj (a : V) : Function.Injective (endpoint a) := by
    intro x y e
    cases h : b
    · simpa [endpoint,h] using congrArg Prod.fst e
    · simpa [endpoint,h] using congrArg Prod.snd e
  have eqA : A.card=2 := by rw [card_image_of_injective _ (inj u),card_neighborFinset_eq_degree,du]
  have eqB : B.card=2 := by rw [card_image_of_injective _ (inj v),card_neighborFinset_eq_degree,dv]
  have lower := card_le_card (union_subset intoA intoB)
  rw [card_union_of_disjoint dj,eqA,eqB] at lower
  exact lower

/-- If the ambient is cyclically five-edge-connected in the explicit
cut sense, the only profile capable of breaking a leaf pair is an
edge between its two exterior endpoints. -/
theorem theta_bad_pair_requires_edge [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : SimpleGraph (Fin 7)} {p : Port ↪ V}
    {r : Port → Fin 7} [DecidableRel (attach G P p r).Adj]
    (strong : SmallFourTrivial (attach G P p r))
    (cub : ∀ x,(attach G P p r).degree (Sum.inl x)=3)
    (c : V→Bool) (b : Bool) {i j : Port} (ij : i ≠ j)
    (two : (boundary G c).card=2)
    (fit : ∀ a,c (p a)=b ↔ a=i ∨ a=j) : G.Adj (p i) (p j) := by
  classical
  have uu := (fit i).mpr (Or.inl rfl)
  have vv := (fit j).mpr (Or.inr rfl)
  have uv : p i ≠ p j := fun h=>ij (p.injective h)
  have pn : portCount p c b=2 := by
    have eq : (univ : Finset Port).filter (fun a => c (p a)=b) = {i,j} := by
      ext a
      simp [fit]
    unfold portCount
    rw [eq]
    simp [card_insert_of_not_mem,ij]
  have mask :
      (boundary (attach G P p r) (Sum.elim c (fun _ => !b))).card=4 := by
    rw [attach_boundary,boundary_const,mismatch_const, two,pn]
  obtain ⟨k,small⟩ := strong (Sum.elim c (fun _ => !b)) mask.le
  have same : k = b := by
    by_contra ne
    have nk : (!b) = k := by
      cases b <;> cases k <;> first | rfl | exact (ne rfl).elim
    have impossible := small (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) nk nk nk
    simp at impossible
  have only (x : V) (hx : c x=b) : x=p i ∨ x=p j := by
    subst k
    rcases small (Sum.inl x) (Sum.inl (p i)) (Sum.inl (p j)) hx uu vv with h|h|h
    · exact Or.inl (Sum.inl_injective h)
    · exact Or.inr (Sum.inl_injective h)
    · exact (uv (Sum.inl_injective h)).elim
  have hd (a : Port) : G.degree (p a)=2 := by
    have h := cub (p a)
    rw [attach_degree_outside,fiber_one] at h
    omega
  by_cases edge : G.Adj (p i) (p j)
  · exact edge
  · have huge := orient_big_cut c b uv uu vv only (hd i) (hd j) edge
    omega

private theorem leaf_ports (t : Fin 3) (leaf : t≠1) :
    (t=0 ∧ ∀ i,pathRoot i=t ↔ i=2 ∨ i=3) ∨
    (t=2 ∧ ∀ i,pathRoot i=t ↔ i=1 ∨ i=4) := by
  revert t
  decide

/-- A cap with fixed two-plus-two grouping is valid whenever its
paired exterior contacts are not adjacent, in the cyclic-five
input class. -/
theorem good_theta_cap_of_cyclic5 [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : SimpleGraph (Fin 7)} {p : Port ↪ V}
    {r : Port → Fin 7} [DecidableRel (attach G P p r).Adj]
    (normal : SmallTrivial (attach G P p r))
    (strong : SmallFourTrivial (attach G P p r))
    (cub : ∀ x,(attach G P p r).degree x=3)
    (p14 : ¬G.Adj (p 1) (p 4)) (p23 : ¬G.Adj (p 2) (p 3)) :
    SmallTrivial (pathCap G p) := by
  have laws := outside_law_of_attachment (by decide : 1<Fintype.card (Fin 7))
    normal (min_three_of_small_trivial cub normal)
  apply good_path_cap_of_no_leaf_split laws
  intro c t b leaf two fit
  rcases leaf_ports t leaf with ⟨_,a⟩|⟨_,a⟩
  · exact p23 (theta_bad_pair_requires_edge strong (fun x=>cub (Sum.inl x))
      c b (by decide) two (fun i => (fit i).trans (a i)))
  · exact p14 (theta_bad_pair_requires_edge strong (fun x=>cub (Sum.inl x))
      c b (by decide) two (fun i => (fit i).trans (a i)))


private def pairColor [DecidableEq V] (u v x : V) : Bool := decide (x=u∨x=v)

private theorem adjacent_pair_boundary [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (uv : G.Adj u v)
    (du : G.degree u=2) (dv : G.degree v=2) :
    (boundary G (pairColor u v)).card=2 := by
  classical
  let A := ((G.neighborFinset u).erase v).image (fun x=>(u,x))
  let B := ((G.neighborFinset v).erase u).image (fun x=>(v,x))
  have s : boundary G (pairColor u v) = A∪B := by
    ext ⟨x,y⟩
    rw [in_boundary,mem_union]
    constructor
    · rintro ⟨xs,ys,ed⟩
      have who : x=u∨x=v := by simpa [pairColor] using xs
      have yn : y≠u ∧ y≠v := by simpa [pairColor] using ys
      rcases who with rfl|rfl
      · exact Or.inl (mem_image.mpr ⟨y,mem_erase.mpr ⟨yn.2,(mem_neighborFinset _ _ _).mpr ed⟩,rfl⟩)
      · exact Or.inr (mem_image.mpr ⟨y,mem_erase.mpr ⟨yn.1,(mem_neighborFinset _ _ _).mpr ed⟩,rfl⟩)
    · rintro (all|all)
      · obtain ⟨w,wm,ee⟩ := mem_image.mp all
        have wy : w=y := congrArg Prod.snd ee
        have xu : x=u := (congrArg Prod.fst ee).symm
        subst x
        subst w
        have ed := (mem_neighborFinset G u y).mp (mem_erase.mp wm).2
        exact ⟨by simp [pairColor],by simp [pairColor,ed.ne.symm,(mem_erase.mp wm).1],ed⟩
      · obtain ⟨w,wm,ee⟩ := mem_image.mp all
        have wy : w=y := congrArg Prod.snd ee
        have xv : x=v := (congrArg Prod.fst ee).symm
        subst x
        subst w
        have ed := (mem_neighborFinset G v y).mp (mem_erase.mp wm).2
        exact ⟨by simp [pairColor],by simp [pairColor,ed.ne.symm,(mem_erase.mp wm).1],ed⟩
  have d : Disjoint A B := by
    apply disjoint_left.mpr
    intro e a b
    obtain ⟨x,_,xa⟩ := mem_image.mp a
    obtain ⟨y,_,yb⟩ := mem_image.mp b
    exact uv.ne (congrArg Prod.fst (xa.trans yb.symm))
  have vn : v∈G.neighborFinset u := (mem_neighborFinset G u v).mpr uv
  have un : u∈G.neighborFinset v := (mem_neighborFinset G v u).mpr uv.symm
  have a : A.card=1 := by
    rw [card_image_of_injective _ (fun _ _ e=>congrArg Prod.snd e),
      card_erase_of_mem vn,card_neighborFinset_eq_degree,du]
  have b : B.card=1 := by
    rw [card_image_of_injective _ (fun _ _ e=>congrArg Prod.snd e),
      card_erase_of_mem un,card_neighborFinset_eq_degree,dv]
  rw [s,card_union_of_disjoint d,a,b]

private def loneLeaf (a : Fin 3) : Bool := decide (a=2)

private theorem loneLeafCut :
    (boundary PentagonCap.path3 loneLeaf).card=1 := by
  have eq : boundary PentagonCap.path3 loneLeaf = {(2,1)} := by
    ext ⟨u,v⟩
    rw [in_boundary]
    have exactTable : ∀ i j : Fin 3,
      (loneLeaf i=true ∧ loneLeaf j=false ∧ PentagonCap.path3.Adj i j) ↔ (i,j)=(2,1) := by decide
    simpa using exactTable u v
  rw [eq,card_singleton]

/-- The prescribed retained pair cannot be adjacent in a legal fixed
cap. This obstruction is independent of any packing statement. -/
theorem kept_edge_breaks_fixed_cap [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : Port↪V}
    (d1 : G.degree (p 1)=2) (d4 : G.degree (p 4)=2)
    (edge : G.Adj (p 1) (p 4)) :
    ¬ SmallTrivial (pathCap G p) := by
  intro good
  let c := pairColor (p 1) (p 4)
  have left : (boundary G c).card=2 := adjacent_pair_boundary edge d1 d4
  have orFit : ∀ i : Port, (i=1∨i=4) ↔ pathRoot i=2 := by decide
  have agree (i : Port) : c (p i)=loneLeaf (pathRoot i) := by
    unfold c pairColor loneLeaf
    simp only [p.injective.eq_iff]
    exact decide_eq_decide.mpr (orFit i)
  have none : mismatch p c (loneLeaf ∘ pathRoot)=0 := by
    simp [mismatch, agree]
  have cut : (boundary (pathCap G p) (Sum.elim c loneLeaf)).card=3 := by
    rw [pathCap,attach_boundary,left,loneLeafCut,none]
  rcases good (Sum.elim c loneLeaf) cut.le with small|small
  · have eq := small (Sum.inl (p 1)) (Sum.inl (p 4))
        (show c (p 1)=true by simp [c,pairColor])
        (show c (p 4)=true by simp [c,pairColor])
    exact edge.ne (Sum.inl_injective eq)
  · have eq := small (Sum.inr 0) (Sum.inr 1) rfl rfl
    exact (by decide : (0:Fin 3)≠1) (Sum.inr_injective eq)

private def loneDiscard (a : Fin 3) : Bool := decide (a=0)

private theorem loneDiscardCut :
    (boundary PentagonCap.path3 loneDiscard).card=1 := by
  have eq : boundary PentagonCap.path3 loneDiscard = {(0,1)} := by
    ext ⟨u,v⟩
    rw [in_boundary]
    have exactTable : ∀ i j : Fin 3,
      (loneDiscard i=true ∧ loneDiscard j=false ∧ PentagonCap.path3.Adj i j) ↔ (i,j)=(0,1) := by decide
    simpa using exactTable u v
  rw [eq,card_singleton]

/-- The prescribed discarded pair cannot be adjacent in a legal fixed
cap. This obstruction is independent of any packing statement. -/
theorem discard_edge_breaks_fixed_cap [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : Port↪V}
    (d1 : G.degree (p 2)=2) (d4 : G.degree (p 3)=2)
    (edge : G.Adj (p 2) (p 3)) :
    ¬ SmallTrivial (pathCap G p) := by
  intro good
  let c := pairColor (p 2) (p 3)
  have left : (boundary G c).card=2 := adjacent_pair_boundary edge d1 d4
  have orFit : ∀ i : Port, (i=2∨i=3) ↔ pathRoot i=0 := by decide
  have agree (i : Port) : c (p i)=loneDiscard (pathRoot i) := by
    unfold c pairColor loneDiscard
    simp only [p.injective.eq_iff]
    exact decide_eq_decide.mpr (orFit i)
  have none : mismatch p c (loneDiscard ∘ pathRoot)=0 := by
    simp [mismatch, agree]
  have cut : (boundary (pathCap G p) (Sum.elim c loneDiscard)).card=3 := by
    rw [pathCap,attach_boundary,left,loneDiscardCut,none]
  rcases good (Sum.elim c loneDiscard) cut.le with small|small
  · have eq := small (Sum.inl (p 2)) (Sum.inl (p 3))
        (show c (p 2)=true by simp [c,pairColor])
        (show c (p 3)=true by simp [c,pairColor])
    exact edge.ne (Sum.inl_injective eq)
  · have eq := small (Sum.inr 1) (Sum.inr 2) rfl rfl
    exact (by decide : (1:Fin 3)≠2) (Sum.inr_injective eq)

#print axioms discard_edge_breaks_fixed_cap
#print axioms kept_edge_breaks_fixed_cap

#print axioms theta_bad_pair_requires_edge
#print axioms good_theta_cap_of_cyclic5

end
end KelmansCactus.AtomicBridge.ThetaGeometry
