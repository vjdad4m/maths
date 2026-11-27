import PentagonCap

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.FiveCapCut
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
theorem five_bad_pair_requires_edge [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : SimpleGraph T} {p : Port ↪ V}
    {r : Port → T} [DecidableRel (attach G P p r).Adj]
    (three : Fin 3 ↪ T)
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
    have impossible := small (Sum.inr (three 0)) (Sum.inr (three 1)) (Sum.inr (three 2)) nk nk nk
    rcases impossible with i|i|i
    · exact (by decide : (0:Fin 3)≠1) (three.injective (Sum.inr_injective i))
    · exact (by decide : (0:Fin 3)≠2) (three.injective (Sum.inr_injective i))
    · exact (by decide : (1:Fin 3)≠2) (three.injective (Sum.inr_injective i))
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
theorem five_cap_of_nonadjacent_pairs [DecidableEq V] [DecidableEq T] {G : SimpleGraph V}
    [DecidableRel G.Adj] {P : SimpleGraph T} {p : Port ↪ V}
    {r : Port → T} [DecidableRel (attach G P p r).Adj]
    (three : Fin 3 ↪ T)
    (normal : SmallTrivial (attach G P p r))
    (strong : SmallFourTrivial (attach G P p r))
    (cub : ∀ x,(attach G P p r).degree x=3)
    (p14 : ¬G.Adj (p 1) (p 4)) (p23 : ¬G.Adj (p 2) (p 3)) :
    SmallTrivial (pathCap G p) := by
  have order : 3≤Fintype.card T := by
    have h := Fintype.card_le_of_injective three three.injective
    simpa using h
  have laws := outside_law_of_attachment (by omega : 1<Fintype.card T)
    normal (min_three_of_small_trivial cub normal)
  apply good_path_cap_of_no_leaf_split laws
  intro c t b leaf two fit
  rcases leaf_ports t leaf with ⟨_,a⟩|⟨_,a⟩
  · exact p23 (five_bad_pair_requires_edge three strong (fun x=>cub (Sum.inl x))
      c b (by decide) two (fun i => (fit i).trans (a i)))
  · exact p14 (five_bad_pair_requires_edge three strong (fun x=>cub (Sum.inl x))
      c b (by decide) two (fun i => (fit i).trans (a i)))


#print axioms five_bad_pair_requires_edge
#print axioms five_cap_of_nonadjacent_pairs

end
end KelmansCactus.AtomicBridge.FiveCapCut
