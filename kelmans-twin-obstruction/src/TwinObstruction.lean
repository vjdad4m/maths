import Mathlib.Combinatorics.SimpleGraph.Finite

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.TwinObstruction
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The oriented cut, definitionally the same as FourRingCutAux.boundary. -/
def boundary (G : SimpleGraph V) (c : V → Bool) : Finset (V × V) := by
  classical
  exact univ.filter (fun e => c e.1 = true ∧ c e.2 = false ∧ G.Adj e.1 e.2)

/-- The small-cut condition is definitionally the same as FourRingCutAux.SmallTrivial. -/
def SmallTrivial (G : SimpleGraph V) : Prop :=
  ∀ c : V → Bool, (boundary G c).card ≤ 3 →
    (∀ x y, c x = true → c y = true → x = y) ∨ (∀ x y, c x = false → c y = false → x = y)

omit [Fintype V] in
private theorem card_finset_four {a b c d : V}
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d)
    (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) :
    ({a,b,c,d} : Finset V).card = 4 := by
  simp [card_insert_of_not_mem, ab, ac, ad, bc, bd, cd]

private theorem four_neighbors_forbidden {G : SimpleGraph V} [DecidableRel G.Adj]
    {v a b c d : V} (budget : G.degree v ≤ 3)
    (va : G.Adj v a) (vb : G.Adj v b) (vc : G.Adj v c) (vd : G.Adj v d)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d)
    (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) : False := by
  have h : ({a,b,c,d} : Finset V) ⊆ G.neighborFinset v := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    all_goals exact (mem_neighborFinset _ _ _).mpr (by assumption)
  have bound := card_le_card h
  rw [card_finset_four ab ac ad bc bd cd, card_neighborFinset_eq_degree] at bound
  omega

private theorem outside_unique {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Finset V) {u a b x y : V} (budget : G.degree u ≤ 3)
    (ab : a ≠ b) (aS : a ∈ S) (bS : b ∈ S) (xS : x ∉ S) (yS : y ∉ S)
    (ua : G.Adj u a) (ub : G.Adj u b) (ux : G.Adj u x) (uy : G.Adj u y) :
    x = y := by
  by_contra n
  exact four_neighbors_forbidden budget ua ub ux uy ab
    (fun e => xS (e ▸ aS)) (fun e => yS (e ▸ aS))
    (fun e => xS (e ▸ bS)) (fun e => yS (e ▸ bS)) n

private def colorOf (S : Finset V) (v : V) : Bool := decide (v ∈ S)

private theorem mem_cut {G : SimpleGraph V} {S : Finset V} {u v : V} :
    (u,v) ∈ boundary G (colorOf S) ↔ u ∈ S ∧ v ∉ S ∧ G.Adj u v := by
  classical
  simp [boundary, colorOf]

/-- If only vertices in `T` can leave `S`, and every vertex in `T` has
two neighbours in its own shore and degree at most three, then the
cut has at most `|T|` edges. -/
theorem cut_le_exposed_vertices {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Finset V)
    (source : ∀ u ∈ S, ∀ v ∉ S, G.Adj u v → u ∈ T)
    (budget : ∀ u ∈ T, G.degree u ≤ 3)
    (internal : ∀ u ∈ T, ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ G.Adj u a ∧ G.Adj u b) :
    (boundary G (colorOf S)).card ≤ T.card := by
  let C := boundary G (colorOf S)
  have inj : Set.InjOn Prod.fst (↑C : Set (V × V)) := by
    rintro ⟨u,x⟩ hx ⟨v,y⟩ hy eq
    change u = v at eq
    subst v
    obtain ⟨us, xs, ux⟩ := mem_cut.mp hx
    obtain ⟨_, ys, uy⟩ := mem_cut.mp hy
    have ut := source u us x xs ux
    obtain ⟨a, as, b, bs, ab, ua, ub⟩ := internal u ut
    have same := outside_unique S (budget u ut) ab as bs xs ys ua ub ux uy
    simp [same]
  have contained : C.image Prod.fst ⊆ T := image_subset_iff.mpr (by
    rintro ⟨u,v⟩ h
    obtain ⟨us, vs, uv⟩ := mem_cut.mp h
    exact source u us v vs uv)
  change C.card ≤ T.card
  simpa only [card_image_of_injOn inj] using card_le_card contained

private theorem shore_too_large {G : SimpleGraph V}
    (small : SmallTrivial G) (S : Finset V)
    (inner : 1 < S.card) (outer : 1 < Fintype.card V - S.card)
    (budget : (boundary G (colorOf S)).card ≤ 3) : False := by
  rcases small (colorOf S) budget with ins | outs
  · obtain ⟨u, hu, v, hv, ne⟩ := one_lt_card.mp inner
    exact ne (ins u v (by simpa [colorOf] using hu) (by simpa [colorOf] using hv))
  · rw [←card_compl] at outer
    obtain ⟨u, hu, v, hv, ne⟩ := one_lt_card.mp outer
    exact ne (outs u v (by simpa [colorOf] using hu) (by simpa [colorOf] using hv))

/-- An order-at-least-seven subcubic graph with no nontrivial cut of at
most three edges cannot contain a K₂,₃ subgraph. This needs degree
bounds only on the five marked vertices. -/
theorem no_three_common_neighbors {G : SimpleGraph V} [DecidableRel G.Adj]
    (small : SmallTrivial G) (large : 7 ≤ Fintype.card V)
    {u v a b c : V} (uv : u ≠ v) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (ua : G.Adj u a) (ub : G.Adj u b) (uc : G.Adj u c)
    (va : G.Adj v a) (vb : G.Adj v b) (vc : G.Adj v c)
    (du : G.degree u ≤ 3) (dv : G.degree v ≤ 3)
    (da : G.degree a ≤ 3) (db : G.degree b ≤ 3) (dc : G.degree c ≤ 3) :
    False := by
  let S : Finset V := {u,v,a,b,c}
  let T : Finset V := {a,b,c}
  have T_card : T.card = 3 := by simp [T,card_insert_of_not_mem,ab,ac,bc]
  have S_upper : S.card ≤ 5 := by
    have bound := card_insert_le u (insert v T)
    have bound' := card_insert_le v T
    change S.card ≤ _ at bound
    omega
  have S_inner : 1 < S.card := one_lt_card.mpr ⟨u, by simp [S], v, by simp [S], uv⟩
  have S_outer : 1 < Fintype.card V - S.card := by omega
  have esc : (boundary G (colorOf S)).card ≤ T.card := by
    apply cut_le_exposed_vertices S T
    · intro x hx w hw xw
      simp only [S, mem_insert, mem_singleton] at hx
      have wa : a ≠ w := fun e => hw (e ▸ (show a ∈ S by simp [S]))
      have wb : b ≠ w := fun e => hw (e ▸ (show b ∈ S by simp [S]))
      have wc : c ≠ w := fun e => hw (e ▸ (show c ∈ S by simp [S]))
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact (four_neighbors_forbidden du ua ub uc xw ab ac wa bc wb wc).elim
      · exact (four_neighbors_forbidden dv va vb vc xw ab ac wa bc wb wc).elim
      · simp [T]
      · simp [T]
      · simp [T]
    · intro x hx
      simp only [T, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · intro x hx
      refine ⟨u, by simp [S], v, by simp [S], uv, ?_⟩
      simp only [T, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨ua.symm, va.symm⟩
      · exact ⟨ub.symm, vb.symm⟩
      · exact ⟨uc.symm, vc.symm⟩
  exact shore_too_large small S S_inner S_outer (esc.trans_eq T_card)

/-- The useful low-order exception to the twin obstruction is explicit:
this theorem does not exclude twins in the six-vertex K₃,₃. -/
theorem no_equal_neighborhoods {G : SimpleGraph V} [DecidableRel G.Adj]
    (small : SmallTrivial G) (large : 7 ≤ Fintype.card V)
    (cub : ∀ v, G.degree v = 3) {u v : V} (uv : u ≠ v) :
    G.neighborFinset u ≠ G.neighborFinset v := by
  intro same
  have d : (G.neighborFinset u).card = 3 := cub u
  obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp (by omega : 1 < (G.neighborFinset u).card)
  let R := (G.neighborFinset u) \ {a,b}
  have rc : R.card = 1 := by
    have ss : ({a,b} : Finset V) ⊆ G.neighborFinset u := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    simp [R, card_sdiff ss, d, card_insert_of_not_mem, ab]
  obtain ⟨c,hc⟩ := (card_pos.mp (by omega : 0 < R.card))
  have hc0 := mem_sdiff.mp hc
  have nc : c ≠ a ∧ c ≠ b := by simpa using hc0.2
  have au := (mem_neighborFinset G u a).mp ha
  have bu := (mem_neighborFinset G u b).mp hb
  have cu := (mem_neighborFinset G u c).mp hc0.1
  rw [same] at ha hb
  have cv : G.Adj v c := by
    have h := hc0.1
    rw [same] at h
    exact (mem_neighborFinset G v c).mp h
  exact no_three_common_neighbors small large uv ab nc.1.symm nc.2.symm au bu cu
    ((mem_neighborFinset G v a).mp ha) ((mem_neighborFinset G v b).mp hb) cv
    (cub u).le (cub v).le (cub a).le (cub b).le (cub c).le

/-- The same cut argument excludes triangles as soon as there are
two other vertices; K₄ is outside this scope. -/
theorem no_triangle {G : SimpleGraph V} [DecidableRel G.Adj]
    (small : SmallTrivial G) (large : 5 ≤ Fintype.card V)
    {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (da : G.degree a ≤ 3) (db : G.degree b ≤ 3) (dc : G.degree c ≤ 3) :
    False := by
  let S : Finset V := {a,b,c}
  have S_card : S.card = 3 := by
    simp [S,card_insert_of_not_mem,ab.ne,bc.ne,ca.ne.symm]
  have cut : (boundary G (colorOf S)).card ≤ S.card := by
    apply cut_le_exposed_vertices S S (fun _ h _ _ _ => h)
    · intro x hx
      simp only [S, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · intro x hx
      simp only [S, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨b, by simp [S], c, by simp [S], bc.ne, ab, ca.symm⟩
      · exact ⟨c, by simp [S], a, by simp [S], ca.ne, bc, ab.symm⟩
      · exact ⟨a, by simp [S], b, by simp [S], ab.ne, ca, bc.symm⟩
  exact shore_too_large small S (by omega) (by omega) (cut.trans_eq S_card)

/-- For a fixed center, distinct partner vertices each have a private
neighbour outside the three marked vertices. Thus even a one-way
replacement of one partner by the other cannot preserve every
exterior attachment. -/
theorem partner_has_exclusive_exterior_neighbor {G : SimpleGraph V} [DecidableRel G.Adj]
    (small : SmallTrivial G) (large : 7 ≤ Fintype.card V)
    (cub : ∀ v, G.degree v = 3) {r u v : V} (ru : G.Adj r u) (rv : G.Adj r v)
    (uv : u ≠ v) : ∃ w, w ≠ r ∧ w ≠ u ∧ w ≠ v ∧ G.Adj u w ∧ ¬ G.Adj v w := by
  have nuv : ¬ G.Adj u v := fun h =>
    no_triangle small (by omega) ru h rv.symm (cub r).le (cub u).le (cub v).le
  by_contra missing
  push_neg at missing
  have sub : G.neighborFinset u ⊆ G.neighborFinset v := by
    intro w h
    rw [mem_neighborFinset] at h ⊢
    by_cases eq : w = r
    · exact eq.symm ▸ rv.symm
    · exact missing w eq h.ne.symm (fun e => nuv (e ▸ h)) h
  have dz : (G.neighborFinset v).card ≤ (G.neighborFinset u).card := by
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, cub, cub]
  exact no_equal_neighborhoods small large cub uv (eq_of_subset_of_card_le sub dz)

/-- The transposition of two potential partners fixing every other
vertex fails even as a one-way adjacency-preserving map on the
graph with their common center removed. -/
theorem no_center_fixed_swap_mono {G : SimpleGraph V} [DecidableRel G.Adj]
    (small : SmallTrivial G) (large : 7 ≤ Fintype.card V)
    (cub : ∀ v, G.degree v = 3) {r u v : V}
    (ru : G.Adj r u) (rv : G.Adj r v) (uv : u ≠ v) :
    ¬ (∀ x y, x ≠ r → y ≠ r →
      G.Adj x y → G.Adj (Equiv.swap u v x) (Equiv.swap u v y)) := by
  intro mono
  obtain ⟨w,wr,wu,wv,uw,vw⟩ :=
    partner_has_exclusive_exterior_neighbor small large cub ru rv uv
  apply vw
  simpa [Equiv.swap_apply_of_ne_of_ne wu wv] using mono u w ru.ne.symm wr uw

/-- Removing one more vertex still cannot make the partner transposition
an adjacency-preserving map. The two obstruction witnesses are distinct.
This covers a second fixed deletion, but not a switch moving additional
vertices. -/
theorem no_two_deleted_fixed_swap_mono {G : SimpleGraph V} [DecidableRel G.Adj]
    (small : SmallTrivial G) (large : 7 ≤ Fintype.card V)
    (cub : ∀ v, G.degree v = 3) {r u v z : V}
    (ru : G.Adj r u) (rv : G.Adj r v) (uv : u ≠ v) (uz : u ≠ z) (vz : v ≠ z) :
    ¬ (∀ x y, x ≠ r → y ≠ r → x ≠ z → y ≠ z →
      G.Adj x y → G.Adj (Equiv.swap u v x) (Equiv.swap u v y)) := by
  intro mono
  obtain ⟨a,ar,au,av,ua,va⟩ :=
    partner_has_exclusive_exterior_neighbor small large cub ru rv uv
  obtain ⟨b,br,bv,bu,vb,ub⟩ :=
    partner_has_exclusive_exterior_neighbor small large cub rv ru uv.symm
  by_cases az : a = z
  · have bz : b ≠ z := fun eq => va ((eq.trans az.symm) ▸ vb)
    apply ub
    simpa [Equiv.swap_apply_of_ne_of_ne bu bv] using mono v b rv.ne.symm br vz bz vb
  · apply va
    simpa [Equiv.swap_apply_of_ne_of_ne au av] using mono u a ru.ne.symm ar uz az ua

#print axioms no_two_deleted_fixed_swap_mono

#print axioms no_triangle
#print axioms partner_has_exclusive_exterior_neighbor
#print axioms no_center_fixed_swap_mono

#print axioms cut_le_exposed_vertices
#print axioms no_three_common_neighbors
#print axioms no_equal_neighborhoods

end
end KelmansCactus.AtomicBridge.TwinObstruction
