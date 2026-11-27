import ReplicaBudget
import Mathlib.Data.Finset.Preimage

open Finset
namespace KelmansCactus.AtomicBridge.ControlBudget
open Substitute Assemble ReplicaBudget

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {H : SimpleGraph V} {G : SimpleGraph W}

omit [Fintype V] in
private theorem pullback_factor (e : W ↪ V)
    (sound : ∀ u v, H.Adj (e u) (e v) → G.Adj u v)
    (closed : Closed H (univ.map e)) : KelmansStarter.HasP3Factor G := by
  classical
  obtain ⟨P, hP⟩ := closed
  let f (t : Finset V) := t.preimage e e.injective.injOn
  have restore (t : Finset V) (ht : t ∈ P) : (f t).map e = t := by
    ext v
    constructor
    · intro mem
      obtain ⟨w, hw, rfl⟩ := mem_map.mp mem
      exact mem_preimage.mp hw
    · intro hv
      obtain ⟨w, _, rfl⟩ := mem_map.mp (hP.tile_sub H ht hv)
      exact mem_map.mpr ⟨w, mem_preimage.mpr hv, rfl⟩
  refine ⟨P.image f, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    obtain ⟨card, a, ha, star⟩ := hP.tile t ht
    obtain ⟨c, _, rfl⟩ := mem_map.mp (hP.tile_sub H ht ha)
    refine ⟨?_, c, mem_preimage.mpr ha, ?_⟩
    · rw [← card_map (s := f t) e, restore t ht]
      exact card
    · intro w hw ne
      exact sound _ _ (star _ (mem_preimage.mp hw) (fun eq => ne (e.injective eq)))
  · intro s hs t ht ne
    obtain ⟨s', hs', rfl⟩ := mem_image.mp hs
    obtain ⟨t', ht', rfl⟩ := mem_image.mp ht
    apply disjoint_left.mpr
    intro w ws wt
    exact disjoint_left.mp (hP.disj _ hs' _ ht' (fun eq => ne (congrArg f eq)))
      (mem_preimage.mp ws) (mem_preimage.mp wt)
  · apply eq_univ_of_forall
    intro w
    have hw : e w ∈ P.biUnion id := by
      rw [hP.cover]
      exact mem_map.mpr ⟨w, mem_univ _, rfl⟩
    obtain ⟨t, ht, wt⟩ := mem_biUnion.mp hw
    have wp : w ∈ f t := mem_preimage.mpr wt
    exact mem_biUnion.mpr ⟨f t, mem_image_of_mem f ht, wp⟩

variable {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

abbrev Host (J W K : Type*) := Sum (J × W) K

def cellIn (j : J) : W ↪ Host J W K where
  toFun u := .inl (j,u)
  inj' := fun _ _ eq => (Prod.mk.inj (Sum.inl.inj eq)).2

def controlIn : K ↪ Host J W K where
  toFun := Sum.inr
  inj' := Sum.inr_injective

/-- The factor on one cell follows from any host factor when the
control count is too small to feed all nonfactorable divisible cells. -/
theorem cell_factor_of_host_factor_general
    (G : SimpleGraph W) (H : SimpleGraph (Host J W K))
    (capacity : 2 * Fintype.card K < 3 * Fintype.card J)
    (div : 3 ∣ Fintype.card W)
    (separates : ∀ (i j : J) (u v : W), H.Adj (.inl (i,u)) (.inl (j,v)) → i = j)
    (sound : ∀ (j : J) (u v : W), H.Adj (.inl (j,u)) (.inl (j,v)) → G.Adj u v)
    (has : KelmansStarter.HasP3Factor H) : KelmansStarter.HasP3Factor G := by
  classical
  by_contra bad
  let D (i : J) : Finset (Host J W K) := univ.map (cellIn i)
  let C : Finset (Host J W K) := univ.map controlIn
  have cell_disj : ((univ : Finset J) : Set J).PairwiseDisjoint D := by
    intro i _ j _ ne
    apply disjoint_left.mpr
    intro v hv hw
    obtain ⟨u, _, rfl⟩ := mem_map.mp hv
    obtain ⟨w, _, ew⟩ := mem_map.mp hw
    apply ne
    exact (Prod.mk.inj (Sum.inl.inj ew)).1.symm
  have cell_control : ∀ i ∈ (univ : Finset J), Disjoint (D i) C := by
    intro i _
    apply disjoint_left.mpr
    intro v hv hc
    obtain ⟨u, _, rfl⟩ := mem_map.mp hv
    obtain ⟨k, _, ek⟩ := mem_map.mp hc
    exact Sum.noConfusion ek
  have exits : ∀ i ∈ (univ : Finset J), ∀ u ∈ D i, ∀ v ∉ D i,
      H.Adj u v → v ∈ C := by
    intro i _ u hu v hv uv
    obtain ⟨s, _, rfl⟩ := mem_map.mp hu
    cases v with
    | inl p =>
      obtain ⟨j,t⟩ := p
      have eq := separates i j s t uv
      subst j
      exact (hv (mem_map.mpr ⟨t, mem_univ _, rfl⟩)).elim
    | inr k => exact mem_map.mpr ⟨k, mem_univ _, rfl⟩
  have no : ∀ i ∈ (univ : Finset J), ¬Closed H (D i) :=
    fun i _ cl => bad (pullback_factor (cellIn i) (sound i) cl)
  have b := defect_budget (G:=H) univ D C cell_disj cell_control exits
    (fun _ _ => by simpa [D] using div) no has
  have b' : 3 * Fintype.card J ≤ 2 * Fintype.card K := by simpa [C] using b
  omega

theorem cell_factor_of_host_factor
    (G : SimpleGraph W) (H : SimpleGraph (Host J W K))
    (hJ : Fintype.card J = 9) (hK : Fintype.card K = 12)
    (div : 3 ∣ Fintype.card W)
    (separates : ∀ (i j : J) (u v : W), H.Adj (.inl (i,u)) (.inl (j,v)) → i = j)
    (sound : ∀ (j : J) (u v : W), H.Adj (.inl (j,u)) (.inl (j,v)) → G.Adj u v)
    (has : KelmansStarter.HasP3Factor H) : KelmansStarter.HasP3Factor G :=
  cell_factor_of_host_factor_general G H (by omega) div separates sound has


omit [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J] [Fintype K] in
/-- No factor tile can use two controls: a control cannot center
such a tile, and a cell vertex has at most one control neighbor. -/
theorem controls_in_tile_eq
    {H : SimpleGraph (Host J W K)}
    (indep : ∀ a b : K, ¬H.Adj (.inr a) (.inr b))
    (uniq : ∀ (j : J) (u : W) (a b : K),
      H.Adj (.inl (j,u)) (.inr a) → H.Adj (.inl (j,u)) (.inr b) → a = b)
    {t : Finset (Host J W K)} (tile : KelmansStarter.IsTile H t)
    {a b : K} (ma : Sum.inr a ∈ t) (mb : Sum.inr b ∈ t) : a = b := by
  classical
  by_contra ne
  obtain ⟨_,c,_,star⟩ := tile
  cases c with
  | inl p =>
    obtain ⟨j,u⟩ := p
    exact ne (uniq j u a b (star _ ma (by simp)) (star _ mb (by simp)))
  | inr c =>
    by_cases eq : a = c
    · exact indep c b (star _ mb (fun h => ne (eq.trans (Sum.inr.inj h).symm)))
    · exact indep c a (star _ ma (fun h => eq (Sum.inr.inj h)))

noncomputable def controlTiles (P : Finset (Finset (Host J W K))) :
    Finset (Finset (Host J W K)) := by
  classical
  exact P.filter fun t => ¬Disjoint t (univ.map controlIn)

/-- Exactly two ordinary vertices per control belong to tiles
that contain a control, if no tile can contain two controls. -/
theorem exact_control_capacity
    {H : SimpleGraph (Host J W K)}
    (indep : ∀ a b : K, ¬H.Adj (.inr a) (.inr b))
    (uniq : ∀ (j : J) (u : W) (a b : K),
      H.Adj (.inl (j,u)) (.inr a) → H.Adj (.inl (j,u)) (.inr b) → a = b)
    {P : Finset (Finset (Host J W K))} (has : Factor H P) :
    ((((controlTiles P).biUnion id) \ (univ.map controlIn))).card = 2 * Fintype.card K := by
  classical
  let C : Finset (Host J W K) := univ.map controlIn
  let E := controlTiles P
  let T := E.biUnion id
  have Es : E ⊆ P := filter_subset _ _
  have pair : (E : Set (Finset (Host J W K))).PairwiseDisjoint id :=
    fun u hu v hv ne => has.disj _ (Es hu) _ (Es hv) ne
  have Csub : C ⊆ T := by
    intro v hv
    have hw : v ∈ P.biUnion id := has.cover.symm ▸ mem_univ _
    obtain ⟨t, ht, vt⟩ := mem_biUnion.mp hw
    exact mem_biUnion.mpr ⟨t, mem_filter.mpr ⟨ht, fun dj => disjoint_left.mp dj vt hv⟩, vt⟩
  have tC (t : Finset (Host J W K)) (ht : t ∈ E) : (t ∩ C).card = 1 := by
    apply le_antisymm
    · apply card_le_one_iff.mpr
      intro x y hx hy
      obtain ⟨a, _, rfl⟩ := mem_map.mp (mem_inter.mp hx).2
      obtain ⟨b, _, rfl⟩ := mem_map.mp (mem_inter.mp hy).2
      exact congrArg Sum.inr (controls_in_tile_eq indep uniq (has.tile _ (Es ht))
        (mem_inter.mp hx).1 (mem_inter.mp hy).1)
    · apply card_pos.mpr
      by_contra none
      exact (mem_filter.mp ht).2 (disjoint_left.mpr
        (fun v hv hc => none ⟨v, mem_inter.mpr ⟨hv,hc⟩⟩))
  have tsize : T.card = 3 * E.card := by
    change (E.biUnion id).card = _
    rw [card_biUnion pair]
    calc
      _ = ∑ t ∈ E, 3 := sum_congr rfl (fun t ht => (has.tile t (Es ht)).1)
      _ = _ := by simp [mul_comm]
  have ec : E.card = C.card := by
    have hcover : E.biUnion (fun t => t ∩ C) = C := by
      rw [← Finset.biUnion_inter]
      exact inter_eq_right.mpr Csub
    have ipair : (E : Set (Finset (Host J W K))).PairwiseDisjoint (fun t => t ∩ C) :=
      fun _ ha _ hb ne => (pair ha hb ne).mono inter_subset_left inter_subset_left
    rw [← hcover, card_biUnion ipair]
    calc
      E.card = ∑ t ∈ E, 1 := by simp
      _ = ∑ t ∈ E, (t ∩ C).card := (sum_congr rfl tC).symm
  have sz := card_sdiff_add_card_eq_card Csub
  have ccard : C.card = Fintype.card K := by simp [C]
  change (T \ C).card = _
  omega

#print axioms exact_control_capacity
#print axioms cell_factor_of_host_factor_general
#print axioms cell_factor_of_host_factor
end KelmansCactus.AtomicBridge.ControlBudget

