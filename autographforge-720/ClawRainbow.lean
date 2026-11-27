import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Nat.Lattice

/-! AutoGraphForge normalized physical row 720, generated ID f6e3f6c0. -/
namespace ClawRainbow720
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- The neighborhood test from the row 371 proof. -/
def ClawFree := ∀ v a b c : V,
  G.Adj v a → G.Adj v b → G.Adj v c → a ≠ b → a ≠ c → b ≠ c →
  G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

/-- GraphCalc's singleton palette and cost, as in the row 357 formalization. -/
def Rainbow (f : V → Fin 4) : Prop :=
  ∀ v, f v = 0 → ∀ c : Fin 4, c ≠ 0 → ∃ w, G.Adj v w ∧ f w = c

def weight (f : V → Fin 4) : ℕ := (univ.filter (fun v => f v ≠ 0)).card

noncomputable def rainbowNumber :=
  sInf {k | ∃ f : V → Fin 4, weight f = k ∧ Rainbow G f}

omit [Fintype V] in
/-- If an independent set meets each neighborhood in at most r vertices, a set
with at least r+1 neighbors at every outside vertex is strictly larger, provided
the graph has an edge. This statement has no connectivity or palette hypothesis. -/
theorem strict_count [DecidableEq V] [DecidableRel G.Adj] (I B : Finset V) (r : ℕ)
    (ind : G.IsIndepSet I) (edge : ∃ a b, G.Adj a b)
    (cap : ∀ u, (I.filter (G.Adj u)).card ≤ r)
    (demand : ∀ u ∉ B, r + 1 ≤ (B.filter (G.Adj u)).card) : I.card < B.card := by
  classical
  have incident (u : V) (hu : u ∈ I \ B) :
      r + 1 ≤ ((B \ I).bipartiteAbove G.Adj u).card := by
    obtain ⟨ui, ub⟩ := mem_sdiff.mp hu
    apply (demand u ub).trans
    apply card_le_card
    intro v hv
    obtain ⟨vb, uv⟩ := mem_filter.mp hv
    exact (mem_bipartiteAbove _).mpr ⟨mem_sdiff.mpr ⟨vb, fun vi => ind ui vi uv.ne uv⟩, uv⟩
  have supply (v : V) (_ : v ∈ B \ I) :
      ((I \ B).bipartiteBelow G.Adj v).card ≤ r := by
    apply le_trans (card_le_card ?_) (cap v)
    intro u hu
    obtain ⟨mem, uv⟩ := (mem_bipartiteBelow _).mp hu
    exact mem_filter.mpr ⟨(mem_sdiff.mp mem).1, uv.symm⟩
  have count := card_mul_le_card_mul G.Adj incident supply
  have hI := card_sdiff_add_card I B
  have hB := card_sdiff_add_card B I
  rw [union_comm B I] at hB
  by_contra! hle
  have size : (B \ I).card ≤ (I \ B).card := by omega
  have upper := Nat.mul_le_mul_right r size
  rw [Nat.mul_add, Nat.mul_one] at count
  have empty : (I \ B).card = 0 := by omega
  have same : I = B := by
    apply Finset.Subset.antisymm
    · exact sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp empty)
    · exact sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (by omega))
  subst B
  obtain ⟨a, b, ab⟩ := edge
  have outside (v : V) : v ∉ I → False := by
    intro hv
    have := demand v hv
    have := cap v
    omega
  exact ind (by_contra (outside a)) (by_contra (outside b)) ab.ne ab

omit [Fintype V] in
theorem local_cap [DecidableRel G.Adj] (hf : ClawFree G) (I : Finset V)
    (hi : G.IsIndepSet I) (v : V) : (I.filter (G.Adj v)).card ≤ 2 := by
  by_contra! h
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp h
  obtain ⟨ai,va⟩ := mem_filter.mp ha
  obtain ⟨bi,vb⟩ := mem_filter.mp hb
  obtain ⟨ci,vc⟩ := mem_filter.mp hc
  rcases hf v a b c va vb vc ab ac bc with e | e | e
  · exact hi ai bi ab e
  · exact hi ai ci ac e
  · exact hi bi ci bc e

/-- The three different nonzero labels require three distinct neighbors. -/
theorem rainbow_demand [DecidableRel G.Adj] (f : V → Fin 4) (hf : Rainbow G f)
    (v : V) (hv : f v = 0) :
    3 ≤ ((univ.filter (fun u => f u ≠ 0)).filter (G.Adj v)).card := by
  obtain ⟨a,va,ha⟩ := hf v hv 1 (by decide)
  obtain ⟨b,vb,hb⟩ := hf v hv 2 (by decide)
  obtain ⟨c,vc,hc⟩ := hf v hv 3 (by decide)
  apply two_lt_card_iff.mpr
  refine ⟨a,b,c,?_,?_,?_,?_,?_,?_⟩
  · simp [va,ha]
  · simp [vb,hb]
  · simp [vc,hc]
  · rintro rfl; rw [ha] at hb; exact (by decide : (1 : Fin 4) ≠ 2) hb
  · rintro rfl; rw [ha] at hc; exact (by decide : (1 : Fin 4) ≠ 3) hc
  · rintro rfl; rw [hb] at hc; exact (by decide : (2 : Fin 4) ≠ 3) hc

theorem row720_of_edge (hf : ClawFree G) (edge : ∃ a b, G.Adj a b) :
    G.indepNum + 1 ≤ rainbowNumber G := by
  classical
  obtain ⟨I,hi⟩ := G.exists_isNIndepSet_indepNum
  let sizes := {k | ∃ f : V → Fin 4, weight f = k ∧ Rainbow G f}
  have feasible : sizes.Nonempty := ⟨_, fun _ => 1, rfl, fun _ hv => False.elim ((by decide : (1 : Fin 4) ≠ 0) hv)⟩
  obtain ⟨f,cost,hf'⟩ := Nat.sInf_mem feasible
  have demand (u : V) (hu : u ∉ univ.filter (fun v => f v ≠ 0)) := rainbow_demand G f hf' u (by simpa using hu)
  have h := strict_count G I _ 2 hi.isIndepSet edge (local_cap G hf I hi.isIndepSet) demand
  change I.card < weight f at h
  change weight f = rainbowNumber G at cost
  simpa [hi.card_eq, cost] using h

theorem row720 (hn : 2 ≤ Fintype.card V) (hf : ClawFree G) (hc : G.Connected) :
    G.indepNum + 1 ≤ rainbowNumber G := by
  apply row720_of_edge G hf
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨a,b,hab⟩ := exists_pair_ne V
  obtain ⟨p⟩ := hc a b
  cases p with
  | nil => exact (hab rfl).elim
  | cons e _ => exact ⟨_,_,e⟩

/-- K₂ attains the additive constant. -/
theorem sharp_K2 : (⊤ : SimpleGraph (Fin 2)).indepNum = 1 ∧
    rainbowNumber (⊤ : SimpleGraph (Fin 2)) = 2 := by
  let K : SimpleGraph (Fin 2) := ⊤
  have claw : ClawFree K := by unfold ClawFree; decide
  have edge : ∃ a b, K.Adj a b := ⟨0, 1, by decide⟩
  have lower := row720_of_edge K claw edge
  have hi : K.IsIndepSet ({0} : Finset (Fin 2)) := by
    intro a ha b hb hab
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    exact (hab (ha.trans hb.symm)).elim
  have one := hi.card_le_indepNum
  change ({0} : Finset (Fin 2)).card ≤ K.indepNum at one
  rw [Finset.card_singleton] at one
  have upper : rainbowNumber K ≤ 2 :=
    Nat.sInf_le ⟨fun _ => 1, by decide,
      fun _ hv => False.elim ((by decide : (1 : Fin 4) ≠ 0) hv)⟩
  change K.indepNum = 1 ∧ rainbowNumber K = 2
  omega

#print axioms strict_count
#print axioms row720_of_edge
#print axioms row720
#print axioms sharp_K2
end ClawRainbow720
