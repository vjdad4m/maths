import SquareCapGeometry

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.PentagonProfile
open SquareCap (boundary SmallTrivial NontrivialSide)
noncomputable section

abbrev Port := Fin 5
variable {V : Type*} [Fintype V]

def portCount (p : Port ↪ V) (c : V → Bool) (b : Bool) : ℕ :=
  ((univ : Finset Port).filter (fun i => c (p i) = b)).card

def portWeight (t : Port → Bool) (b : Bool) : ℕ :=
  ((univ : Finset Port).filter (fun i => t i = b)).card

def mismatch (p : Port ↪ V) (c : V → Bool) (t : Port → Bool) : ℕ :=
  ((univ : Finset Port).filter (fun i => c (p i) ≠ t i)).card

/-- Lower bounds obtained by restoring the full 5-port gadget to the
opposite shore. Weak covers a singleton shore; strong covers all
larger shores. -/
structure OutsideLaw (G : SimpleGraph V) (p : Port ↪ V) : Prop where
  weak : ∀ c b, (∃ x, c x = b) → 3 ≤ (boundary G c).card + portCount p c b
  strong : ∀ c b, NontrivialSide c b → 4 ≤ (boundary G c).card + portCount p c b

omit [Fintype V] in
theorem portCount_complement (p : Port ↪ V) (c : V → Bool) :
    portCount p c true + portCount p c false = 5 := by
  have d : Disjoint ((univ : Finset Port).filter (fun i => c (p i) = true))
    ((univ : Finset Port).filter (fun i => c (p i) = false)) := by
    simp [disjoint_left]
  have e : ((univ : Finset Port).filter (fun i => c (p i) = true)) ∪
    ((univ : Finset Port).filter (fun i => c (p i) = false)) = univ := by
    ext i
    cases c (p i) <;> simp
  unfold portCount
  rw [←card_union_of_disjoint d,e,card_univ,Fintype.card_fin]

omit [Fintype V] in
private theorem portCount_le_one (p : Port ↪ V) (c : V → Bool) (b : Bool)
    (ns : ¬ NontrivialSide c b) : portCount p c b ≤ 1 := by
  unfold portCount
  apply card_le_one.mpr
  intro i hi j hj
  by_contra ne
  exact ns ⟨p i,p j,(mem_filter.mp hi).2,(mem_filter.mp hj).2,
    fun eq => ne (p.injective eq)⟩

omit [Fintype V] in
private theorem mismatch_zero (p : Port ↪ V) (c : V → Bool) (t : Port → Bool)
    (h : mismatch p c t = 0) : ∀ i, c (p i) = t i := by
  intro i
  by_contra ne
  have e := card_eq_zero.mp h
  have mem : i ∈ (univ : Finset Port).filter (fun i => c (p i) ≠ t i) :=
    mem_filter.mpr ⟨mem_univ _,ne⟩
  rw [e] at mem
  simp at mem

omit [Fintype V] in
private theorem agree_weight (p : Port ↪ V) (c : V → Bool) (t : Port → Bool)
    (h : ∀ i,c (p i) = t i) (b : Bool) :
    portCount p c b = portWeight t b := by
  simp [portCount,portWeight,h]

/-- The middle singleton in a path cap has two crossing internal
edges and one assigned port. No nontrivial bad cut can arise from
this case if both colors occur in the exterior. -/
theorem middle_split_impossible {G : SimpleGraph V} {p : Port ↪ V}
    (L : OutsideLaw G p) (c : V → Bool) (t : Port → Bool)
    (b : Bool) (solo : portWeight t b = 1)
    (mixed : ∀ b,∃ x,c x=b)
    (budget : (boundary G c).card + mismatch p c t + 2 ≤ 3) : False := by
  have a := L.weak c true (mixed true)
  have z := L.weak c false (mixed false)
  have both := portCount_complement p c
  have nm : mismatch p c t = 0 := by omega
  have agree := mismatch_zero p c t nm
  have s := L.weak c b (mixed b)
  rw [agree_weight p c t agree b,solo] at s
  omega

/-- The only possible nontrivial bad cut of a leaf-isolating path cap
is a genuine outside 2-edge cut with perfect agreement on all five
ports. In particular both outside shores contain ≥2 vertices. -/
theorem leaf_split_is_exact_two {G : SimpleGraph V} {p : Port ↪ V}
    (L : OutsideLaw G p) (c : V → Bool) (t : Port → Bool)
    (load : ∀ b,2 ≤ portWeight t b)
    (mixed : ∀ b,∃ x,c x=b)
    (budget : (boundary G c).card + mismatch p c t + 1 ≤ 3) :
    (boundary G c).card = 2 ∧ (∀ i,c (p i)=t i) ∧
      ∀ b,NontrivialSide c b := by
  have sides (b : Bool) : NontrivialSide c b := by
    by_contra h
    have sm := portCount_le_one p c b h
    have lw := L.weak c b (mixed b)
    have nm : mismatch p c t = 0 := by omega
    have p2 := agree_weight p c t (mismatch_zero p c t nm) b
    have lower := load b
    omega
  have a := L.strong c true (sides true)
  have z := L.strong c false (sides false)
  have both := portCount_complement p c
  have cb : (boundary G c).card = 2 := by omega
  have nm : mismatch p c t = 0 := by omega
  exact ⟨cb,mismatch_zero p c t nm,sides⟩

/-- A cut found on a proposed two-port leaf side projects to a
four-edge cut in the original graph when the pentagon is placed
entirely on the other side. This arithmetic version keeps
the exact equality separate from the graph lift. -/
theorem original_budget_four {G : SimpleGraph V} {p : Port ↪ V}
    (c : V → Bool) (t : Port → Bool) (b : Bool)
    (twoEdges : (boundary G c).card = 2) (agree : ∀ i,c (p i)=t i)
    (twoPorts : portWeight t b = 2) :
    (boundary G c).card + portCount p c b = 4 := by
  rw [twoEdges,agree_weight p c t agree b,twoPorts]

#print axioms middle_split_impossible
#print axioms leaf_split_is_exact_two
#print axioms original_budget_four

end
end KelmansCactus.AtomicBridge.PentagonProfile
