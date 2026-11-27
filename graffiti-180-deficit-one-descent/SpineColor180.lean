import SpineLayers180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem xor_diff (a b x y : Prop) [Decidable a] [Decidable b] [Decidable x] [Decidable y]
    (law : (a ↔ b) ↔ ¬(x ↔ y)) :
    xor (decide a) (decide x) ≠ xor (decide b) (decide y) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hx : x <;> by_cases hy : y <;> simp_all

/-- Flip the distance-parity color on the far component of the first
alternating bridge. When the unmarked vertices are independent, deleting
the first disagreement leaves a bipartite graph. -/
theorem spine_color (J : SimpleGraph V) (jc : J.Connected) (r : V) (odd : Bool) (A : Finset V)
    (ai : Indep J A) (t s : V) :
    let P := parity J r odd
    let D := (A∪P)\(A∩P)
    Spine J r D t → s∈D → Arc J r t s → ¬(carve J P t s).Reachable t s →
      Indep J (univ\(A∪P)) → TwoColor J (univ.erase t) := by
  classical
  intro P D sp sd ts broken outside
  let K := carve J P t s
  let R (v : V) := K.Reachable r v
  let c (v : V) := xor (decide (v∈P)) (decide (R v))
  have layers := separated_layers jc sp sd ts odd broken
  have flat {a b : V} (e : J.Adj a b) (same : a∈P ↔ b∈P) : J.dist a r=J.dist b r := by
    have l := jc.dist_triangle (u:=a) (v:=b) (w:=r)
    have m := jc.dist_triangle (u:=b) (v:=a) (w:=r)
    rw [dist_eq_one_iff_adj.mpr e] at l
    rw [dist_eq_one_iff_adj.mpr e.symm] at m
    change a∈parity J r odd ↔ b∈parity J r odd at same
    simp only [mem_parity] at same
    cases odd <;> simp only [Bool.toNat_false,Bool.toNat_true] at same <;> omega
  have meets {a b : V} (e : J.Adj a b) (same : a∈P ↔ b∈P) : a∈D ∨ b∈D := by
    by_contra! neither
    have flip {v : V} (no : v∉D) : v∈A ↔ v∈P := by
      change v∉(A∪P)\(A∩P) at no
      simp only [mem_sdiff,mem_union,mem_inter] at no
      tauto
    by_cases ap : a∈P
    · exact ai a ((flip neither.1).mpr ap) b ((flip neither.2).mpr (same.mp ap)) e.ne e
    · have absent {v : V} (no : v∉D) (np : v∉P) : v∈univ\(A∪P) :=
        mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim (fun va => np ((flip no).mp va)) np⟩
      exact outside a (absent neither.1 ap) b (absent neither.2 (fun bp => ap (same.mpr bp))) e.ne e
  apply (color_function J _).mpr
  refine ⟨c,?_⟩
  intro a ha b hb e
  have atip := (mem_erase.mp ha).1
  have btip := (mem_erase.mp hb).1
  by_cases same : a∈P ↔ b∈P
  · have eq := flat e same
    have diff : ¬(R a ↔ R b) := by
      rcases meets e same with ad|bd
      · obtain ⟨ar,br⟩ := layers a ad atip
        exact fun iff => ar (iff.mpr (br b e.ne.symm eq.symm))
      · obtain ⟨br,ar⟩ := layers b bd btip
        exact fun iff => br (iff.mp (ar a e.ne eq))
    exact xor_diff _ _ _ _ ⟨fun _ => diff,fun _ => same⟩
  · have op : a∈P ↔ b∉P := by tauto
    have inK : K.Adj a b := by
      apply deleteEdges_adj.mpr
      refine ⟨⟨e,op⟩,?_⟩
      intro pair
      rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp pair) with h|h
      · exact atip h.1
      · exact btip h.2
    have eqR : R a ↔ R b := ⟨fun h => h.trans inK.reachable,fun h => h.trans inK.symm.reachable⟩
    exact xor_diff _ _ _ _ ⟨fun h => (same h).elim,fun n => (n eqR).elim⟩

#print axioms spine_color
end Minimal180.DescentOne
