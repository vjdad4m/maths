import OriginalPins
namespace Graffiti384b.OddStars.CubicComponent
open Finset SimpleGraph LeafCritical CubicLeaves
open private Graffiti384b.cut Graffiti384b.cut_symm from Proof384b
open private OddStars.crossing OddStars.translated OddStars.crossing_compl from CutAtVertex
open private OddStars.flip from ComponentBalance
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem cross_total (A : Finset V) :
    ∑v,(OddStars.crossing G A v).card=2*Graffiti384b.cut G A Aᶜ := by
  classical
  have side (B : Finset V) : ∑v∈B,(OddStars.crossing G B v).card=Graffiti384b.cut G B Bᶜ := by
    unfold Graffiti384b.cut
    apply sum_congr rfl
    intro v vm
    rw [OddStars.translated,if_pos vm]
    simp [nbr]
  have s := side A
  have t := side Aᶜ
  simp only [OddStars.crossing_compl,compl_compl,Graffiti384b.cut_symm G Aᶜ A] at t
  have parts := sum_union (s₁:=A) (s₂:=Aᶜ) (f:=fun v => (OddStars.crossing G A v).card) disjoint_compl_right
  rw [show A∪Aᶜ=univ by ext; simp] at parts
  calc
    _ = (∑v∈A,(OddStars.crossing G A v).card)+(∑v∈Aᶜ,(OddStars.crossing G A v).card) := parts
    _ = _ := by rw [s,t]; omega

/-- Reversing all colors in an entire union of components preserves
the maximum-cut objective. -/
theorem component_flip {A R : Finset V} (maximal : Maximum G A) (closed : region G R) :
    Maximum G (OddStars.flip A R) := by
  classical
  have eq (v : V) : OddStars.crossing G (OddStars.flip A R) v=OddStars.crossing G A v := by
    ext w
    simp only [OddStars.crossing,mem_filter,G.mem_neighborFinset]
    by_cases e : G.Adj v w
    · have both := closed e
      simp only [e,true_and,OddStars.flip,mem_union,mem_sdiff]
      tauto
    · simp [e]
  have total := cross_total G (OddStars.flip A R)
  simp only [eq] at total
  have old := cross_total G A
  intro B
  have val := maximal B
  omega

/-- Every original neighbor of a skeletal cubic belongs to the same
triangle-edge component, even when the joining edge is unsupported. -/
theorem every_neighbor_reachable (conn : G.Connected) (order : 2<Fintype.card V)
    (bad : bound G<gamma G) (one : 1∉types G) {v y : V} (dv : (patch G ∅).degree v=3)
    (edge : G.Adj v y) : (patch G ∅).Reachable v y := by
  classical
  let J := patch G ∅
  by_contra apart
  have unsup : ¬J.Adj v y := fun ed => apart ed.reachable
  let R := univ.filter (fun w => J.Reachable v w)
  have closed : region J R := by
    intro x z xz
    simp only [R,mem_filter,mem_univ,true_and]
    exact ⟨fun p => p.trans xz.reachable,fun p => p.trans xz.symm.reachable⟩
  have vin : v∈R := mem_filter.mpr ⟨mem_univ _,Reachable.refl _⟩
  have yout : y∉R := fun m => apart (mem_filter.mp m).2
  obtain ⟨A,_,opt⟩ := exists_max_image (univ : Finset (Finset V)) (fun A => Graffiti384b.cut J A Aᶜ) univ_nonempty
  have maxA : Maximum J A := fun S => opt _ (mem_univ S)
  have diff := (forced_crossing G conn order bad one maxA dv edge).2 unsup
  have same := (forced_crossing G conn order bad one (component_flip J maxA closed) dv edge).2 unsup
  simp only [OddStars.flip,mem_union,mem_sdiff,vin,yout,not_true_eq_false,and_false,
    false_and,false_or,true_and,not_false_eq_true,and_true,or_false] at same
  tauto

end Graffiti384b.OddStars.CubicComponent
#print axioms Graffiti384b.OddStars.CubicComponent.component_flip
#print axioms Graffiti384b.OddStars.CubicComponent.every_neighbor_reachable
