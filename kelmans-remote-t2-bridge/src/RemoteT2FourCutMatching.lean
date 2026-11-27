import RemoteT2PairCounts

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2FourCutMatching
open SquareCap (boundary SmallTrivial)
open RemoteT2PairCounts (OutsideTwo extended_lower extend innerCut row mismatch extended_boundary row_sum)
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in
def ColorThree (c : V→Bool) (b : Bool) : Prop :=
  ∃ a d e : V,a≠d∧a≠e∧d≠e∧c a=b∧c d=b∧c e=b

omit [Fintype V] [DecidableEq V] in
private theorem outside_two_of_color_three (c : V→Bool) {x y : V}
    (xy : c x≠c y) {b : Bool} (three : ColorThree c b) :
    OutsideTwo c x y b := by
  obtain ⟨a,d,e,ad,ae,de,ha,hd,he⟩ := three
  by_cases cx : c x=b
  · have cy : c y≠b := fun h=>xy (cx.trans h.symm)
    have ay : a≠y := fun h=>cy (h ▸ ha)
    have dy : d≠y := fun h=>cy (h ▸ hd)
    have ey : e≠y := fun h=>cy (h ▸ he)
    by_cases ax : a=x
    · exact ⟨d,e,(ax ▸ ad).symm,dy,(ax ▸ ae).symm,ey,de,hd,he⟩
    · by_cases dx : d=x
      · exact ⟨a,e,ax,ay,(dx ▸ de).symm,ey,ae,ha,he⟩
      · exact ⟨a,d,ax,ay,dx,dy,ad,ha,hd⟩
  · have ax : a≠x := fun h=>cx (h ▸ ha)
    have dx : d≠x := fun h=>cx (h ▸ hd)
    have ex : e≠x := fun h=>cx (h ▸ he)
    by_cases ay : a=y
    · exact ⟨d,e,dx,(ay ▸ ad).symm,ex,(ay ▸ ae).symm,de,hd,he⟩
    · by_cases dy : d=y
      · exact ⟨a,e,ax,ay,ex,(dy ▸ de).symm,ae,ha,he⟩
      · exact ⟨a,d,ax,ay,dx,dy,ad,ha,hd⟩

/-- A four-edge cut in a cubic cyclic-four graph with three or more
vertices on each shore consists of a matching. At a repeated port
one can recolor its common endpoint, leaving a nontrivial cut with
at most three crossing edges, which is forbidden. -/
theorem no_repeated_endpoint_of_four_cut (small : SmallTrivial G)
    (cub : ∀ w : V,G.degree w=3) (c : V→Bool)
    (pos : ColorThree c true) (neg : ColorThree c false) (width : (boundary G c).card≤4)
    {x y z : V} (xy : G.Adj x y) (xz : G.Adj x z)
    (qy : c x≠c y) (qz : c x≠c z) :
    y=z := by
  classical
  by_contra yz
  have p := outside_two_of_color_three c qy pos
  have q := outside_two_of_color_three c qy neg
  have extend_id : extend c x y (c x) (c y) = c := by
    funext v
    by_cases a : v=x
    · simp [extend,a]
    · by_cases b : v=y
      · subst v
        simp [extend,xy.ne.symm]
      · simp [extend,a,b]
  have nX : 1≤(row G c x y (c x)).card := by
    have zrow : z∈row G c x y (c x) :=
      mem_filter.mpr ⟨mem_erase.mpr ⟨(fun h=>yz h.symm),(mem_neighborFinset _ _ _).mpr xz⟩,qz.symm⟩
    exact card_pos.mpr ⟨z,zrow⟩
  have complement := row_sum G c xy (cub x)
  have lower := extended_lower G small c x y p q (c y) (c y)
  have d₁ := extended_boundary G c xy (c x) (c y)
  have d₂ := extended_boundary G c xy (c y) (c y)
  rw [extend_id] at d₁
  have hW : (innerCut G c x y).card+(row G c x y (c x)).card+
      (row G c y x (c y)).card+mismatch (c x) (c y)≤4 := d₁ ▸ width
  have hLo : 4≤(innerCut G c x y).card+(row G c x y (c y)).card+
      (row G c y x (c y)).card+mismatch (c y) (c y) := d₂ ▸ lower
  cases ex : c x <;> cases ey : c y
  · exact qy (ex.trans ey.symm)
  · rw [ex] at nX
    simp [ex,ey,mismatch] at hW hLo
    omega
  · rw [ex] at nX
    simp [ex,ey,mismatch] at hW hLo
    omega
  · exact qy (ex.trans ey.symm)

#print axioms no_repeated_endpoint_of_four_cut
end
end KelmansCactus.AtomicBridge.RemoteT2FourCutMatching
