import SplitFlankImpossible189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.SingleStar Graffiti189LongestPath.FlankShore
open Graffiti189LongestPath.UltraOrder Graffiti189LongestPath.SixBorder
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external
  Graffiti189LongestPath.Rigidity.pin_pos from Rigidity189
open private Graffiti189LongestPath.OneSlack.cardinal_flankVertices
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option warningAsError true
set_option maxHeartbeats 3500000
namespace Graffiti189LongestPath.TriangleFar
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a far singleton, large omitted stars are traceable. In a counterexample
the two flanks are adjacent and the star has order at most d+1. -/
theorem traceable_of_far_flanks (hc : G.Connected) (k : Nat) (hk : 4≤k)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (far : (Shell G x 4).Nonempty) (xd : k+2≤G.degree x)
    {i : Nat} (hi : i∈Pins p x)
    {f g : V} (hf : f∈FlankVertices p x) (hg : g∈FlankVertices p x) (fg : f≠g)
    (fd : k+2≤G.degree f)
    (route : ¬G.Adj f g ∨ k+3<(OmittedStar p x).card) :
    ∃ (u v : V) (q : G.Walk u v), q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  apply Classical.byContradiction
  intro fail
  let d := k+2
  let t := p.getVert i
  let A := OmittedStar p x
  let B := External G A
  let F := FlankVertices p x
  let R := (univ : Finset V) \ (A∪B)
  let L := A.filter (G.Adj t)
  let T := A.filter (fun z => ¬G.Adj t z)
  let S := B.filter (G.Adj f)
  let P := DistanceTwo G f \ A
  let N := R.filter (fun z => G.Adj f z ∧ z≠g)
  let e : Nat := if G.Adj f g then 1 else 0
  have cap₂ (z : V) : (DistanceTwo G z).card≤d := distanceTwo_le_of_even d z (cap z)
  have tx : G.Adj t x := (Graffiti189LongestPath.pin_data hi).2.symm
  have bt : t∈B := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx
    (mem_image.mpr ⟨i,hi,rfl⟩)
  have ta : t∉A := (Graffiti189LongestPath.Rigidity.mem_external.mp bt).1
  have xa : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have sB := singleton_star_budget hc k conn hp hx one (cap x)
  have bk : B.card=k := (sB.2.2.2.2.1 far).1
  have rA {z : V} (hz : z∈R) : z∉A := fun h => (mem_sdiff.mp hz).2 (mem_union.mpr (Or.inl h))
  have rB {z : V} (hz : z∈R) : z∉B := fun h => (mem_sdiff.mp hz).2 (mem_union.mpr (Or.inr h))
  have noA {z u : V} (hz : z∈R) (ha : u∈A) : ¬G.Adj z u := fun e => rB hz
    (Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨rA hz,u,ha,e.symm⟩)
  have flankR (z : V) (hz : z∈F) : z∈R := by
    have nb := (mem_sdiff.mp (flanks_outside_boundary hc hp hx hz)).2
    obtain ⟨j,_,he⟩ := mem_image.mp hz
    have na : z∉A := fun h => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp h).1
      (he ▸ p.getVert_mem_support _)
    exact mem_sdiff.mpr ⟨mem_univ _,fun hz => (mem_union.mp hz).elim na nb⟩
  have fR := flankR f hf
  have gR := flankR g hg
  have rcl : ∀ u∈R,∀ v∉R,G.Adj u v → v∈B := by
    intro u hu v hv ed
    have cov : v∈A∪B := Classical.byContradiction (fun h => hv (mem_sdiff.mpr ⟨mem_univ _,h⟩))
    exact (mem_union.mp cov).elim (fun h => (noA hu h ed).elim) id
  have eqF : R.filter (G.Adj t)=R∩F := by
    have ca : Disjoint R A := disjoint_left.mpr (fun _ h => rA h)
    have cb : Disjoint R B := disjoint_left.mpr (fun _ h => rB h)
    exact (pins_meet_complement_in_flanks hc k cap conn hp hx one far hi R ⟨f,fR⟩ ca cb rcl).2
  have ft : G.Adj t f :=
    (mem_filter.mp (eqF.symm ▸ mem_inter.mpr ⟨fR,hf⟩)).2
  have gt : G.Adj t g :=
    (mem_filter.mp (eqF.symm ▸ mem_inter.mpr ⟨gR,hg⟩)).2
  have sing : Pins p x={i} := by
    apply (eq_of_subset_of_card_le _ _).symm
    · intro z hz; exact (mem_singleton.mp hz).symm ▸ hi
    · rw [card_singleton,one]
  have fct : F.card≤2 := by
    change (FlankVertices p x).card≤2
    rw [Graffiti189LongestPath.OneSlack.cardinal_flankVertices hp]
    simp only [FlankIndices,sing,image_singleton]
    exact (card_union_le _ _).trans (by simp)
  have fsplit : F = {f,g} := by
    apply (eq_of_subset_of_card_le ?_ ?_).symm
    · intro v hv
      rcases mem_insert.mp hv with rfl|hv
      · exact hf
      · exact (mem_singleton.mp hv).symm ▸ hg
    · simpa [fg] using fct
  have xsize : d≤A.card := by
    have cover : G.neighborFinset x⊆PinVertices p x∪A.erase x := by
      intro z hz
      have ed := (G.mem_neighborFinset x z).mp hz
      by_cases h : z∈p.support
      · obtain ⟨j,hj,eq⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx h ed
        exact mem_union.mpr (Or.inl (mem_image.mpr ⟨j,hj,eq⟩))
      · exact mem_union.mpr (Or.inr (mem_erase.mpr ⟨ed.ne.symm,
          Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨h,Or.inr ed⟩⟩))
    have c := card_le_card cover
    rw [G.card_neighborFinset_eq_degree] at c
    have u := card_union_le (PinVertices p x) (A.erase x)
    rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,one,card_erase_of_mem xa] at u
    dsimp [d]
    omega
  have asplit : A.card≤L.card+T.card := by
    have sub : A⊆L∪T := by
      intro z hz
      by_cases ed : G.Adj t z
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hz,ed⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hz,ed⟩))
    exact (card_le_card sub).trans (card_union_le _ _)
  have coverT : T⊆DistanceTwo G t := by
    intro z hz
    obtain ⟨za,no⟩ := mem_filter.mp hz
    rcases (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp za).2 with eq|h
    · exact (no (eq.symm ▸ tx)).elim
    · exact Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc (fun e => ta (e.symm ▸ za)) no tx h)
  have coverN : N⊆DistanceTwo G t := by
    intro z hz
    obtain ⟨zr,ed,ng⟩ := mem_filter.mp hz
    have nF : z∉F := by
      rw [fsplit]
      intro zf
      rcases mem_insert.mp zf with e|e
      · exact ed.ne e.symm
      · exact ng (mem_singleton.mp e)
    have no : ¬G.Adj t z := fun ed => nF (mem_inter.mp (eqF ▸ mem_filter.mpr ⟨zr,ed⟩)).2
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc (fun e => rB zr (e ▸ bt)) no ft ed)
  have disTN : Disjoint T N := disjoint_left.mpr (fun _ h h' =>
    rA (mem_filter.mp h').1 (mem_filter.mp h).1)
  have countTN := card_le_card (union_subset coverT coverN)
  rw [card_union_of_disjoint disTN] at countTN
  have tn : T.card+N.card≤d := countTN.trans (cap₂ t)
  have fbound : G.degree f≤S.card+N.card+e := by
    let E := ({g}:Finset V).filter (G.Adj f)
    have ce : E.card=e := by
      by_cases h : G.Adj f g <;> simp [E,e,h,Finset.filter_singleton]
    have sub : G.neighborFinset f⊆S∪N∪E := by
      intro z hz
      have ed := (G.mem_neighborFinset f z).mp hz
      by_cases zr : z∈R
      · by_cases zz : z=g
        · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_singleton.mpr zz,ed⟩))
        · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_filter.mpr ⟨zr,ed,zz⟩))))
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl
          (mem_filter.mpr ⟨rcl f fR z zr ed,ed⟩))))
    have c := card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at c
    have u := card_union_le S N
    have v := card_union_le (S∪N) E
    omega
  have l2 : L⊆DistanceTwo G f := by
    intro z hz
    obtain ⟨za,ed⟩ := mem_filter.mp hz
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc (fun e => rA fR (e.symm ▸ za)) (noA fR za) ft.symm ed)
  have lp : L.card+P.card≤d := by
    have dis : Disjoint L P := disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp h').2 (mem_filter.mp h).1)
    have c := card_le_card (union_subset l2 (sdiff_subset : P⊆DistanceTwo G f))
    rw [card_union_of_disjoint dis] at c
    exact c.trans (cap₂ f)
  have nonadj_help : ¬G.Adj f g → L.card+S.card≤d →
      g∈P ∧ ∀ z∈R, 2<G.dist f z → ¬G.Adj g z := by
    intro no small
    have e0 : e=0 := if_neg no
    have exactN : T.card+N.card=d := by dsimp [d] at xsize tn small; omega
    have coverE : T∪N=DistanceTwo G t :=
      (eq_of_subset_of_card_le (union_subset coverT coverN)
        (by rw [card_union_of_disjoint disTN,exactN]; exact cap₂ t)).symm.symm
    have gp : g∈P := mem_sdiff.mpr
      ⟨Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc fg no ft.symm gt),rA gR⟩
    refine ⟨gp,?_⟩
    intro z zr z3 ed
    have zNotF : z∉F := by
      rw [fsplit]
      intro zf
      rcases mem_insert.mp zf with rfl|eg
      · rw [dist_self] at z3
        omega
      · obtain rfl := mem_singleton.mp eg
        exact ed.ne rfl
    have znt : ¬G.Adj t z := fun a => zNotF (mem_inter.mp (eqF ▸ mem_filter.mpr ⟨zr,a⟩)).2
    have z2 : z∈DistanceTwo G t := Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc (fun e => rB zr (e ▸ bt)) znt gt ed)
    rw [←coverE] at z2
    rcases mem_union.mp z2 with zt|zn
    · exact rA zr (mem_filter.mp zt).1
    · have near : G.dist f z=1 := dist_eq_one_iff_adj.mpr (mem_filter.mp zn).2.1
      omega
  have radius (z : V) (zr : z∈R) : G.dist f z≤2 := by
    apply Nat.le_of_not_gt
    intro farZ
    let Y := R.filter (fun u => 2<G.dist f u)
    have zy : z∈Y := mem_filter.mpr ⟨zr,farZ⟩
    have fy : f∉Y := fun h => by
      have h' := (mem_filter.mp h).2
      rw [dist_self] at h'
      omega
    have close (U : Finset V) (sub : U⊆P)
        (allowed : ∀ u∈Y,∀ v∈P,G.Adj u v → v∈U)
        (small : (B\S).card+U.card<k) : False := by
      let K := (B\S)∪U
      have fk : f∉K := by
        intro h
        rcases mem_union.mp h with h|h
        · exact rB fR (mem_sdiff.mp h).1
        · have hh := Graffiti189LongestPath.mem_distanceTwo.mp (mem_sdiff.mp (sub h)).1
          rw [dist_self] at hh
          omega
      have dK : Disjoint Y K := disjoint_left.mpr (by
        intro u uy uk
        rcases mem_union.mp uk with h|h
        · exact rB (mem_filter.mp uy).1 (mem_sdiff.mp h).1
        · have dd := Graffiti189LongestPath.mem_distanceTwo.mp (mem_sdiff.mp (sub h)).1
          have v := (mem_filter.mp uy).2
          omega)
      have border : ∀ u∈Y,∀ v∉Y,G.Adj u v → v∈K := by
        intro u yu v vn ed
        have ur := (mem_filter.mp yu).1
        have u3 := (mem_filter.mp yu).2
        have tr := hc.dist_triangle (u:=f) (v:=v) (w:=u)
        have vu : G.dist v u=1 := dist_eq_one_iff_adj.mpr ed.symm
        by_cases vr : v∈R
        · have v2 : G.dist f v≤2 := Nat.le_of_not_gt (fun h => vn (mem_filter.mpr ⟨vr,h⟩))
          have vp : v∈P := mem_sdiff.mpr
            ⟨Graffiti189LongestPath.mem_distanceTwo.mpr (by omega),rA vr⟩
          exact mem_union.mpr (Or.inr (allowed u yu v vp ed))
        · have vb := rcl u ur v vr ed
          have vs : v∉S := by
            intro h
            have fv : G.dist f v=1 := dist_eq_one_iff_adj.mpr (mem_filter.mp h).2
            omega
          exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨vb,vs⟩))
      have c := Graffiti189LongestPath.boundary_card_of_connectivity k conn zy fy fk dK border
      exact (Nat.not_lt_of_ge c) ((card_union_le _ _).trans_lt small)
    have lm := card_sdiff_add_card_eq_card (show S⊆B from filter_subset _ _)
    by_cases big : d<L.card+S.card
    · exact close P (fun _ h => h) (fun _ _ _ h _ => h) (by omega)
    · have lbs : L.card+S.card≤d := Nat.le_of_not_gt big
      have ng : ¬G.Adj f g := by
        apply Classical.byContradiction
        intro no
        have ed : G.Adj f g := not_not.mp no
        have e1 : e=1 := if_pos ed
        rcases route with h|large
        · exact h ed
        · change k+3<A.card at large
          dsimp [d] at tn lbs
          omega
      obtain ⟨gp,noTouch⟩ := nonadj_help ng lbs
      have erase := card_erase_add_one gp
      have e0 : e=0 := if_neg ng
      have dls : d≤L.card+S.card := by dsimp [d] at tn xsize ⊢; omega
      exact close (P.erase g) (erase_subset _ _) (fun u yu v vp ed => mem_erase.mpr
        ⟨fun e => noTouch u (mem_filter.mp yu).1 (mem_filter.mp yu).2 (e ▸ ed.symm),vp⟩)
        (by omega)
  have rcount : R.card≤1+e+N.card+P.card := by
    let E := ({g}:Finset V).filter (G.Adj f)
    have ce : E.card=e := by by_cases h : G.Adj f g <;> simp [E,e,h,Finset.filter_singleton]
    have cover : R⊆insert f (E∪N∪P) := by
      intro z hz
      by_cases eq : z=f
      · exact mem_insert.mpr (Or.inl eq)
      apply mem_insert.mpr
      right
      by_cases ed : G.Adj f z
      · by_cases eg : z=g
        · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_filter.mpr
            ⟨mem_singleton.mpr eg,ed⟩))))
        · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_filter.mpr ⟨hz,ed,eg⟩))))
      · have d₂ := radius z hz
        have lo := hc.one_lt_dist_of_ne_of_not_adj (Ne.symm eq) ed
        exact mem_union.mpr (Or.inr
          (mem_sdiff.mpr ⟨Graffiti189LongestPath.mem_distanceTwo.mpr (by omega),rA hz⟩))
    have h := card_le_card cover
    have ci := card_insert_le f (E∪N∪P)
    have c₁ := card_union_le E N
    have c₂ := card_union_le (E∪N) P
    omega
  have total : Fintype.card V≤A.card+B.card+R.card := by
    have cov : (univ:Finset V)⊆A∪B∪R := by
      intro z h
      by_cases ab : z∈A∪B
      · exact mem_union.mpr (Or.inl ab)
      · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨h,ab⟩))
    have c := card_le_card cov
    rw [card_univ] at c
    have c₁ := card_union_le A B
    have c₂ := card_union_le (A∪B) R
    omega
  have et : e≤1 := by by_cases h : G.Adj f g <;> simp [e,h]
  dsimp [d] at tn lp
  by_cases q : k=4
  · have floor := order_lower_six_border hc k q cap conn deg fail
    omega
  · have floor := order_lower_wings_sharp hc k (by omega) cap conn deg fail
    omega
#print axioms traceable_of_far_flanks
end Graffiti189LongestPath.TriangleFar
