import FlankShore189
import ExactStarOpposite189
import WideWing189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.SingleStar Graffiti189LongestPath.FlankShore
open Graffiti189LongestPath.UltraOrder Graffiti189LongestPath.SixBorder
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.TruncatedHall Graffiti189LongestPath.ForeignPorts
open Graffiti189LongestPath.PortHall Graffiti189LongestPath.WideWing
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two Graffiti189LongestPath.no_endpoints
  Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external
  Graffiti189LongestPath.Rigidity.pin_pos from Rigidity189
open private Graffiti189LongestPath.OneSlack.cardinal_flankVertices
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option warningAsError true
set_option maxHeartbeats 3500000
namespace Graffiti189LongestPath.TriangleTransfer
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Both residual far-singleton star sizes redirect to a separated double
porter: at d≥11 for size d, and at d≥8 for size d+1. -/
theorem triangle_star_transfers (hc : G.Connected) (k δ : Nat) (hk : 9≤k+3*δ) (hδ : δ≤1)
    (cap : ∀ v, (EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hpN : EdgeMinAvoid (k+2) p) (hx : x∉p.support)
    (one : (Pins p x).card=1) (far : (Shell G x 4).Nonempty) (xd : k+2≤G.degree x)
    {i : Nat} (hi : i∈Pins p x)
    {f g : V} (hf : f∈FlankVertices p x) (hg : g∈FlankVertices p x) (fg : f≠g)
    (fd : k+2≤G.degree f) (tri : G.Adj f g) (height : (OmittedStar p x).card=k+2+δ)
    (fail : ¬∃ (u v : V) (q : G.Walk u v), q.IsPath ∧ ∀ z,z∈q.support) :
    ∃ z∈OmittedStar p x, z≠x ∧ k+2≤G.degree z ∧
      (Pins p z).card=2 ∧ PairedPins p z=∅ := by
  classical
  have hp := hpN.1.1
  have k6 : 6≤k := by omega
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
  let Lit := B.filter (G.Adj t)
  let Q := shoreNeighbors G A S
  have e1 : e=1 := if_pos tri
  have tS : t∈S := mem_filter.mpr ⟨bt,ft.symm⟩
  have lQ : L⊆Q := by
    intro z hz
    exact mem_filter.mpr ⟨(mem_filter.mp hz).1,t,tS,(mem_filter.mp hz).2⟩
  have lq := card_le_card lQ
  have ab : Disjoint A B := disjoint_left.mpr (fun _ a b =>
    (Graffiti189LongestPath.Rigidity.mem_external.mp b).1 a)
  have acl : ∀ z∈A,∀ v∉A,G.Adj z v → v∈B := fun z za v va e =>
    Graffiti189LongestPath.Rigidity.mem_external.mpr ⟨va,z,za,e⟩
  have qBudget := opposite_port_budget hc d k A B conn ab bk (by dsimp [d] at xsize; omega)
    (rA fR) (rB fR) acl (cap f)
  have qp : Q.card+P.card≤d := qBudget.2
  have radius_sufficient (U : Finset V) (sub : U⊆P)
      (allowed : ∀ u∈R,2<G.dist f u → ∀ v∈R, v∈P → G.Adj u v → v∈U)
      (small : (B\S).card+U.card<k) (z : V) (zr : z∈R) : G.dist f z≤2 := by
    apply Nat.le_of_not_gt
    intro farZ
    let Y := R.filter (fun u => 2<G.dist f u)
    have zy : z∈Y := mem_filter.mpr ⟨zr,farZ⟩
    have fy : f∉Y := fun h => by
      have h' := (mem_filter.mp h).2
      rw [dist_self] at h'
      omega
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
        exact mem_union.mpr (Or.inr (allowed u ur u3 v vr vp ed))
      · have vb := rcl u ur v vr ed
        have vs : v∉S := by
          intro h
          have fv : G.dist f v=1 := dist_eq_one_iff_adj.mpr (mem_filter.mp h).2
          omega
        exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨vb,vs⟩))
    have c := Graffiti189LongestPath.boundary_card_of_connectivity k conn zy fy fk dK border
    exact (Nat.not_lt_of_ge c) ((card_union_le _ _).trans_lt small)
  have impossible_radius (radius : ∀ z∈R,G.dist f z≤2) : False := by
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
  have lm := card_sdiff_add_card_eq_card (show S⊆B from filter_subset _ _)
  have qnormal : Q.card+S.card≤d := by
    apply Nat.le_of_not_gt
    intro big
    exact impossible_radius (radius_sufficient P (fun _ h => h) (fun _ _ _ _ _ h _ => h)
      (by omega))
  have hs : A.card=d+δ := height
  have astrict : A.card=L.card+T.card := by
    have dis : Disjoint L T := disjoint_left.mpr (fun _ h h' => (mem_filter.mp h').2 (mem_filter.mp h).2)
    have eq : L∪T=A := Finset.Subset.antisymm
      (union_subset (filter_subset _ _) (filter_subset _ _)) (by
        intro z hz
        by_cases e : G.Adj t z
        · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hz,e⟩))
        · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hz,e⟩)))
    rw [←card_union_of_disjoint dis,eq]
  let sig := d-(L.card+S.card)
  let rho := d-(T.card+N.card)
  have sc : L.card+S.card+sig=d := by dsimp [sig]; omega
  have rc : T.card+N.card+rho=d := by dsimp [rho]; omega
  have slack : sig+rho+δ≤1 := by dsimp [d] at hs sc rc; omega
  have tc : T.card=S.card+sig+δ := by omega
  have qfree : (Q\L).card≤sig := by
    have h := card_sdiff_add_card_eq_card lQ
    omega
  let B₂ := B∩DistanceTwo G t
  have disE : Disjoint (T∪N) B₂ := disjoint_left.mpr (by
    intro z h zb
    have zB := (mem_inter.mp zb).1
    exact (mem_union.mp h).elim (fun ht => disjoint_left.mp ab (mem_filter.mp ht).1 zB)
      (fun hn => rB (mem_filter.mp hn).1 zB))
  have b₂ : B₂.card≤rho := by
    have h := card_le_card (union_subset (union_subset coverT coverN)
      (inter_subset_right : B₂⊆DistanceTwo G t))
    rw [card_union_of_disjoint disE,card_union_of_disjoint disTN] at h
    have c := cap₂ t
    omega
  let I := Lit∩S
  let M := Lit\S
  have mp : M⊆P := by
    intro z hz
    obtain ⟨zL,zS⟩ := mem_sdiff.mp hz
    obtain ⟨zb,tz⟩ := mem_filter.mp zL
    have no : ¬G.Adj f z := fun e => zS (mem_filter.mpr ⟨zb,e⟩)
    exact mem_sdiff.mpr
      ⟨Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc (fun e => rB fR (e.symm ▸ zb)) no ft.symm tz),
        fun h => disjoint_left.mp ab h zb⟩
  have mc : M.card≤sig := by
    apply Nat.le_of_not_gt
    intro n
    have er := card_sdiff_add_card_eq_card mp
    exact impossible_radius (radius_sufficient (P\M) sdiff_subset
      (fun u _ _ v vr vp _ => mem_sdiff.mpr ⟨vp,fun e => rB vr (mem_filter.mp (mem_sdiff.mp e).1).1⟩)
      (by omega))
  have lc : Lit.card≤I.card+M.card := by
    have cover : Lit⊆I∪M := by
      intro z hz
      by_cases hs : z∈S
      · exact mem_union.mpr (Or.inl (mem_inter.mpr ⟨hz,hs⟩))
      · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hz,hs⟩))
    exact (card_le_card cover).trans (card_union_le _ _)
  have notLit : t∉Lit := fun e => (mem_filter.mp e).2.ne rfl
  have s_upper : S.card≤1+I.card+B₂.card := by
    have cover : S⊆insert t (I∪B₂) := by
      intro z hz
      obtain ⟨zb,fz⟩ := mem_filter.mp hz
      by_cases eq : z=t
      · exact mem_insert.mpr (Or.inl eq)
      by_cases e : z∈Lit
      · exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inl (mem_inter.mpr ⟨e,hz⟩))))
      have tz : ¬G.Adj t z := fun h => e (mem_filter.mpr ⟨zb,h⟩)
      have e2 := Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc (Ne.symm eq) tz ft fz)
      exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inr (mem_inter.mpr ⟨zb,e2⟩))))
    have h := card_le_card cover
    have c := card_insert_le t (I∪B₂)
    have u := card_union_le I B₂
    omega
  let Dark := ((B.erase t)\Lit)
  have dark_to_T : shoreNeighbors G A (Dark\B₂) ⊆ T := by
    intro z hz
    obtain ⟨za,v,vd,vz⟩ := mem_filter.mp hz
    obtain ⟨vd,vn⟩ := mem_sdiff.mp vd
    obtain ⟨vB,vL⟩ := mem_sdiff.mp vd
    have vb := (mem_erase.mp vB).2
    have ne : t≠v := (mem_erase.mp vB).1.symm
    have tv : ¬G.Adj t v := fun e => vL (mem_filter.mpr ⟨vb,e⟩)
    by_cases e : G.Adj t z
    · have bad := Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc ne tv e vz.symm)
      exact (vn (mem_inter.mpr ⟨vb,bad⟩)).elim
    · exact mem_filter.mpr ⟨za,e⟩
  have dsub : Dark\B₂⊆B := fun z h => (mem_erase.mp (mem_sdiff.mp (mem_sdiff.mp h).1).1).2
  have dk := truncated_hall k A B (Dark\B₂) conn ab bk dsub (rA fR) (rB fR) acl
  have kd := card_le_card dsub
  rw [min_eq_right (by dsimp [d] at xsize; omega : (Dark\B₂).card≤A.card)] at dk
  have cd := card_le_card dark_to_T
  have darkc : Dark.card≤T.card+B₂.card := by
    have cov : Dark⊆(Dark\B₂)∪B₂ := by
      intro z hz
      by_cases h : z∈B₂
      · exact mem_union.mpr (Or.inr h)
      · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hz,h⟩))
    have c := card_le_card cov
    have u := card_union_le (Dark\B₂) B₂
    omega
  have allB : B.card≤1+Lit.card+Dark.card := by
    have cov : B⊆insert t (Lit∪Dark) := by
      intro z hz
      by_cases e : z=t
      · exact mem_insert.mpr (Or.inl e)
      by_cases l : z∈Lit
      · exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inl l)))
      · exact mem_insert.mpr (Or.inr (mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨mem_erase.mpr ⟨e,hz⟩,l⟩))))
    have c := card_le_card cov
    have u := card_union_le Lit Dark
    have v := card_insert_le t (Lit∪Dark)
    omega
  have litOn (z : V) (hz : z∈I) : z∈p.support := by
    apply Classical.byContradiction
    intro off
    have zt := (mem_filter.mp (mem_inter.mp hz).1).2.symm
    have zf := (mem_filter.mp (mem_inter.mp hz).2).2.symm
    have ii := (Graffiti189LongestPath.pin_data hi).1
    have pos := Graffiti189LongestPath.Rigidity.pin_pos hp hx hi
    have pr : i∈Pins p z := mem_filter.mpr ⟨mem_range.mpr ii,zt⟩
    obtain ⟨j,hj,ej⟩ := mem_image.mp hf
    rcases mem_union.mp hj with h|h
    · obtain ⟨l,hl,el⟩ := mem_image.mp h
      have li : l=i := by rw [sing] at hl; exact mem_singleton.mp hl
      have jj : j=i-1 := by omega
      have zz : i-1∈Pins p z := mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [←jj,ej]⟩
      have im := terminal_length_le_gap hp zz pr (by omega) (.nil : G.Walk z z) (by simp [isPath_def])
        (fun w hw => by
          have e : w=z := by simpa using hw
          exact e.symm ▸ off)
      simp only [length_nil] at im
      omega
    · obtain ⟨l,hl,el⟩ := mem_image.mp h
      have li : l=i := by rw [sing] at hl; exact mem_singleton.mp hl
      have jj : j=i+1 := by omega
      have before : i+1<p.length := by
        apply Nat.lt_of_not_ge
        intro h
        have e : i+1=p.length := by omega
        have bad : G.Adj z b := by
          have ee : p.getVert j=b := by rw [jj,e,getVert_length]
          exact ee ▸ (ej.symm ▸ zf)
        exact (Graffiti189LongestPath.no_endpoints hp off).2 bad
      have zz : i+1∈Pins p z := mem_filter.mpr ⟨mem_range.mpr before,by rwa [←jj,ej]⟩
      have im := terminal_length_le_gap hp pr zz (by omega) (.nil : G.Walk z z) (by simp [isPath_def])
        (fun w hw => by
          have e : w=z := by simpa using hw
          exact e.symm ▸ off)
      simp only [length_nil] at im
      omega
  obtain ⟨Fmap,inj,matching⟩ := ports_match_into_shore k A B conn ab bk
    (by dsimp [d] at xsize; omega) (rA fR) (rB fR) acl
  have finish (u : V) (hu : u∈I) (z : V) (za : z∈A) (zl : z∈L) (uz : G.Adj u z)
      (high : k+2≤G.degree z) :
      ∃ w∈A,w≠x ∧ k+2≤G.degree w ∧ (Pins p w).card=2 ∧ PairedPins p w=∅ := by
    have zoff := (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp za).1
    obtain ⟨j,hj,eq⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp zoff (litOn u hu) uz.symm
    have it : i∈Pins p z := mem_filter.mpr
      ⟨(mem_filter.mp hi).1,(mem_filter.mp zl).2.symm⟩
    have ij : i≠j := by
      intro e
      have tt : t=u := by rwa [←e] at eq
      exact notLit (tt.symm ▸ (mem_inter.mp hu).1)
    have zz : z≠x := by
      intro e
      have e' : j=i := mem_singleton.mp (sing ▸ (e ▸ hj))
      exact ij e'.symm
    have atLeast := one_lt_card.mpr ⟨i,it,j,hj,ij⟩
    have n := normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hpN zoff high i it
    have none : PairedPins p z=∅ := eq_empty_iff_forall_not_mem.mpr (by
      intro m hm
      obtain ⟨hm,l,hl,e|e⟩ := mem_filter.mp hm
      · exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hpN zoff high l hl).2
          (e.symm ▸ hm)
      · exact (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hpN zoff high m hm).2
          (e.symm ▸ hl))
    exact ⟨z,za,zz,high,by omega,none⟩
  apply Classical.byContradiction
  intro no
  let Low := A.filter (fun z => G.degree z<d)
  have lowc : Low.card≤1 := by
    apply Nat.le_of_not_gt
    intro big
    obtain ⟨u,hu,v,hv,ne⟩ := one_lt_card.mp big
    have uLo := (mem_filter.mp hu).2
    have vLo := (mem_filter.mp hv).2
    dsimp [d] at uLo vLo
    rcases deg u v ne with h|h <;> omega
  let Ii : Finset ↥(B : Set V) := univ.filter (fun z => z.val∈I)
  have ii : Ii.image Subtype.val=I := by
    ext z
    constructor
    · intro h
      obtain ⟨w,hw,rfl⟩ := mem_image.mp h
      exact (mem_filter.mp hw).2
    · intro h
      exact mem_image.mpr ⟨⟨z,(mem_filter.mp (mem_inter.mp h).1).1⟩,
        mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
  have image : Ii.image Fmap⊆Low∪(Q\L) := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    have vi := (mem_filter.mp hv).2
    have q : Fmap v∈Q := mem_filter.mpr ⟨(matching v).1,v.val,(mem_inter.mp vi).2,(matching v).2⟩
    by_cases l : Fmap v∈L
    · have dd : G.degree (Fmap v)<d := Nat.lt_of_not_ge (fun h =>
        no (finish v.val vi (Fmap v) (matching v).1 l (matching v).2 h))
      exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨(matching v).1,dd⟩))
    · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨q,l⟩))
  have im := card_le_card image
  have un := card_union_le Low (Q\L)
  rw [card_image_of_injective Ii inj,←card_image_of_injective Ii Subtype.val_injective,ii] at im
  omega
#print axioms triangle_star_transfers
end Graffiti189LongestPath.TriangleTransfer
