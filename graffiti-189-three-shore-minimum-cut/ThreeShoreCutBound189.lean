import SmallSeparator189
open Finset SimpleGraph Graffiti189LongestPath
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
set_option maxHeartbeats 7000000
namespace Graffiti189LongestPath.ThreeShoreCutBound
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A single cut vertex that reaches three mutually nonadjacent shores
at high-degree vertices spends another layer-two budget on the three
neighborhood differences. -/
theorem degree_le_six_cut_minus_six (hc : G.Connected) (d : Nat)
    (cap : ∀ v,(DistanceTwo G v).card≤d) (S C E T : Finset V)
    (parts : (univ:Finset V)=C∪E∪T∪S)
    (s : V) (ss : s∈S)
    (cs : Disjoint C S) (es : Disjoint E S) (ts : Disjoint T S)
    (ce : Disjoint C E) (ct : Disjoint C T) (et : Disjoint E T)
    (noCE : ∀ u∈C,∀ v∈E,¬G.Adj u v)
    (noCT : ∀ u∈C,∀ v∈T,¬G.Adj u v)
    (noET : ∀ u∈E,∀ v∈T,¬G.Adj u v)
    (u : V) (uc : u∈C) (su : G.Adj s u) (ud : d≤G.degree u)
    (v : V) (ve : v∈E) (sv : G.Adj s v) (vd : d≤G.degree v)
    (w : V) (wt : w∈T) (sw : G.Adj s w) (wd : d≤G.degree w) :
    d+6≤6*S.card := by
  classical
  let N (R : Finset V) := R.filter (G.Adj s)
  let gate (R : Finset V) (a : V) := (R.filter (G.Adj a))\N R
  have gsub (R : Finset V) (a : V) : gate R a⊆R := fun _ h => (mem_filter.mp (mem_sdiff.mp h).1).1
  have gates (R : Finset V) (ds : Disjoint R S) (a : V) (ar : a∈R) (sa : G.Adj s a) :
      gate R a⊆DistanceTwo G s := by
    intro z zz
    obtain ⟨zh,no⟩ := mem_sdiff.mp zz
    obtain ⟨zr,az⟩ := mem_filter.mp zh
    have ne : s≠z := fun e => disjoint_left.mp ds zr (e ▸ ss)
    have na : ¬G.Adj s z := fun e => no (mem_filter.mpr ⟨zr,e⟩)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc ne na sa az)
  have cGate := gates C cs u uc su
  have eGate := gates E es v ve sv
  have tGate := gates T ts w wt sw
  have cE : Disjoint (gate C u) (gate E v) :=
    disjoint_left.mpr (fun _ zu zv => disjoint_left.mp ce (gsub C u zu) (gsub E v zv))
  have cT : Disjoint (gate C u) (gate T w) :=
    disjoint_left.mpr (fun _ zu zw => disjoint_left.mp ct (gsub C u zu) (gsub T w zw))
  have eT : Disjoint (gate E v) (gate T w) :=
    disjoint_left.mpr (fun _ zv zw => disjoint_left.mp et (gsub E v zv) (gsub T w zw))
  have allGate := (card_le_card (union_subset (union_subset cGate eGate) tGate)).trans (cap s)
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨cT,eT⟩),card_union_of_disjoint cE] at allGate
  have sideBudget (R B₁ B₂ : Finset V) (cover : (univ:Finset V)=R∪B₁∪B₂∪S)
      (no₁ : ∀ a∈R,∀ b∈B₁,¬G.Adj a b) (no₂ : ∀ a∈R,∀ b∈B₂,¬G.Adj a b)
      (a : V) (ar : a∈R) (sa : G.Adj s a) (hi : d≤G.degree a) :
      d+1≤S.card+(N R).card+(gate R a).card := by
    have sub : G.neighborFinset a⊆S∪(N R).erase a∪gate R a := by
      intro z zn
      have az := (G.mem_neighborFinset _ _).mp zn
      have loc : z∈R∪B₁∪B₂∪S := cover ▸ mem_univ z
      rcases mem_union.mp loc with main|zs
      · rcases mem_union.mp main with sub|zB₂
        · rcases mem_union.mp sub with zr|zB₁
          · by_cases sZ : G.Adj s z
            · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr
                (mem_erase.mpr ⟨az.ne.symm,mem_filter.mpr ⟨zr,sZ⟩⟩))))
            · exact mem_union.mpr (Or.inr (mem_sdiff.mpr
                ⟨mem_filter.mpr ⟨zr,az⟩,fun e => sZ (mem_filter.mp e).2⟩))
          · exact (no₁ a ar z zB₁ az).elim
        · exact (no₂ a ar z zB₂ az).elim
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl zs)))
    have n := card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at n
    have o := card_union_le S ((N R).erase a)
    have p := card_union_le (S∪(N R).erase a) (gate R a)
    have e := card_erase_add_one (mem_filter.mpr ⟨ar,sa⟩ : a∈N R)
    change ((N R).erase a).card+1=(N R).card at e
    omega
  have cB := sideBudget C E T parts noCE noCT u uc su ud
  have eB := sideBudget E C T (parts.trans (by ac_rfl))
    (fun v ve u uc e => noCE u uc v ve e.symm) noET v ve sv vd
  have tB := sideBudget T C E (parts.trans (by ac_rfl))
    (fun w wt u uc e => noCT u uc w wt e.symm) (fun w wt v ve e => noET v ve w wt e.symm)
    w wt sw wd
  have spend (R R' : Finset V) (ds : Disjoint R R')
      (no : ∀ a∈R,∀ b∈R',¬G.Adj a b)
      (a : V) (ar : a∈R) (sa : G.Adj s a) : N R'⊆DistanceTwo G a := by
    intro z zn
    obtain ⟨zr,sz⟩ := mem_filter.mp zn
    have ne : a≠z := fun e => disjoint_left.mp ds ar (e.symm ▸ zr)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr (Graffiti189LongestPath.dist_two hc ne
      (no a ar z zr) sa.symm sz)
  have pn (R R' : Finset V) (ds : Disjoint R R') : Disjoint (N R) (N R') :=
    disjoint_left.mpr (fun _ z₁ z₂ => disjoint_left.mp ds (mem_filter.mp z₁).1 (mem_filter.mp z₂).1)
  have cu := (card_le_card (union_subset (spend C E ce noCE u uc su)
    (spend C T ct noCT u uc su))).trans (cap u)
  rw [card_union_of_disjoint (pn E T et)] at cu
  have ev := (card_le_card (union_subset (spend E C ce.symm (fun v ve u uc e => noCE u uc v ve e.symm) v ve sv)
    (spend E T et noET v ve sv))).trans (cap v)
  rw [card_union_of_disjoint (pn C T ct)] at ev
  have tw := (card_le_card (union_subset (spend T C ct.symm (fun w wt u uc e => noCT u uc w wt e.symm) w wt sw)
    (spend T E et.symm (fun w wt v ve e => noET v ve w wt e.symm) w wt sw))).trans (cap w)
  rw [card_union_of_disjoint (pn C E ce)] at tw
  omega

/-- In a minimum separator of size k≥2, every one of three nontrivial
disconnected sides has a high neighbor of one common cut vertex. -/
theorem degree_le_of_minimum_cut_with_three_nontrivial_shores
    (hc : G.Connected) (k d : Nat) (hk : 2≤k)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D:Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (cap : ∀ v,(DistanceTwo G v).card≤d) (S C E T : Finset V) (sCard : S.card=k)
    (parts : (univ:Finset V)=C∪E∪T∪S)
    (cs : Disjoint C S) (es : Disjoint E S) (ts : Disjoint T S)
    (ce : Disjoint C E) (ct : Disjoint C T) (et : Disjoint E T)
    (noCE : ∀ u∈C,∀ v∈E,¬G.Adj u v)
    (noCT : ∀ u∈C,∀ v∈T,¬G.Adj u v)
    (noET : ∀ u∈E,∀ v∈T,¬G.Adj u v)
    (cn : 1<C.card) (en : 1<E.card) (tn : 1<T.card) :
    d+6≤6*k := by
  classical
  have reach (R B₁ B₂ : Finset V) (prt : (univ:Finset V)=R∪B₁∪B₂∪S)
      (rs : Disjoint R S) (rb : Disjoint R B₁) (bs : Disjoint B₁ S)
      (rn : R.Nonempty) (bn : B₁.Nonempty)
      (no₁ : ∀ u∈R,∀ v∈B₁,¬G.Adj u v) (no₂ : ∀ u∈R,∀ v∈B₂,¬G.Adj u v)
      (s : V) (ss : s∈S) : ∃ u∈R,G.Adj s u := by
    apply Classical.byContradiction
    intro no
    obtain ⟨x,xr⟩ := rn
    obtain ⟨y,yb⟩ := bn
    have non : y∉R := fun e => disjoint_left.mp rb e yb
    have nos : y∉S.erase s := fun e => disjoint_left.mp bs yb (mem_erase.mp e).2
    have rS : Disjoint R (S.erase s) := disjoint_left.mpr (fun _ zr zs =>
      disjoint_left.mp rs zr (mem_erase.mp zs).2)
    have cl (u : V) (ur : u∈R) (v : V) (vr : v∉R) (e : G.Adj u v) : v∈S.erase s := by
      have loc : v∈R∪B₁∪B₂∪S := prt ▸ mem_univ v
      rcases mem_union.mp loc with z|vs
      · rcases mem_union.mp z with r|b
        · exact ((mem_union.mp r).elim vr (fun z => no₁ u ur v z e)).elim
        · exact (no₂ u ur v b e).elim
      exact mem_erase.mpr ⟨fun h => no ⟨u,ur,h ▸ e.symm⟩,vs⟩
    have contradiction := Graffiti189LongestPath.boundary_card_of_connectivity k conn xr non nos rS cl
    have h := card_erase_add_one ss
    omega
  have highReach (R B₁ B₂ : Finset V) (prt : (univ:Finset V)=R∪B₁∪B₂∪S)
      (rb : Disjoint R B₁) (rn : 1<R.card) (bn : B₁.Nonempty)
      (no₁ : ∀ u∈R,∀ v∈B₁,¬G.Adj u v) (no₂ : ∀ u∈R,∀ v∈B₂,¬G.Adj u v)
      (x : V) (xr : x∈R) (xl : G.degree x<d) : ∃ s∈S,∃ u∈R,G.Adj s u ∧ d≤G.degree u := by
    apply Classical.byContradiction
    intro none
    have e := card_erase_add_one xr
    obtain ⟨u,ur⟩ := card_pos.mp (show 0<(R.erase x).card from by omega)
    obtain ⟨v,vb⟩ := bn
    have vr : v∉R := fun e => disjoint_left.mp rb e vb
    have vn : v∉({x}:Finset V) := fun h => vr ((mem_singleton.mp h).symm ▸ xr)
    have rdis : Disjoint (R.erase x) ({x}:Finset V) := disjoint_left.mpr (fun _ zr zx =>
      (mem_erase.mp zr).1 (mem_singleton.mp zx))
    have cl (a : V) (ar : a∈R.erase x) (b : V) (br : b∉R.erase x) (e : G.Adj a b) :
        b∈({x}:Finset V) := by
      obtain ⟨ax,aR⟩ := mem_erase.mp ar
      have high := (deg a x ax).resolve_right (Nat.not_le_of_lt xl)
      have loc : b∈R∪B₁∪B₂∪S := prt ▸ mem_univ b
      rcases mem_union.mp loc with zu|bs
      · rcases mem_union.mp zu with z|b₂
        · rcases mem_union.mp z with bR|b₁
          · exact mem_singleton.mpr (Classical.byContradiction
              (fun he => br (mem_erase.mpr ⟨he,bR⟩)))
          · exact (no₁ a aR b b₁ e).elim
        · exact (no₂ a aR b b₂ e).elim
      exact (none ⟨b,bs,a,aR,e.symm,high⟩).elim
    have lf := Graffiti189LongestPath.boundary_card_of_connectivity k conn ur
      (fun h => vr (mem_erase.mp h).2) vn rdis cl
    simp at lf
    omega
  have cNon : C.Nonempty := card_pos.mp (by omega)
  have eNon : E.Nonempty := card_pos.mp (by omega)
  have tNon : T.Nonempty := card_pos.mp (by omega)
  have pE : (univ:Finset V)=E∪C∪T∪S := parts.trans (by ac_rfl)
  have pT : (univ:Finset V)=T∪C∪E∪S := parts.trans (by ac_rfl)
  have nEC (u : V) (ue : u∈E) (v : V) (vc : v∈C) : ¬G.Adj u v :=
    fun h => noCE v vc u ue h.symm
  have nTC (u : V) (ut : u∈T) (v : V) (vc : v∈C) : ¬G.Adj u v :=
    fun h => noCT v vc u ut h.symm
  have nTE (u : V) (ut : u∈T) (v : V) (ve : v∈E) : ¬G.Adj u v :=
    fun h => noET v ve u ut h.symm
  have Cto (s : V) (ss : s∈S) := reach C E T parts cs ce es cNon eNon noCE noCT s ss
  have Eto (s : V) (ss : s∈S) := reach E C T pE es ce.symm cs eNon cNon nEC noET s ss
  have Tto (s : V) (ss : s∈S) := reach T C E pT ts ct.symm cs tNon cNon nTC nTE s ss
  have finish (s : V) (ss : s∈S)
      (c : ∃ u∈C,G.Adj s u ∧ d≤G.degree u) (e : ∃ v∈E,G.Adj s v ∧ d≤G.degree v)
      (t : ∃ w∈T,G.Adj s w ∧ d≤G.degree w) : d+6≤6*k := by
    obtain ⟨u,uc,su,uh⟩ := c
    obtain ⟨v,ve,sv,vh⟩ := e
    obtain ⟨w,wt,sw,wh⟩ := t
    have out := degree_le_six_cut_minus_six hc d cap S C E T parts s ss cs es ts ce ct et
      noCE noCT noET u uc su uh v ve sv vh w wt sw wh
    omega
  by_cases there : ∃ x∈C∪E∪T,G.degree x<d
  · obtain ⟨x,xo,xl⟩ := there
    have other (v : V) (ne : x≠v) : d≤G.degree v :=
      (deg x v ne).resolve_left (Nat.not_le_of_lt xl)
    rcases mem_union.mp xo with z|xt
    · rcases mem_union.mp z with xc|xe
      · obtain ⟨s,ss,c⟩ := highReach C E T parts ce cn eNon noCE noCT x xc xl
        obtain ⟨v,ve,sv⟩ := Eto s ss
        obtain ⟨w,wt,sw⟩ := Tto s ss
        exact finish s ss c ⟨v,ve,sv,other v (fun e => disjoint_left.mp ce xc (e.symm ▸ ve))⟩
          ⟨w,wt,sw,other w (fun e => disjoint_left.mp ct xc (e.symm ▸ wt))⟩
      · obtain ⟨s,ss,e⟩ := highReach E C T pE ce.symm en cNon nEC noET x xe xl
        obtain ⟨u,uc,su⟩ := Cto s ss
        obtain ⟨w,wt,sw⟩ := Tto s ss
        exact finish s ss ⟨u,uc,su,other u (fun h => disjoint_left.mp ce (h.symm ▸ uc) xe)⟩ e
          ⟨w,wt,sw,other w (fun h => disjoint_left.mp et xe (h.symm ▸ wt))⟩
    · obtain ⟨s,ss,t⟩ := highReach T C E pT ct.symm tn cNon nTC nTE x xt xl
      obtain ⟨u,uc,su⟩ := Cto s ss
      obtain ⟨v,ve,sv⟩ := Eto s ss
      exact finish s ss ⟨u,uc,su,other u (fun h => disjoint_left.mp ct (h.symm ▸ uc) xt)⟩
        ⟨v,ve,sv,other v (fun h => disjoint_left.mp et (h.symm ▸ ve) xt)⟩ t
  · obtain ⟨s,ss⟩ := card_pos.mp (show 0<S.card from by omega)
    obtain ⟨u,uc,su⟩ := Cto s ss
    obtain ⟨v,ve,sv⟩ := Eto s ss
    obtain ⟨w,wt,sw⟩ := Tto s ss
    have allHigh (v : V) (vv : v∈C∪E∪T) : d≤G.degree v :=
      Nat.le_of_not_gt (fun h => there ⟨v,vv,h⟩)
    exact finish s ss ⟨u,uc,su,allHigh u (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl uc))))⟩
      ⟨v,ve,sv,allHigh v (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr ve))))⟩
      ⟨w,wt,sw,allHigh w (mem_union.mpr (Or.inr wt))⟩

#print axioms degree_le_six_cut_minus_six
#print axioms degree_le_of_minimum_cut_with_three_nontrivial_shores
end Graffiti189LongestPath.ThreeShoreCutBound
