import P5CliqueOnePortAmbientBudget133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem mixed_high_has_joint_pure_foreign_representatives
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (q : V) (qo : q∉D) (high : 3<localIndependence G q) :
      ∃ S : Finset V, (∀ x∈S,G.Adj q x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) ∧
        ∀ i, ¬G.Adj q (p i) → ∃ x∈S, x∉D ∧ ∀ w∈D,G.Adj x w↔w=p i := by
  classical
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  choose lab hlab using attach
  let tag (q : V) := if h : q∉D then p (lab q h) else q
  have pick (q : V) (qo : q∉D) : tag q∈D ∧ tag q∈P ∧ G.Adj q (tag q) := by
    have e : tag q=p (lab q qo) := dif_pos qo
    rw [e]
    exact ⟨pm _,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,hlab q qo⟩
  have ne : (localIndependentSets G q).Nonempty := by
    refine ⟨∅,?_⟩
    simp [localIndependentSets]
  obtain ⟨S,hS,sval⟩ := Finset.exists_mem_eq_sup _ ne Finset.card
  have sc : S.card≥4 := by
    change localIndependence G q=S.card at sval
    omega
  have info : (∀ x∈S,G.Adj q x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,
      Finset.subset_iff,Finset.mem_univ,true_and] using hS
  let g (x : V) := if x∈D then x else tag x
  have hit (x : V) (xm : x∈S) : g x∈P := by
    by_cases xd : x∈D
    · obtain ⟨i,ix⟩ := palette q qo x xd (info.1 _ xm)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simpa only [g,if_pos xd] using ix.symm⟩
    · simpa only [g,if_neg xd] using (pick x xd).2.1
  have inj : Set.InjOn g (S : Set V) := by
    intro v vm w wm e
    by_cases vd : v∈D
    · by_cases wd : w∈D
      · simpa only [g,if_pos vd,if_pos wd] using e
      simp only [g,if_pos vd,if_neg wd] at e
      exact ((info.2 w wm v vm) (e.symm ▸ (pick w wd).2.2)).elim
    by_cases wd : w∈D
    · simp only [g,if_neg vd,if_pos wd] at e
      exact ((info.2 v vm w wm) (e ▸ (pick v vd).2.2)).elim
    simp only [g,if_neg vd,if_neg wd] at e
    have qn : q≠tag v := fun eq=>qo (eq.symm ▸ (pick v vd).1)
    exact h4 q (tag v) v w qn (info.1 _ vm) (pick v vd).2.2.symm
      (info.1 _ wm) (e.symm ▸ (pick w wd).2.2).symm
  have sub : S.image g⊆P := by
    intro v vm
    obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp vm
    exact hit w wm
  have im := Finset.card_image_of_injOn inj
  have eq : S.image g=P := Finset.eq_of_subset_of_card_le sub (by omega)
  have repr (i : Fin 4) (i0 : ¬G.Adj q (p i)) : ∃ x∈S,x∉D ∧ ∀ w∈D,G.Adj x w↔w=p i := by
    have M : p i∈S.image g := eq.symm ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨x,xS,xg⟩ := Finset.mem_image.mp M
    have xo : x∉D := by
      intro xm
      simp only [g,if_pos xm] at xg
      exact i0 (xg ▸ info.1 _ xS)
    simp only [g,if_neg xo] at xg
    have xi : G.Adj x (p i) := xg ▸ (pick x xo).2.2
    refine ⟨x,xS,xo,?_⟩
    intro y yd
    constructor
    · intro xy
      obtain ⟨j,jy⟩ := palette x xo y yd xy
      by_cases ji : j=i
      · exact jy.trans (congrArg p ji)
      have pj : p j∈S.image g := eq.symm ▸ Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
      obtain ⟨z,zS,zg⟩ := Finset.mem_image.mp pj
      by_cases zd : z∈D
      · have zp : z=p j := by simpa only [g,if_pos zd] using zg
        have xz : G.Adj x z := (jy.trans zp.symm) ▸ xy
        exact ((info.2 x xS z zS) xz).elim
      · simp only [g,if_neg zd] at zg
        have zx : G.Adj z (p j) := zg ▸ (pick z zd).2.2
        have xx : G.Adj x (p j) := jy ▸ xy
        have id := h4 q (p j) x z (fun e=>qo (e.symm ▸ pm j))
          (info.1 _ xS) xx.symm (info.1 _ zS) zx.symm
        have pEq : p i=p j := xg.symm.trans ((congrArg tag id).trans zg)
        exact (ji (pi pEq).symm).elim
    · rintro rfl
      exact xi
  exact ⟨S,info.1,info.2,repr⟩

#print axioms mixed_high_has_joint_pure_foreign_representatives

theorem mixed_high_has_pure_foreign_representatives
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (q : V) (qo : q∉D) (high : 3<localIndependence G q) :
      ∀ i, ¬G.Adj q (p i) → ∃ x, x∉D ∧ G.Adj q x ∧
        ∀ w∈D,G.Adj x w↔w=p i := by
  obtain ⟨S,sa,_,R⟩ := mixed_high_has_joint_pure_foreign_representatives h4 D p pm pi attach palette q qo high
  intro i ni
  obtain ⟨v,vm,vo,vp⟩ := R i ni
  exact ⟨v,vo,sa v vm,vp⟩

#print axioms mixed_high_has_pure_foreign_representatives

theorem unique_mixed_center_at_pure_foreign_leaf
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (x y v : V) (vo : v∉D)
    (xv : G.Adj x v) (yv : G.Adj y v) (i : Fin 4)
    (xi : ¬G.Adj x (p i)) (yi : ¬G.Adj y (p i))
    (xc : 2≤((Finset.univ : Finset (Fin 4)).filter (fun j=>G.Adj x (p j))).card)
    (yc : 2≤((Finset.univ : Finset (Fin 4)).filter (fun j=>G.Adj y (p j))).card) :
    x=y := by
  classical
  let A := (Finset.univ : Finset (Fin 4)).filter (fun j=>G.Adj x (p j))
  let B := (Finset.univ : Finset (Fin 4)).filter (fun j=>G.Adj y (p j))
  have ub : (A∪B).card≤3 := by
    have e : A∪B ⊆ (Finset.univ : Finset (Fin 4)).erase i := by
      intro j jm
      simp only [A,B,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] at jm
      refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
      rintro rfl
      exact jm.elim xi yi
    have c : ((Finset.univ : Finset (Fin 4)).erase i).card=3 := by simp
    exact (Finset.card_le_card e).trans c.le
  have ce := Finset.card_union_add_card_inter A B
  change 2≤A.card at xc
  change 2≤B.card at yc
  have non : (A∩B).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j,jm⟩ := non
  simp only [A,B,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] at jm
  exact h4 v (p j) x y (fun e=>vo (e.symm ▸ pm j)) xv.symm jm.1.symm yv.symm jm.2.symm

#print axioms unique_mixed_center_at_pure_foreign_leaf
theorem pure_foreign_neighbor_signed_cap
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (v q : V) (vo : v∉D) (qout : q∉D) (vq : G.Adj v q)
    (i : Fin 4) (vi : ∀ w∈D,G.Adj v w↔w=p i)
    (qi : ¬G.Adj q (p i)) :
    localIndependence G v+(D.filter (G.Adj q)).card≤5 := by
  classical
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  choose lab hlab using attach
  let tag (v : V) := if h : v∉D then p (lab v h) else v
  have pick (v : V) (vo : v∉D) : tag v∈D ∧ tag v∈P ∧ G.Adj v (tag v) := by
    have e : tag v=p (lab v vo) := dif_pos vo
    rw [e]
    exact ⟨pm _,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,hlab v vo⟩
  have ne : (localIndependentSets G v).Nonempty := by
    refine ⟨∅,?_⟩
    simp [localIndependentSets]
  obtain ⟨S,hS,sval⟩ := Finset.exists_mem_eq_sup _ ne Finset.card
  have info : (∀ x∈S,G.Adj v x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,
      Finset.subset_iff,Finset.mem_univ,true_and] using hS
  let g (x : V) := if x∈D then x else tag x
  have hit (x : V) (xm : x∈S) : g x∈P := by
    by_cases xd : x∈D
    · obtain ⟨i,ix⟩ := palette v vo x xd (info.1 _ xm)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simpa only [g,if_pos xd] using ix.symm⟩
    · simpa only [g,if_neg xd] using (pick x xd).2.1
  have inj : Set.InjOn g (S : Set V) := by
    intro x vm w wm e
    by_cases vd : x∈D
    · by_cases wd : w∈D
      · simpa only [g,if_pos vd,if_pos wd] using e
      simp only [g,if_pos vd,if_neg wd] at e
      exact ((info.2 w wm x vm) (e.symm ▸ (pick w wd).2.2)).elim
    by_cases wd : w∈D
    · simp only [g,if_neg vd,if_pos wd] at e
      exact ((info.2 x vm w wm) (e ▸ (pick x vd).2.2)).elim
    simp only [g,if_neg vd,if_neg wd] at e
    have qn : v≠tag x := fun eq=>vo (eq.symm ▸ (pick x vd).1)
    exact h4 v (tag x) x w qn (info.1 _ vm) (pick x vd).2.2.symm
      (info.1 _ wm) (e.symm ▸ (pick w wd).2.2).symm
  have sub : S.image g⊆P := by
    intro v vm
    obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp vm
    exact hit w wm
  have im := Finset.card_image_of_injOn inj
  let T := D.filter (G.Adj q)
  have tp : T⊆P := by
    intro x xm
    obtain ⟨xd,qx⟩ := Finset.mem_filter.mp xm
    obtain ⟨j,e⟩ := palette q qout x xd qx
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e.symm⟩
  have imageSub : S.image g⊆insert (g q) (P\T) := by
    intro y ym
    obtain ⟨x,xm,rfl⟩ := Finset.mem_image.mp ym
    by_cases xq : x=q
    · subst x
      exact Finset.mem_insert_self _ _
    apply Finset.mem_insert_of_mem
    refine Finset.mem_sdiff.mpr ⟨hit x xm,?_⟩
    intro gxT
    have qg := (Finset.mem_filter.mp gxT).2
    by_cases xd : x∈D
    · have e : x=p i := (vi x xd).mp (info.1 _ xm)
      simp only [g,e,if_pos (pm i)] at qg
      exact qi qg
    simp only [g,if_neg xd] at qg
    exact xq (h4 v (tag x) x q (fun a=>vo (a.symm ▸ (pick x xd).1))
      (info.1 _ xm) (pick x xd).2.2.symm vq qg.symm)
  have c := Finset.card_le_card imageSub
  have d := Finset.card_insert_le (s:=P\T) (g q)
  have f := Finset.card_sdiff_add_card_eq_card tp
  change localIndependence G v=S.card at sval
  change _+T.card≤5
  omega

#print axioms pure_foreign_neighbor_signed_cap

end Graffiti133P5CliqueArms
